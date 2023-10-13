{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Data.Aeson
import qualified Data.ByteString.Lazy as B
import qualified Data.ByteString.Lazy.Char8 as Char8
import qualified Data.Aeson.KeyMap as Map
import Data.Text
import Data.Maybe (catMaybes)
import qualified Debug.Trace as Debug

data Tree = Tree {
    text_ :: Text,
    start_time_ :: Integer,
    end_time_ :: Integer,
    children_ :: [Tree]
} deriving (Show)

isNvtxEvent :: Object -> Bool
isNvtxEvent obj = case Map.lookup "NvtxEvent" obj of
    Just _ -> True
    _ -> False

-- bugs! only a layer will be appended.
buildTree :: Object -> [Tree] -> [Tree]
buildTree obj trees = case getInfo obj of 
        Just (start_time, end_time, text) -> Tree text start_time end_time [] : trees
        _ -> trees
    where 
        getInfo :: Object -> Maybe (Integer, Integer, Text)
        getInfo o = do
            (Object nvtx_event) <- Map.lookup "NvtxEvent" o 
            (String start_time) <- Map.lookup "Timestamp" nvtx_event
            (String end_time) <-  Map.lookup "EndTimestamp" nvtx_event
            (String text) <- Map.lookup "Text" nvtx_event
            return (text2int start_time, text2int end_time, text)
        text2int :: Text -> Integer
        text2int = read . Data.Text.unpack

appendChildEach :: [Tree] -> Tree -> Tree
appendChildEach trees current = Tree (text_ current) (start_time_ current) (end_time_ current) (findChildren trees current)

findChildren :: [Tree] -> Tree -> [Tree]
findChildren trees current = childrens
    where isChild :: Tree -> Tree -> Bool
          isChild current tree = segmentContains current tree
          subgraph = Prelude.filter (isChild current) trees
          childrens = Prelude.filter (not . (existLonger subgraph)) subgraph

segmentContains :: Tree -> Tree -> Bool
segmentContains a b = (start_time_ a) < (start_time_ b) && (end_time_ a) > (end_time_ b)

-- 是否存在比当前节点小的节点
existLonger :: [Tree] -> Tree -> Bool
existLonger trees current = Prelude.any ((flip segmentContains) current) trees

main :: IO ()
main = do
    -- 从文件中读取 JSON 数据
    jsonBytes <- B.readFile "my_report.json"
    let jsons = Prelude.map decode (Char8.lines jsonBytes)
    let just_json = catMaybes jsons
    let objects = Prelude.filter isNvtxEvent just_json
    let nodes = Prelude.foldr buildTree [] objects
    let batch_nodes = batch_root:Prelude.filter (segmentContains batch_root) nodes
                    where batch_root = (Prelude.head $ filterNameExactly batch_string nodes)
    let trees = (appendchild . appendchild . appendchild . appendchild) batch_nodes -- add 3 layer childrens, not a good idea, but easy.
                    where appendchild current_trees = Prelude.map (appendChildEach current_trees) current_trees
    -- 构建一个树形结构
    print ("Total nvtxEvent length is : " ++ (show . Prelude.length) trees)
    {-putStrLn (getChildNames $ Prelude.head trees) -} -- the order is the same with nsight.
    analysis_evalframe trees
    analysis_fallback_wrapper trees
    analysis_interpreter_core trees

-- filter helper function
filterNameIn :: Text -> [Tree] -> [Tree]
filterNameIn name trees = Prelude.filter (\x -> (Data.Text.isInfixOf name (text_ x))) trees

filterNameExactly :: Text -> [Tree] -> [Tree]
filterNameExactly name trees = Prelude.filter (\x -> (name == (text_ x))) trees

-- start ms - end ms
filterByRange :: Integer -> Integer -> [Tree] -> [Tree]
filterByRange start end trees = Prelude.filter (\x -> (start_time_ x) * 1000000 > start && (end_time_ x) * 100000 < end) trees

filterLeafNode :: [Tree] -> [Tree]
filterLeafNode trees = Prelude.filter (\x -> (Prelude.length (children_ x)) == 0) trees

flattenChildren :: Tree -> [Tree]
flattenChildren tree = Prelude.concat $ [[tree]] ++ (Prelude.map flattenChildren (children_ tree))

-- x ms
getTime :: Tree -> Double
getTime tree = fromIntegral ((end_time_ tree) - (start_time_ tree)) * 1.0 / 1000000.0

summaryTime :: [Tree] -> Double
summaryTime trees = Prelude.foldr (\x r -> getTime x + r) 0.0 trees

getChildNames :: Tree -> String
getChildNames trees = string
    where texts = Prelude.map (\x->Data.Text.unpack (text_ x) ++ Data.Text.unpack "\n") $ children_ trees
          string = Prelude.foldr (++) "" texts

batch_string = "26"

analysis_evalframe :: [Tree] -> IO ()
analysis_evalframe trees = do 
    print "Start analysis Eval Frame Cost..."
    let root = filterNameExactly batch_string trees
    print $ "filtered nodes : " ++ (show . Prelude.length) root
    let children = flattenChildren (Prelude.head root)
    {-print root-}
    let callbacks = filterNameIn "eval_frame_callback" children
    {-let callbacks = filterNameIn "eval_frame_callback" children-}
    {-print $ Prelude.map (\x->text_ x) callbacks-}
    let totals_evalframes = summaryTime callbacks
    let leaf_evalframes = summaryTime $ filterLeafNode callbacks
    let totals_lookup = summaryTime $ (filterNameExactly "lookup") children
    let totals_tryguard = summaryTime $ (filterNameExactly "try guard") children
    print ("Total Evalframe is (totals    )" ++ show totals_evalframes ++ " ms")
    print ("    Lookup Time     is (guard time)" ++ show totals_lookup ++ " ms")
    print ("        try guard Time     is " ++ show totals_tryguard ++ " ms")
    print ("    Leaf  Evalframe is (skip files)" ++ show leaf_evalframes ++ " ms")

analysis_fallback_wrapper :: [Tree] -> IO ()
analysis_fallback_wrapper trees = do 
    print "Start analysis fallback wrapper cost..."
    let root = filterNameExactly batch_string trees
    let children = flattenChildren (Prelude.head root)
    let fbwrappers = filterNameIn "FallbackWrapper: SIR_" children
    let totals = summaryTime fbwrappers
    print ("TotalTime is " ++ show totals ++ " ms")

analysis_interpreter_core :: [Tree] -> IO ()
analysis_interpreter_core trees = do 
    print "Start analysis interpreter_core info..."
    -- remove backward run interpreter core
    let root = filterNameExactly batch_string trees
    let backward_event = Prelude.head $ filterNameExactly "backward" trees
    let children = Prelude.filter (not . (segmentContains backward_event)) $ flattenChildren (Prelude.head root)
    let interpreter = filterNameExactly "interpreter_core_run" children
    let min_cost = 1.0 --  0.2 ms is the min cost of run program op.
    let valid_interpreter = Prelude.filter (\x -> getTime x > min_cost) interpreter
    print ("Valid vs NoValid: " ++ show (Prelude.length valid_interpreter) ++ " / " ++ show (Prelude.length interpreter))
