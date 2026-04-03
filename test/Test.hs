module Main where

import           Control.Exception (SomeException, catch)
import           Control.Monad
import           Data.List
import           MyErrorType
import           Parser
import           Public
import           Test.HUnit


data TestType = NoParseError
              | NoTypeError
              | SolutionIs String
              | FreeVars [String]
              | EvalsToSomething

testAnswers :: [(FilePath, TestType)]
testAnswers = [
    -- ("filename", "expected")
    ("corelambda_files/cbntest1.corelambda", NoTypeError), -- diverges
    ("corelambda_files/intFact.corelambda", SolutionIs "120"),
    ("corelambda_files/sumn100.corelambda", SolutionIs "5050"),
    ("corelambda_files/takFastOpts.corelambda", NoTypeError), -- did not evaluate
    ("corelambda_files/takTest1Opts.corelambda", NoTypeError), -- did not evaluate
    ("corelambda_files/takTestOpts.corelambda", SolutionIs "6"),
    ("corelambda_files/test11.corelambda", SolutionIs "false"),
    ("corelambda_files/test12.corelambda", SolutionIs "8"),
    ("corelambda_files/test13.corelambda", SolutionIs "720"),
    ("corelambda_files/test14.corelambda", SolutionIs "false"),
    ("corelambda_files/test15.corelambda", SolutionIs "'b'"),
    ("corelambda_files/test16.corelambda", EvalsToSomething),
    ("corelambda_files/test17.corelambda", EvalsToSomething),
    ("corelambda_files/test18.corelambda", EvalsToSomething),
    ("corelambda_files/test21.corelambda", EvalsToSomething),
    ("corelambda_files/test23.corelambda", EvalsToSomething),
    ("corelambda_files/test24.corelambda", EvalsToSomething),
    ("corelambda_files/test25.corelambda", EvalsToSomething),
    ("corelambda_files/test26.corelambda", EvalsToSomething),
    ("corelambda_files/test27.corelambda", EvalsToSomething),
    ("corelambda_files/test28.corelambda", EvalsToSomething),
    ("corelambda_files/test28prime.corelambda", EvalsToSomething),
    ("corelambda_files/test39.corelambda", EvalsToSomething),
    ("corelambda_files/test40.corelambda", EvalsToSomething),
    ("corelambda_files/test74.corelambda", EvalsToSomething),
    ("corelambda_files/test96.corelambda", EvalsToSomething),
    ("corelambda_files/test105.corelambda", EvalsToSomething),
    ("corelambda_files/test115.corelambda", EvalsToSomething),
    ("corelambda_files/test141.corelambda", SolutionIs "27"),
    ("corelambda_files/test_fix", EvalsToSomething),
    ("corelambda_files/test_freevar", FreeVars ["z"]),
    ("corelambda_files/test_if", SolutionIs "true"),
    ("corelambda_files/test_primop", NoTypeError), -- diverges
    ("corelambda_files/test_types", EvalsToSomething)
    ]

testSingle :: (FilePath, TestType) -> IO Test
testSingle (file, NoParseError) = do
    parsedFile <- parseOnly file
    return $ TestCase $ assertBool ("ParseError in " ++ file) (parsedFile /= Nothing)
testSingle (file, FreeVars varsExpected) = do
    maybeVarsActual <- parseFVar file
    case maybeVarsActual of
        Just varsActual -> return $ TestCase $ assertBool ("Incorrect FreeVars in " ++ file) (varsExpected == varsActual)
        Nothing -> assertFailure ("ParseError in " ++ file)
testSingle (file, NoTypeError) = do
    typeOfFile <- parseFVarTypeCheck file
    return $ TestCase $ assertBool ("TypeError in " ++ file) (typeOfFile /= Nothing)
testSingle (file, EvalsToSomething) = do
    res <- testEval file
    return $ TestCase $ assertBool ("Something went wrong in " ++ file) (res /= Nothing)
testSingle (file, SolutionIs expected) = do
    Just actual <- testEval file
    return $ TestCase $ assertBool ("Actual ["++show actual++"] /= Expected ["++show expected++"] in " ++ file) (expected == actual)



tests :: IO Test
tests = do
    TestList <$> mapM testSingle testAnswers

evaluators :: [(String, TermEvaluator)]
evaluators = [("SOS CBV", evalWithCBV)
            --  , ("DB CBV", evalWithDeBruijn)
             --, ("NatSem", evalWithNatSemantics)
             , ("STD Red.", evalWithReductionSemantics)
             , ("CC Machine", evalWithCCMachine)
             ]

evaluatorNames :: [String]
evaluatorNames = map fst evaluators


testEvaluatorSingle :: (String, TermEvaluator) -> FilePath -> Result Term
testEvaluatorSingle e@(evalName, evaluator) file = do
    parsed <- parser file
    typeChecked <- typeChecker parsed
    evaluateWith e typeChecked

passOrFail :: Bool -> String
passOrFail True  = "passing"
passOrFail False = "FAILING"

-- | assumes the header is the longest string in a column
printMatrix :: Show a => [[a]] -> IO ()
printMatrix matrix = putStrLn $ unlines $ map (intercalate "\t" . map show) matrix
    where
        headers = head matrix
        tabs = map ((+1) . (`div` 8) . length . show) headers



testMatrix :: [[String]]
testMatrix = [zipWith sameValid [testEvaluatorSingle e fp | fp <- filenames] answers | e@(evalName, evaluator) <- evaluators]
    where
        filenames = map (\s -> "corelambda_files/" ++ s ++ ".corelambda") matrixTests
        answers = testEvaluatorSingle (head evaluators) <$> filenames


main :: IO Counts
main = do
    printMatrix $ ("Test #" : evaluatorNames) : [] : transpose (matrixTests : testMatrix)
    runTestTT =<< tests

matrixTests :: [String]
matrixTests = ["test11","test12","test13","test14","test15","test16","test17","test18","test21",
               "test23","test24","test25","test26","test27","test28","test39","test40","test41",
               "test43",
               "test55",
               "test77","test78","test79","test82",
               "test99",
               "test100","test101",
               "test110","test114",
               "test133","test134"
            --    ,"test74", "test96", "test105", "test115"
            --    ,"test141","test142","test143","test145"
               ]
