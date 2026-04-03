{-# LANGUAGE FlexibleContexts #-}
module Public where

import qualified AbstractSyntax                                                 as S
import qualified CCMachine                                                      as CC
-- import           Control.Monad
-- import           CEKMachine                                                     as CEK
import           CKMachine                                                      as CK
import           Control.Monad
import           DeBruijnWithIntegerLabelsAndTags                               as DBS
import           MyErrorType
import qualified NaturalSemantics_CBV                                           as NS
import qualified NaturalSemanticsWithEnvironmentsAndClosures_CBV                as NSEC
import qualified NaturalSemanticsWithEnvironmentsClosuresAndDeBruijnIndices_CBV as NSECDB
import qualified Parser                                                         as P
import qualified ReductionSemantics                                             as RS
import qualified StructuralOperationalSemantics_CBV                             as CBV
import           StructuralOperationalSemantics_CBV_forDeBruijn                 as DB
import           System.Environment
import           System.IO
import           System.IO.Unsafe
import           Text.Parsec
import qualified Typing                                                         as T
import qualified CPS

-- import qualified

type TermEvaluator = S.Term -> S.Term
type Term = S.Term

toDB :: S.Term -> DBS.Term
toDB = DBS.toDeBruijn

parser :: FilePath -> Result S.Term
parser fname = do
    case parse P.programParser "" fileData of
        Right success -> Valid success
        Left err      -> ParseError $ show err
    where
        fileData = unsafePerformIO $ hGetContents =<< openFile fname ReadMode

typeChecker :: S.Term -> Result S.Term
typeChecker t = case T.typeCheck t of
    S.TypeError err -> TypeError err
    _               -> Valid t

evaluateWith :: (String, TermEvaluator) -> S.Term -> Result S.Term
evaluateWith (evalName, evaluator) t = case evaluator t of
    S.ErrorTerm err -> EvaluationError evalName err
    t'              -> Valid t'

evalWithReductionSemantics :: TermEvaluator
evalWithReductionSemantics = RS.textualMachineEval

evalWithCCMachine :: TermEvaluator
evalWithCCMachine = CC.ccMachineEval

evalWithCKMachine :: S.Term -> S.Term
evalWithCKMachine = CK.ckMachineEval

-- evalWithCEKMachine :: S.Term -> S.Term
-- evalWithCEKMachine = CEK.cekMachineEval

evalWithCBV :: TermEvaluator
evalWithCBV = CBV.eval

evalWithDeBruijn :: S.Term -> DBS.Term
evalWithDeBruijn = DB.eval . DBS.toDeBruijn

evalWithNSwEnvClo :: S.Term -> S.Term
evalWithNSwEnvClo = NSEC.evalToTerm

evalWithNSwDB :: S.Term -> DBS.Term
evalWithNSwDB = NSECDB.evalToTerm . DBS.toDeBruijn

evalWithNatSemantics :: S.Term -> S.Term
evalWithNatSemantics t = case NS.eval t of
    Just t' -> t'
    Nothing -> S.ErrorTerm "failed"

cpsFischerPlotkin :: S.Term -> S.Term
cpsFischerPlotkin t = CPS.toCPS_FischerPlotkin (T.typeCheck t) t

idTerm :: S.Term
idTerm = S.Abs "x" S.TypeUnit (S.Var "x")

evalWithFischerPlotkinCPS :: S.Term -> S.Term
evalWithFischerPlotkinCPS t = evalWithCBV $ S.App (CPS.toCPS_FischerPlotkin (T.typeCheck t) t) idTerm

undefinedEvaluator :: String -> TermEvaluator
undefinedEvaluator name t = S.ErrorTerm $ name ++ " is undefined"

{-
Good Tests for this:

test_if
sumn100.corelambda
test41.corelambda

-}
mainCompiler :: String -> IO ()
mainCompiler args = do
    -- 1. read the program text from a file into a string,
    --args
    -- 2. invoke the parser to produce an abstract syntax tree for the program,
    program <- P.parseProgram args
    print program
    -- 3. print the free variables of the program,
    let freevars = S.fv program
    putStrLn $ "Free Variables:" ++ show freevars
    unless (null freevars) (error $ "unbound variables")
    -- 4. in case the program is closed (has no free variables), type-check the program,
    putStrLn $ "Type:" ++ show (P.typeCheckTerm program)
    -- 5. in case the program has a type, evaluate it with respect to call-by-value structural
    -- operational semantics (yielding a term),
    putStrLn $ "Call-by-value evaluation: \n\t" ++ show (evalWithCBV program)
    -- 6. evaluate it according to big-step operational semantics (yielding a value), in sev-
    -- eral flavors (vanilla cbv, with environments and closures, and with DeBruijn in-
    -- dices),
    putStrLn $ "Natural CBV: \n\t" ++ show (evalWithNatSemantics program)
    putStrLn $ "Natural CBV Closures: \n\t" ++ show (evalWithNSwEnvClo program)
    putStrLn $ "Natural CBV Closures & DB: \n\t" ++ show (evalWithNSwDB program)

    putStrLn $ "BeBruijn evaluation: \n\t" ++ show (evalWithDeBruijn program)
    -- 7. evaluate the program using standard reduction,
    putStrLn $ "Standard Reduction evaluation: \n\t" ++ show (evalWithReductionSemantics program)
    -- 8. evaluate the program using the CC machine,
    putStrLn $ "CC Machine evaluation: \n\t" ++ show (evalWithCCMachine program)
    -- 9. evaluate the program using the CK machine,
    putStrLn $ "CK Machine evaluation: \n\t" ++ show (evalWithCKMachine program)
    -- 10. evaluate the program using the CEK machine.
    putStrLn $ "CEK Machine evaluation: \n\t" ++ show "not working :(" -- (evalWithCEKMachine program)


q = (\p -> evalWithCBV  $ S.App p (S.Abs "x" S.TypeUnit (S.Var "x"))) <$> cpsFischerPlotkin <$> parser "corelambda_files/cps_test" 