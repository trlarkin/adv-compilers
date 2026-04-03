module Main where

import           AbstractSyntax     as S
import           CCMachine          as CC
import           Control.Monad
import           Parser
import           Public
import           System.Environment

main :: IO ()
main = do
    [args] <- getArgs
    mainCompiler args

compileWithCC :: FilePath -> IO ()
compileWithCC fp = do
    program <- parseProgram fp
    print program
    print $ typeCheckTerm program
    let evalResult = CC.ccMachineEval program
    print evalResult
