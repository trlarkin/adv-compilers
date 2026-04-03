{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module Parser where

import qualified AbstractSyntax                     as S
import           Control.Monad
import           ParserUtils
import           Prelude                            hiding (div)
import qualified ReductionSemantics                 as RS
import           StructuralOperationalSemantics_CBV as SOS
import           System.IO
import           System.IO.Unsafe
import           Text.Parsec.Combinator
import           Text.Parsec.Error
import           Text.Parsec.Prim                   hiding (label)
import           Text.Parsec.String                 (Parser)
import           Typing                             as T


-- | The actual parser that should be used to parse an entire program
programParser :: Parser S.Term
programParser = whitespace *> termParser <* eof

-- helper functions

typeAnnotation :: Parser (S.Label, S.Type)
typeAnnotation = (,) <$> label
                     <*> (colon *> typeParser)

recordInternal :: Parser (S.Label, S.Term)
recordInternal = (,) <$> label
                     <*> (equal *> termParser)

caseInternal :: Parser (S.Label, S.Var, S.Term)
caseInternal = (,,) <$> label
                    <*> (equal *> var)
                    <*> (thickArrow *> termParser)

caseOptions :: Parser [(S.Label, S.Var, S.Term)]
caseOptions = caseInternal `sepBy1` bar

-- The largest parsers

typeParser :: Parser S.Type
typeParser = try (S.TypeArrow <$> (arrow *> lpar *> typeParser) <*> (comma *> typeParser <* rpar))
         <|> try (S.TypeBool <$ kw "Bool")
         <|> try (S.TypeInt <$ kw "Int")
         <|> try (S.TypeChar <$ kw "Char")
         <|> try (S.TypeUnit <$ kw "Unit")
         <|> try (S.TypeRecord <$> (kw "Record" *> tuple typeAnnotation))
         <|> try (S.TypeVariant <$> (kw "Variant" *> tuple typeAnnotation))
         <|> try (S.TypeMu <$> (kw "Mu" *> lpar *> type_var) <*> (fullstop *> typeParser <* rpar))
         <|> try (S.TypeVar <$> (type_var))

termParser :: Parser S.Term
termParser =
        try (S.Var <$> var)
    <|> try (S.Const . S.IntConst <$> intliteral)
    <|> try (S.Const S.Tru <$ kw "true")
    <|> try (S.Const S.Fls <$ kw "false")
    <|> try (S.Const . S.CharConst <$> charConst)
    <|> try (S.Const S.Unit <$ kw "unit")
    <|> try (S.Abs <$> (kw "abs" *> lpar *> identifier)
                   <*> (colon *> typeParser)
                   <*> (fullstop *> termParser) <* rpar)
    <|> try (S.Fix <$> (kw "fix" *> lpar *> termParser) <* rpar) -- not implemented
    <|> try (S.App <$> (kw "app" *> lpar *> termParser)
                   <*> (comma *> termParser) <* rpar)
    <|> try (S.If <$> (kw "if" *> termParser)
                  <*> (kw "then" *> termParser)
                  <*> (kw "else" *> termParser) <* kw "fi")
    <|> try (S.Let <$> (kw "let" *> identifier)
                   <*> (equal *> termParser)
                   <*> (kw "in" *> termParser) <* kw "end")
    <|> try (S.PrimApp <$> primOp
                       <*> (lpar *> termParser `sepBy1` comma) <* rpar)
    <|> try (S.Project <$> (kw "project" *> lpar *> termParser)
                       <*> (fullstop *> identifier) <* rpar)
    <|> try (S.Record <$> (kw "record" *> tuple recordInternal))
    <|> try (S.Tag <$> (kw "tag" *> lpar *> label)
                   <*> (equal *> termParser)
                   <*> (kw "as" *> typeParser) <* rpar)
    <|> try (S.Case <$> (kw "case" *> termParser)
                    <*> (kw "of" *> caseOptions) <* kw "esac")
    <|> try (S.Fold <$> (kw "fold" *> lpar *> typeParser)
                    <*> (comma *> termParser) <* rpar)
    <|> try (S.Unfold <$> (kw "unfold" *> lpar *> typeParser)
                    <*> (comma *> termParser) <* rpar)
    <|> try (lpar *> termParser <* rpar)

-- | Function debugging in repl
parseFile :: FilePath -> IO ()
parseFile fname = do
                  inh <- openFile fname ReadMode
                  file_data <- hGetContents inh
                  let x = case parse programParser "" file_data of
                        Left err            -> error (show err)
                        Right parsedProgram -> parsedProgram
                  putStrLn ("GIVEN PROGRAM: " ++ show x)
                  putStrLn ("Free Variables: " ++ show (S.fv x))
                  putStrLn ("Typechecker: " ++ show (T.typeCheck x))
                  putStrLn ("Evaluator: " ++ show (SOS.eval x))

parseFileDebug :: FilePath -> IO ()
parseFileDebug fname = do inh <- openFile fname ReadMode
                          file_data <- hGetContents inh
                          let x = case parse programParser "" file_data of
                                Left err            -> error (show err)
                                Right parsedProgram -> parsedProgram
                          putStrLn ("GIVEN PROGRAM: " ++ show x)
                          putStrLn ("Free Variables: " ++ show (S.fv x))
                          putStrLn ("Typechecker: " ++ show (T.typeCheck x))
                          putStrLn ("Evaluator: " ++ "\n" ++ (show (SOS.eval_trace x)))
                
parseFileNoTypeCheck :: FilePath -> IO ()
parseFileNoTypeCheck fname = do
                  inh <- openFile fname ReadMode
                  file_data <- hGetContents inh
                  let x = case parse programParser "" file_data of
                        Left err            -> error (show err)
                        Right parsedProgram -> parsedProgram
                  putStrLn ("GIVEN PROGRAM: " ++ show x)
                  putStrLn ("Free Variables: " ++ show (S.fv x))
                  putStrLn ("Evaluator: " ++ show (SOS.eval x))

parseFile_bigStep :: FilePath -> IO ()
parseFile_bigStep fname = do
                  inh <- openFile fname ReadMode
                  file_data <- hGetContents inh
                  let x = case parse programParser "" file_data of
                        Left err            -> error (show err)
                        Right parsedProgram -> parsedProgram
                  putStrLn ("GIVEN PROGRAM: " ++ show x)
                  putStrLn ("Free Variables: " ++ show (S.fv x))
                  putStrLn ("Typechecker: " ++ show (T.typeCheck x))
                  let evalOfX = SOS.eval_prime x
                  putStrLn ("Evaluator: " ++ show evalOfX)


-- For test/Test.Hs
parseOnly :: FilePath -> IO (Maybe String)
parseOnly fname = do
    inh <- openFile fname ReadMode
    fileData <- hGetContents inh
    case parse programParser "" fileData of
        Right success -> return $ Just $ show success
        Left err      -> return Nothing

parseProgram :: FilePath -> IO S.Term
parseProgram fname = do
        inh <- openFile fname ReadMode
        fileData <- hGetContents inh
        case parse programParser "" fileData of
                Left err -> error $ show err
                Right x  -> return x

reductionSem x = do
        prgm <- parseProgram x
        return $ RS.makeEvalContext prgm

typeCheckTerm :: S.Term -> S.Type
typeCheckTerm t = T.typeCheck t

parseFVar :: FilePath -> IO (Maybe [String])
parseFVar fname = do
    inh <- openFile fname ReadMode
    fileData <- hGetContents inh
    let x = case parse programParser "" fileData of
                Right parsedProgram -> Just parsedProgram
                Left errMsg         -> Nothing
    return $ S.fv <$> x

parseFVarTypeCheck :: FilePath -> IO (Maybe String)
parseFVarTypeCheck fname = do
    inh <- openFile fname ReadMode
    fileData <- hGetContents inh
    let x = case parse programParser "" fileData of
            Right parsedProgram -> Just parsedProgram
            Left errMsg         -> Nothing
    let y = case S.fv <$> x of
            Just [] -> x
            _       -> Nothing
    return $ case T.typeCheck <$> y of
            Just (S.TypeError errMsg) -> Nothing
            Just tau                  -> Just $ show tau
            Nothing                   -> Nothing

testEval :: FilePath -> IO (Maybe String)
testEval fname = do
    inh <- openFile fname ReadMode
    fileData <- hGetContents inh
    return (do
        parsedProgram <- case parse programParser "" fileData of
                            Right x -> Just x
                            Left _  -> Nothing
        _ <- case S.fv parsedProgram of
                [] -> Just parsedProgram
                _  -> Nothing
        _ <- case T.typeCheck parsedProgram of
                (S.TypeError errMsg) -> Nothing
                _                    -> Just parsedProgram
        case SOS.eval parsedProgram of
            (S.ErrorTerm err) -> Nothing
            success           -> return $ show success)


