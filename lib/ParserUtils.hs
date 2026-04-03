module ParserUtils where

import qualified AbstractSyntax         as S
import           Control.Monad
import qualified IntegerArithmetic      as I
import           Text.Parsec.Char
import           Text.Parsec.Combinator
import           Text.Parsec.Prim
import           Text.Parsec.String

comment :: Parser String
comment = try (string "--" *> manyTill anyChar (choice [newline, fmap (const '\\') eof ]))
      <|> string "{-" *> manyTill anyChar (try $ string "-}")

-- | parses whitespace, fails if there is no whitespace.
whitespace :: Parser [String]
whitespace = many $ choice [many1 (oneOf " \n\t\r"), comment]

-- | Parses a string that is followed by at least
-- | 1 whitespace character
stringSpace :: String -> Parser String
stringSpace s = string s <* whitespace

charSpace :: Char -> Parser Char
charSpace c = char c <* whitespace

arrow :: Parser String
arrow = stringSpace "->"

thickArrow :: Parser String
thickArrow = stringSpace "=>"

equal :: Parser Char
equal = charSpace '='

lpar :: Parser Char
lpar = charSpace '('

comma :: Parser Char
comma = charSpace ','

rpar :: Parser Char
rpar = charSpace ')'

bar :: Parser Char
bar = charSpace '|'

identifier :: Parser S.Var
identifier = do
    firstLetter <- letter
    restOfString <- many $ letter <|> digit <|> char '\''
    let identifierString = firstLetter : restOfString
    when (identifierString `elem` keywordList) (fail "Keywords cannot be identifiers")
    _ <- notFollowedBy letter
    _ <- whitespace
    return identifierString

type_indentifer :: Parser S.TypeVar
type_indentifer = do
    identifierString <- many $ letter <|> digit
    when (identifierString `elem` keywordList) (fail "Keywords cannot be identifiers")
    _ <- notFollowedBy letter
    _ <- whitespace
    return identifierString

var :: Parser S.Var
var = identifier

type_var :: Parser S.TypeVar
type_var = type_indentifer

label :: Parser S.Var
label = identifier

colon :: Parser Char
colon = charSpace ':'

fullstop :: Parser Char
fullstop = charSpace '.'

-- | add to avoid the current whitespace issues.
keyword :: String -> Parser String
keyword s = if s `elem` keywordList
    then string s <* notFollowedBy letter <* whitespace
    else error (s ++ " is not a keyword and cannot be used as one unless in keywordList. ")

charConst :: Parser Char
charConst = char '\'' *> (escapeChar <|> anyChar) <* char '\''

escapeChar :: Parser Char
escapeChar = char '\\' *> (('\n' <$ char 'n' ) <|> ('\t' <$ char 't' ))

-- | alias for keyword
kw :: String -> Parser String
kw = keyword

keywordList :: [String]
keywordList = [
    "Bool", "Int", "Char",
    "Unit", "unit",
    "abs", "app", "fix",
    "true", "false",
    "if", "then", "else", "fi",
    "let", "in", "end",
    "Record", "record", "project",
    "Variant", "case", "of", "|", "esac",
    "tag", "=", "as",
    "ord", "chr", "Mu", "fold", "unfold"]


intliteral :: Parser I.IntegerType
intliteral = fmap read (many1 digit) <* whitespace

primOp :: Parser S.PrimOp
primOp = choice $ uncurry singlePrimOp <$> primOpList

singlePrimOp :: String -> S.PrimOp -> Parser S.PrimOp
singlePrimOp s op = stringSpace s >> return op

primOpList :: [(String, S.PrimOp)]
primOpList = [
    ("+", S.IntAdd), -- add
    ("-", S.IntSub), -- minus
    ("*", S.IntMul), -- mul
    ("/", S.IntDiv), -- div
    ("^", S.IntNand), -- nand
    ("=", S.IntEq), -- equals
    ("<", S.IntLt), -- less than
    ("ord", S.CharOrd),
    ("chr", S.CharChr)
    ]

tuple :: Parser a -> Parser [a]
tuple p = lpar *> (p `sepBy1` comma) <* rpar
