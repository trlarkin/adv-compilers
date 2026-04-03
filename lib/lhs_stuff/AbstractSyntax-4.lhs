\begin{code}
module AbstractSyntax where

import Data.Maybe
import Data.List
import Latex
import qualified IntegerArithmetic as I

\end{code}
\newpage
\section{Abstract-syntactic preliminaries}
\subsection{Source types}
\begin{code}
type Label = String

type TypeVar  =  String

data Type  =  TypeArrow      Type Type
           |  TypeBool
           |  TypeInt
           |  TypeChar
           |  TypeUnit
           |  TypeRecord     [(Label, Type)]
           |  TypeVariant    [(Label, Type)]
           |  TypeVar        TypeVar
           |  TypeMu         Int [TypeVar] [Type]

instance Eq Type where
  tau1 == tau2 = typeEq [] tau1 tau2

typeEq :: [(TypeVar, TypeVar)] -> Type -> Type -> Bool
typeEq env tau tau' = case (tau, tau') of
        
instance Show Type where
  show tau = case tau of
    TypeArrow tau1 tau2   ->  "->(" ++ show tau1 ++ "," ++ show tau2 ++ ")"
    TypeBool              ->  "Bool"
    TypeInt               ->  "Int"
    TypeChar              ->  "Char"
    TypeUnit              ->  "Unit"
    TypeRecord ltaus      ->  "Record(" ++ intercalate ", " (map (\(l,tau) -> l ++ ": " ++ show tau) ltaus) ++ ")"
    TypeVariant ltaus     ->  "Variant(" ++ intercalate ", " (map (\(l,tau) -> l ++ ": " ++ show tau) ltaus) ++ ")"
    TypeVar xi            ->  xi
    TypeMu 0 [xi] [tau]   ->  "Mu (" ++ xi ++ "." ++ show tau ++ ")"
    TypeMu i xis taus     ->  "Mu " ++ show i ++ " (" ++ intercalate "," xis ++ ").(" ++ intercalate "," (map show taus) ++ ")"

instance LatexShow Type where
  latexShow tau = case tau of
    TypeArrow tau1 tau2   ->  "$\\rightarrow$ (" ++ latexShow tau1 ++ ", " ++ latexShow tau2 ++ ")"
    TypeBool              ->  "Bool"
    TypeInt               ->  "Int"
    TypeChar              ->  "Char"
    TypeUnit              ->  "Unit"
    TypeRecord ltaus      ->  "$\\lbrace$" ++ intercalate "," (map (\(l,tau) -> l ++ ": " ++ latexShow tau) ltaus) ++ "$\\rbrace$"
    TypeVariant ltaus     ->  "$\\langle$" ++ intercalate "," (map (\(l,tau) -> l ++ ": " ++ latexShow tau) ltaus) ++ "$\\rangle$"
    TypeVar xi            ->  xi
    TypeMu 0 [xi] [tau]   ->  "$\\mu$(" ++ xi ++ "." ++ latexShow tau ++ ")"
    TypeMu i xis taus     ->  "$\\mu_{" ++ show i ++ "}$(" ++ intercalate "," xis ++ ").(" ++ intercalate "," (map latexShow taus) ++ ")"
\end{code}

\subsection{Certain types used in the prelude and known to the interpreters and compilers}
\begin{code}
typeIntList :: Type
typeIntList = TypeMu 0 ["X"] [TypeVariant [("nil", TypeUnit), ("cons", TypeRecord [("fst", TypeInt), ("snd", TypeVar "X")])]]

typeCharList :: Type
typeCharList = TypeMu 0 ["X"] [TypeVariant [("nil", TypeUnit), ("cons", TypeRecord [("fst", TypeChar), ("snd", TypeVar "X")])]]

typeString :: Type
typeString = typeCharList

typeStringUnfolded :: Type
typeStringUnfolded = TypeVariant [("nil", TypeUnit), ("cons", TypeRecord [("fst", TypeChar), ("snd", typeString)])]

typeStringStringFun :: Type
typeStringStringFun = TypeArrow typeString typeString

encodeString :: String -> Term
encodeString = foldr cons' nil'
               where
                 nil' :: Term
                 nil' = Fold typeString (Tag "nil" (Const Unit) typeStringUnfolded)
                 cons' :: Char -> Term -> Term
                 cons' c s = Fold typeString (Tag "cons" (Record [("fst", Const (CharConst c)), ("snd", s)]) typeStringUnfolded)

decodeString :: Term -> String
decodeString t = case t of
  Fold tau t1
    | tau == typeString ->
        case t1 of
          Tag "nil" (Const Unit) tau'
            | tau' == typeStringUnfolded -> []
          Tag "cons" (Record [("fst", Const (CharConst c)), ("snd", s)]) tau'
            | tau' == typeStringUnfolded -> c : decodeString s
  _ -> error "string-decoding a non-string term"
\end{code}

\subsection{Source terms}
\begin{code}
type Var = String

data Term  =
              -- lambda-calculus forms
              Var         Var
           |  Abs         Var Type Term
           |  App         Term Term
              -- extensions (lazy conditional; general recursion; and let-binding)
           |  If          Term Term Term
           |  Fix         Term
           |  Let         Var Term Term
              -- constants
           |  Const       Const
              -- primitive operator applications
           |  PrimApp     PrimOp [Term]
              -- data structures
           |  Record      [(Label, Term)]
           |  Project     Term Label
           |  Tag         Label Term Type
           |  Case        Term [(Label, Var, Term)]
           |  Fold        Type Term
           |  Unfold      Type Term
           deriving Eq

data Const = Tru | Fls | IntConst I.IntegerType | CharConst Char | Unit
             deriving Eq

instance Show Const where
  show c = case c of
    Tru              ->  "true"
    Fls              ->  "false"
    IntConst i       ->  show i
    CharConst c      ->  show c
    Unit             ->  "unit"

instance LatexShow Const where
  latexShow c = show c

constType :: Const -> Type
constType c = case c of
  Tru          ->  TypeBool
  Fls          ->  TypeBool
  IntConst _   ->  TypeInt
  CharConst _  ->  TypeChar
  Unit         ->  TypeUnit

data PrimOp  =  IntAdd | IntSub | IntMul | IntDiv | IntNand | IntEq | IntLt | CharOrd | CharChr
                deriving Eq

instance Show PrimOp where
  show p = case p of
    IntAdd   ->  "+"
    IntSub   ->  "-"
    IntMul   ->  "*"
    IntDiv   ->  "/"
    IntNand  ->  "^"
    IntEq    ->  "="
    IntLt    ->  "<"
    CharOrd  ->  "ord"
    CharChr  ->  "chr"

instance LatexShow PrimOp where
  latexShow p = case p of
    IntAdd   ->  "$+$"
    IntSub   ->  "$-$"
    IntMul   ->  "$\\times$"
    IntDiv   ->  "$/$"
    IntNand  ->  "$\\uparrow$"
    IntEq    ->  "$=$"
    IntLt    ->  "$<$"
    CharOrd  ->  "ord"
    CharChr  ->  "chr"

type PrimOpType = ([Type], Type)

arithmeticBinaryPrimOpType :: PrimOpType
arithmeticBinaryPrimOpType = ([TypeInt, TypeInt], TypeInt)

relationalBinaryPrimOpType :: PrimOpType
relationalBinaryPrimOpType = ([TypeInt, TypeInt], TypeBool)

primOpArity :: PrimOp -> Int
primOpArity p = case p of
  IntAdd   ->  2
  IntSub   ->  2
  IntMul   ->  2
  IntDiv   ->  2
  IntNand  ->  2
  IntEq    ->  2
  IntLt    ->  2
  CharOrd  ->  1
  CharChr  ->  1

primOpType :: PrimOp -> PrimOpType
primOpType p = case p of
  IntAdd   ->  arithmeticBinaryPrimOpType
  IntSub   ->  arithmeticBinaryPrimOpType
  IntMul   ->  arithmeticBinaryPrimOpType
  IntDiv   ->  arithmeticBinaryPrimOpType
  IntNand  ->  arithmeticBinaryPrimOpType
  IntEq    ->  relationalBinaryPrimOpType
  IntLt    ->  relationalBinaryPrimOpType
  CharOrd  ->  ([TypeChar], TypeInt)
  CharChr  ->  ([TypeInt], TypeChar)

primOpEval :: PrimOp -> [Term] -> Term
primOpEval IntAdd [Const (IntConst i1), Const (IntConst i2)] = Const (IntConst (I.intAdd i1 i2))
primOpEval IntSub [Const (IntConst i1), Const (IntConst i2)] = Const (IntConst (I.intSub i1 i2))
primOpEval IntMul [Const (IntConst i1), Const (IntConst i2)] = Const (IntConst (I.intMul i1 i2))
primOpEval IntDiv [Const (IntConst i1), Const (IntConst i2)] = Const (IntConst (I.intDiv i1 i2))
primOpEval IntNand [Const (IntConst i1), Const (IntConst i2)] = Const (IntConst (I.intNand i1 i2))
primOpEval IntEq [Const (IntConst i1), Const (IntConst i2)] = Const (if I.intEq i1 i2 then Tru else Fls)
primOpEval IntLt [Const (IntConst i1), Const (IntConst i2)] = Const (if I.intLt i1 i2 then Tru else Fls)
primOpEval CharOrd [Const (CharConst c)] = Const (IntConst (I.intOrd c))
primOpEval CharChr [Const (IntConst i)] = Const (CharConst (I.intChr i))

instance Show Term where
  show t = case t of
    Var x            ->  x
    Abs x tau t      ->  "abs(" ++ x ++ ": " ++ show tau ++ ". " ++ show t ++ ")"
    App t1 t2        ->  "app(" ++ show t1  ++ ", " ++ show t2 ++ ")"
    If t1 t2 t3      ->  "if " ++ show t1 ++ " then " ++ show t2 ++ " else " ++ show t3 ++ " fi"
    Fix t            ->  "fix(" ++ show t ++ ")"
    Let x t1 t2      ->  "let " ++ x ++ " = " ++ show t1 ++ " in " ++ show t2 ++ " end"
    Const c          ->  show c
    PrimApp p ts     ->  show p ++ "(" ++ intercalate ", " (map show ts) ++ ")"
    Record lts       ->  "record(" ++ intercalate ", " (map (\(l,t) -> l ++ " = " ++ show t) lts) ++ ")"
    Project t l      ->  "project(" ++ show t ++ "." ++ l ++ ")"
    Tag l t tau      ->  "tag(" ++ l ++ " = " ++ show t ++ " as " ++ show tau ++ ")"
    Case t lxts      ->  "case " ++ show t ++ " of "
                         ++ intercalate " | " (map (\(l,x,t) -> l ++ " = " ++ x ++ " => " ++ show t) lxts) ++ " esac"
    Fold tau t       ->  "fold(" ++ show tau ++ ", " ++ show t ++ ")"
    Unfold tau t     ->  "unfold(" ++ show tau ++ ", " ++ show t ++ ")"

showElidingTypes :: Term -> String
showElidingTypes t = case t of
    Var x            ->  x
    Abs x tau t      ->  "abs(" ++ x ++ ":. " ++ showElidingTypes t ++ ")"
    App t1 t2        ->  "app(" ++ showElidingTypes t1  ++ ", " ++ showElidingTypes t2 ++ ")"
    If t1 t2 t3      ->  "if " ++ showElidingTypes t1 ++ " then " ++ showElidingTypes t2 ++ " else " ++ showElidingTypes t3 ++ " fi"
    Fix t            ->  "fix(" ++ showElidingTypes t ++ ")"
    Let x t1 t2      ->  "let " ++ x ++ " = " ++ showElidingTypes t1 ++ " in " ++ showElidingTypes t2 ++ " end"
    Const c          ->  show c
    PrimApp p ts     ->  show p ++ "(" ++ intercalate ", " (map showElidingTypes ts) ++ ")"
    Record lts       ->  "record(" ++ intercalate ", " (map (\(l,t) -> l ++ " = " ++ showElidingTypes t) lts) ++ ")"
    Project t l      ->  "project(" ++ showElidingTypes t ++ "." ++ l ++ ")"
    Tag l t tau      ->  "tag(" ++ l ++ " = " ++ showElidingTypes t ++ " as)"
    Case t lxts      ->  "case " ++ showElidingTypes t ++ " of "
                         ++ intercalate " | " (map (\(l,x,t) -> l ++ " = " ++ x ++ " => " ++ showElidingTypes t) lxts) ++ " esac"
    Fold tau t       ->  "fold(" ++ showElidingTypes t ++ ")"
    Unfold tau t     ->  "unfold(" ++ showElidingTypes t ++ ")"

instance LatexShow Term where
  latexShow t = case t of
    Var x           ->  x
    Abs x tau t     ->  "$\\lambda$" ++ x ++ ": " ++ latexShow tau
                         ++ ". " ++ latexShow t
    App t1 t2       ->  "$\\blacktriangleright$ (" ++ latexShow t1  ++ ", " ++ latexShow t2 ++ ")"
    If t1 t2 t3     ->  "if " ++ latexShow t1 ++ " then " ++ latexShow t2
                         ++ " else " ++ latexShow t3 ++ " fi"
    Fix t           ->  "fix (" ++ latexShow t ++ ")"
    Let x t1 t2     ->  "let " ++ x ++ " = " ++ latexShow t1 ++ " in " ++ latexShow t2 ++ " end"
    Const c         ->  latexShow c
    PrimApp p ts    ->  latexShow p ++ " (" ++ intercalate ", " (map latexShow ts) ++ ")"
    Record lts      ->  "$\\lbrace$" ++ intercalate ", " (map (\(l,t) -> l ++ " $=$ " ++ latexShow t) lts) ++ "$\\rbrace$"
    Project t l     ->  latexShow t ++ "." ++ l
    Tag l t tau     ->  "$\\langle$" ++ l ++ " $=$ " ++ latexShow t ++ "$\\rangle$ as " ++ latexShow tau
    Case t lxts     ->  "case " ++ latexShow t ++ " of "
                        ++ intercalate " $\\talloblong$ " (map (\(l,x,t) -> l ++ "$=$" ++ x ++ "$\\Rightarrow$" ++ latexShow t) lxts)
                        ++ " esac"
    Fold tau t      ->  "fold [" ++ latexShow tau ++ "] " ++ latexShow t
    Unfold tau t    ->  "unfold [" ++ latexShow tau ++ "] " ++ latexShow t
\end{code}


\newpage
\subsection{Binding and free variables}
\begin{code}
fv :: Term -> [Var]
fv t = case t of


ftv :: Type -> [TypeVar]
ftv tau = case tau of
\end{code}

\newpage
\subsection{Substitution}
Substitution: |subst x s t|, or $[x \mapsto s]t$ in Pierce, 
is the result of substituting |s| for |x| in |t|.

\begin{code}
subst :: Var -> Term -> Term -> Term
subst x s t = case t of

typeSubst :: [TypeVar] -> [Type] -> Type -> Type
typeSubst xis sigmas tau = case tau of

pickfresh :: String -> [String] -> String
pickfresh v avoidlist
  | v `elem` avoidlist  =  pickfresh (v++"'") avoidlist 
  | otherwise           =  v

typeExpand :: Type -> Type
typeExpand (TypeMu i alphas taus) = 
\end{code}

\newpage
Syntactic values:

\begin{code}
isValue :: Term -> Bool
isValue t = case t of
  Abs _ _ _      ->  True
  Const _        ->  True
  Record lts     ->  all isValue (snd (unzip lts))
  Tag _ t _      ->  isValue t
  Fold _ t       ->  isValue t
  _              ->  False
\end{code}
