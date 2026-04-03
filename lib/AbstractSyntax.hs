{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
{-# LANGUAGE InstanceSigs #-}
module AbstractSyntax where

import           Control.Monad.Fail
import           Data.List
import qualified IntegerArithmetic  as I
import           Latex

type Label = String

data Type  =  TypeArrow      Type Type
           |  TypeBool
           |  TypeInt
           |  TypeChar
           |  TypeUnit
           |  TypeRecord     [(Label, Type)]
           |  TypeVariant    [(Label, Type)]
           |  TypeVar TypeVar
           |  TypeMu TypeVar Type
           |  TypeError String

instance Eq Type where
  tau1 == tau2 = typeEq tau1 tau2

typeEq :: Type -> Type -> Bool
typeEq tau tau' = case (tau, tau') of
    (TypeArrow tau1 tau2, TypeArrow tau1' tau2')   ->  typeEq tau1 tau1' && typeEq tau2 tau2'
    (TypeBool, TypeBool)                           ->  True
    (TypeInt, TypeInt)                             ->  True
    (TypeChar, TypeChar)                           ->  True
    (TypeUnit, TypeUnit)                           ->  True
    (TypeRecord ltaus, TypeRecord ltaus')          ->  sorted_ltaus == sorted_ltaus'
        where
            sorted_ltaus = sortBy (\a b -> fst a `compare` fst b) ltaus
            sorted_ltaus' = sortBy (\a b -> fst a `compare` fst b) ltaus'
    (TypeVariant ltaus, TypeVariant ltaus')        ->  sorted_ltaus == sorted_ltaus'
        where
            sorted_ltaus = sortBy (\a b -> fst a `compare` fst b) ltaus
            sorted_ltaus' = sortBy (\a b -> fst a `compare` fst b) ltaus'
    (TypeVar x, TypeVar y)                         -> x == y
    (TypeMu x1 tau1, TypeMu x2 tau2)               -> (x1 == x2) && (typeEq tau1 tau2)
    _                                              ->  False


instance Show Type where
  show tau = case tau of
    TypeArrow tau1 tau2   ->  "->(" ++ show tau1 ++ "," ++ show tau2 ++ ")"
    TypeBool              ->  "Bool"
    TypeInt               ->  "Int"
    TypeChar              ->  "Char"
    TypeUnit              ->  "Unit"
    TypeRecord ltaus      ->  "Record(" ++ intercalate ", " (map (\(l,tau') -> l ++ ": " ++ show tau') ltaus) ++ ")"
    TypeVariant ltaus     ->  "Variant(" ++ intercalate ", " (map (\(l,tau') -> l ++ ": " ++ show tau') ltaus) ++ ")"
    TypeVar x             ->  x
    TypeMu x tau         ->  "Mu(" ++ x ++ "." ++ (show tau) ++ ")"
    TypeError err -> "TypeError: " ++ err

instance LatexShow Type where
  latexShow tau = case tau of
    TypeArrow tau1 tau2   ->  "$\\rightarrow$ (" ++ latexShow tau1 ++ ", " ++ latexShow tau2 ++ ")"
    TypeBool              ->  "Bool"
    TypeInt               ->  "Int"
    TypeChar              ->  "Char"
    TypeUnit              ->  "Unit"
    TypeRecord ltaus      ->  "$\\lbrace$" ++ intercalate "," (map (\(l,tau') -> l ++ ": " ++ latexShow tau') ltaus) ++ "$\\rbrace$"
    TypeVariant ltaus     ->  "$\\langle$" ++ intercalate "," (map (\(l,tau') -> l ++ ": " ++ latexShow tau') ltaus) ++ "$\\rangle$"
    TypeError s           ->  "TypeError("++ s ++")"

type Var = String
type TypeVar = String

data Environment = Empty | Bind (Var,Term) Environment
  deriving (Eq, Show)

lookupEnv :: Var -> Environment -> Either String Term
lookupEnv x (Bind (y,t) e) = if x == y then return t else (lookupEnv x e)
lookupEnv x Empty          = Left ("Couldn't find " ++ x ++ " in environment.")

data Term  =
              -- lambda-calculus forms
              Var         Var
           |  Abs         Var Type Term
           |  App         Term Term
              -- extension for big-step semantics
           |  Closure      Term Environment
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
           |  Fold Type Term
           |  Unfold Type Term
           |  ErrorTerm   String
           deriving Eq

data Const = Tru | Fls | IntConst I.IntegerType | CharConst Char | Unit
             deriving Eq

instance Show Const where
  show c = case c of
    Tru          ->  "true"
    Fls          ->  "false"
    IntConst i   ->  show i
    CharConst ch ->  show ch
    Unit         ->  "unit"

instance LatexShow Const where
  latexShow c = show c

constType :: Const -> Type
constType c = case c of
  Tru         ->  TypeBool
  Fls         ->  TypeBool
  IntConst _  ->  TypeInt
  CharConst _ ->  TypeChar
  Unit        ->  TypeUnit

data PrimOp  =  IntAdd | IntSub | IntMul | IntDiv | IntNand | IntEq | IntLt | CharOrd | CharChr
                deriving Eq
{-
instance Show PrimOp where
  show p = case p of
    IntAdd  ->  "+"
    IntSub  ->  "-"
    IntMul  ->  "*"
    IntDiv  ->  "/"
    IntNand ->  "^"
    IntEq   ->  "="
    IntLt   ->  "<"
    CharOrd ->  "ord"
    CharChr ->  "chr"
-}

-- Detailed showing PrimOp
instance Show PrimOp where
  show p = case p of
    IntAdd  ->  "IntAdd"
    IntSub  ->  "IntSub"
    IntMul  ->  "IntMul"
    IntDiv  ->  "IntDiv"
    IntNand ->  "IntNand"
    IntEq   ->  "IntEq"
    IntLt   ->  "IntLt"
    CharOrd ->  "ord"
    CharChr ->  "chr"

instance LatexShow PrimOp where
  latexShow p = case p of
    IntAdd  ->  "$+$"
    IntSub  ->  "$-$"
    IntMul  ->  "$\\times$"
    IntDiv  ->  "$/$"
    IntNand ->  "$\\uparrow$"
    IntEq   ->  "$=$"
    IntLt   ->  "$<$"
    CharOrd ->  "ord"
    CharChr ->  "chr"

type PrimOpType = ([Type], Type)

arithmeticBinaryPrimOpType :: PrimOpType
arithmeticBinaryPrimOpType = ([TypeInt, TypeInt], TypeInt)

relationalBinaryPrimOpType :: PrimOpType
relationalBinaryPrimOpType = ([TypeInt, TypeInt], TypeBool)

primOpArity :: PrimOp -> Int
primOpArity p = case p of
  IntAdd  ->  2
  IntSub  ->  2
  IntMul  ->  2
  IntDiv  ->  2
  IntNand ->  2
  IntEq   ->  2
  IntLt   ->  2
  CharOrd ->  1
  CharChr ->  1

primOpType :: PrimOp -> PrimOpType
primOpType p = case p of
  IntAdd  ->  arithmeticBinaryPrimOpType
  IntSub  ->  arithmeticBinaryPrimOpType
  IntMul  ->  arithmeticBinaryPrimOpType
  IntDiv  ->  arithmeticBinaryPrimOpType
  IntNand ->  arithmeticBinaryPrimOpType
  IntEq   ->  relationalBinaryPrimOpType
  IntLt   ->  relationalBinaryPrimOpType
  CharOrd ->  ([TypeChar], TypeInt)
  CharChr ->  ([TypeInt], TypeChar)

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
primOpEval x t = Var ((show x) ++ (show t))

instance Show Term where
  show t = case t of
    Var x            ->  x
    Abs x tau t'      ->  "abs(" ++ x ++ ": " ++ show tau ++ ". " ++ show t' ++ ")"
    App t1 t2        ->  "app(" ++ show t1  ++ ", " ++ show t2 ++ ")"
    If t1 t2 t3      ->  "if " ++ show t1 ++ " then " ++ show t2 ++ " else " ++ show t3 ++ " fi"
    Fix t'            ->  "fix(" ++ show t' ++ ")"
    Let x t1 t2      ->  "let " ++ x ++ " = " ++ show t1 ++ " in " ++ show t2 ++ " end"
    Const c          ->  show c
    PrimApp p ts     ->  show p ++ "(" ++ intercalate ", " (map show ts) ++ ")"
    Record lts       ->  "record(" ++ intercalate ", " (map (\(l,t'') -> l ++ " = " ++ show t'') lts) ++ ")"
    Project t' l      ->  "project(" ++ show t' ++ "." ++ l ++ ")"
    Tag l t' tau      ->  "tag(" ++ l ++ " = " ++ show t' ++ " as " ++ show tau ++ ")"
    Case t' lxts      ->  "case " ++ show t' ++ " of "
                         ++ intercalate " | " (map (\(l,x,t'') -> l ++ " = " ++ x ++ " => " ++ show t'') lxts) ++ " esac"
    Fold tau t    -> "fold(" ++ (show tau) ++ "," ++ (show t) ++ ")"
    Unfold tau t  -> "unfold(" ++ (show tau) ++ "," ++ (show t) ++ ")"
    ErrorTerm s -> "EvaluationError: " ++ s

showElidingTypes :: Term -> String
showElidingTypes t = case t of
    Var x            ->  x
    Abs x _ t'      ->  "abs(" ++ x ++ ":. " ++ showElidingTypes t' ++ ")"
    App t1 t2        ->  "app(" ++ showElidingTypes t1  ++ ", " ++ showElidingTypes t2 ++ ")"
    If t1 t2 t3      ->  "if " ++ showElidingTypes t1 ++ " then " ++ showElidingTypes t2 ++ " else " ++ showElidingTypes t3 ++ " fi"
    Fix t'            ->  "fix(" ++ showElidingTypes t' ++ ")"
    Let x t1 t2      ->  "let " ++ x ++ " = " ++ showElidingTypes t1 ++ " in " ++ showElidingTypes t2 ++ " end"
    Const c          ->  show c
    PrimApp p ts     ->  show p ++ "(" ++ intercalate ", " (map showElidingTypes ts) ++ ")"
    Record lts       ->  "record(" ++ intercalate ", " (map (\(l,t'') -> l ++ " = " ++ showElidingTypes t'') lts) ++ ")"
    Project t' l      ->  "project(" ++ showElidingTypes t' ++ "." ++ l ++ ")"
    Tag l t' _      ->  "tag(" ++ l ++ " = " ++ showElidingTypes t' ++ " as)"
    Case t' lxts      ->  "case " ++ showElidingTypes t' ++ " of "
                         ++ intercalate " | " (map (\(l,x,t'') -> l ++ " = " ++ x ++ " => " ++ showElidingTypes t'') lxts) ++ " esac"
    ErrorTerm s -> "[ErrorTerm: " ++ s ++ "]"

instance LatexShow Term where
  latexShow t = case t of
    Var x           ->  x
    Abs x tau t1     ->  "$\\lambda$" ++ x ++ ": " ++ latexShow tau
                         ++ ". " ++ latexShow t1
    App t1 t2       ->  "$\\blacktriangleright$ (" ++ latexShow t1  ++ ", " ++ latexShow t2 ++ ")"
    If t1 t2 t3     ->  "if " ++ latexShow t1 ++ " then " ++ latexShow t2
                         ++ " else " ++ latexShow t3 ++ " fi"
    Fix t1           ->  "fix (" ++ latexShow t1 ++ ")"
    Let x t1 t2     ->  "let " ++ x ++ " = " ++ latexShow t1 ++ " in " ++ latexShow t2 ++ " end"
    Const c         ->  latexShow c
    PrimApp p ts    ->  latexShow p ++ " (" ++ intercalate ", " (map latexShow ts) ++ ")"
    Record lts      ->  "$\\lbrace$" ++ intercalate ", " (map (\(l,t') -> l ++ " $=$ " ++ latexShow t') lts) ++ "$\\rbrace$"
    Project t1 l     ->  latexShow t1 ++ "." ++ l
    Tag l t1 tau     ->  "$\\langle$" ++ l ++ " $=$ " ++ latexShow t1 ++ "$\\rangle$ as " ++ latexShow tau
    Case t1 lxts     ->  "case " ++ latexShow t1 ++ " of "
                        ++ intercalate " $\\talloblong$ " (map (\(l,x,t') -> l ++ "$=$" ++ x ++ "$\\Rightarrow$" ++ latexShow t') lxts)
                        ++ " esac"
    ErrorTerm s -> error s

fv :: Term -> [Var]
fv t = case t of
  ErrorTerm s -> []
  Var x          -> [x]
  Abs x _ t2      -> filter (/= x) (fv t2)
  App x y        -> [x,y] >>= fv
  If x y z       -> [x,y,z] >>= fv
  Const _        -> []
  PrimApp _ xs   -> xs >>= fv
  Let x _ t2      -> filter (/= x) (fv t2)
  Fix x          -> fv x
  Case t1 xs     -> concatMap (\(_, vN, tN) -> filter (/= vN) (fv tN)) xs ++ fv t1
  -- Case t1 xs     -> filter (`notElem` vars) (fv t1 ++ concatMap fv terms) where (labels, vars, terms) = unzip3 xs
  Tag _ t1 _ -> fv t1
  Project t1 _ -> fv t1
  Record labelsAndTerms -> concatMap (fv . snd) labelsAndTerms
  Unfold _ t1 -> fv t1
  Fold _ t1 -> fv t1
  -- _              -> error (show t ++ " is not implemented in fv")

-- | substitute a type variable iwth a type in a type (for mu operator)
-- Format : substT X for T1 in T2
substT :: TypeVar -> Type -> Type -> Type
substT chi s tau = case tau of
  TypeVar chi1        -> if chi == chi1 then s else tau
  TypeRecord ltaus    -> TypeRecord $ map (\(l', tau') -> (l', (chi |-> s) tau')) ltaus
  TypeVariant ltaus   -> TypeVariant $ map (\(l', tau') -> (l', (chi |-> s) tau')) ltaus
  TypeArrow tau1 tau2 -> undefined
  TypeBool            -> TypeBool
  TypeInt             -> TypeInt
  TypeChar            -> TypeChar
  TypeUnit            -> TypeUnit
  TypeMu chi1 tau1    -> undefined
  TypeError err       -> TypeError err
-- substT  chi1 tau2 tau1@(TypeVar chi2)
--   | chi1 == chi2 = tau2
--   | otherwise    = tau1
-- substT chi1 tau2 (TypeRecord xs) = TypeRecord [(label, substT chi1 tau tau2) | (label, tau) <- xs]
-- substT chi1 tau2 (TypeVariant xs) = TypeRecord [(label, substT chi1 tau tau2) | (label, tau) <- xs]
-- substT chi1 tau4 (TypeArrow tau2 tau3) = TypeArrow (substT chi1 tau2 tau4) (substT chi1 tau3 tau4)
-- substT _ _ TypeBool = TypeBool
-- substT _ _ TypeInt = TypeInt
-- substT _ _ TypeChar = TypeChar
-- substT _ _ TypeUnit = TypeUnit
-- substT _ tau1@(TypeError _) _ = tau1
-- substT chi1 tau2 tau3 = TypeError $ ("(" ++ chi1 ++ " |-> " ++ show tau2 ++ ") " ++ show tau3 ++ "is not valid")

-- | substitute a variable with a term in a term
subst :: Var -> Term -> Term -> Term
subst x s t = case t of
  Var y             -> if y == x then s else Var y
  Abs y tau bod     -> if ((x /= y) && (y `notElem` (fv s))) then (Abs y tau (subst x s bod)) else t
  App y z           -> App (subst x s y) (subst x s z)
  If y z w          -> If (subst x s y) (subst x s z ) (subst x s w)
  Const _           -> t
  PrimApp func xs   -> PrimApp func (fmap (subst x s) xs)
  Fix t' -> Fix (subst x s t') -- no idea if this works !!!!
  Project t1 label -> Project (subst x s t1) label
  Case t1 lvt -> Case (subst x s t1) ((\(l', v', t') -> if v' == x then (l', v',t') else (l', v', subst x s t')) <$> lvt) -- check that v' is not equal to x
  Record lt -> Record $ map (\(l', t') -> (l', subst x s t')) lt
  Tag l t1 tau1 -> Tag l (subst x s t1) tau1
  Let var t1 t2 -> Let var (subst x s t1) (if (var == x) then t2 else (subst x s t2))
  Unfold tau t1 -> Unfold tau (subst x s t1)
  Fold tau t1 -> Fold tau (subst x s t1)
  _ -> ErrorTerm $ "Not a valid term in 'subst': " ++ show t
  -- _            -> error ("substitute " ++ x ++ " into " ++ show t ++ " is not implemented in subst")

-- | substitution: "(x |-> t2) t1" is "[x ↦ t2] t1"
instance Substitutable Term where
  (|->) :: String -> Term -> Term -> Term
  (|->) = subst

instance Substitutable Type where
  (|->) = substT
-- | substitution: "(x |-> t2) t1" is "[x ↦ t2] t1"
-- (↦) :: Var -> Term -> Term -> Term


isValue :: Term -> Bool
isValue t = case t of
  Abs {}     ->  True
  Closure {} ->  True
  Const _    ->  True
  Record lts ->  all (isValue . snd) lts
  Tag _ t' _ ->  isValue t'
  Fold _ t'  -> isValue t'
  _          ->  False

isNotValue :: Term -> Bool
isNotValue = not . isValue

class Substitutable a where
  -- | Substitute String in a1 with a2 yielding a3
  (|->) :: String -> a -> a -> a
  (↦) :: String -> a -> a -> a
  (↦) = (|->)
