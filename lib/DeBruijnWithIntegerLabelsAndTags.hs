{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
module DeBruijnWithIntegerLabelsAndTags
       (Type(..),
        S.Const(..),
        S.PrimOp(..),
        Term(..),
        toDeBruijn,
        toDeBruijnType,
        primOpEval,
        constFromDeBruijn,
        fromValueDeBruijn,
        isValue,
        shift,
        subst,
        typeExpand,
        (|->)
       ) where

import           Data.Bifunctor
import           Data.Either
import           Data.Function
import           Data.List
import           Data.Maybe
-- import           Utils          as U

import qualified AbstractSyntax as S
import           Latex
import qualified Typing         as T

type Const = S.Const
type PrimOp = S.PrimOp

data Type  =  TypeArrow      Type Type
           |  TypeBool
           |  TypeInt
           |  TypeChar
           |  TypeUnit
           |  TypeRecord     [Type]
           |  TypeVariant    [Type]
           |  TypeVar        S.TypeVar
           |  TypeMu         S.TypeVar Type

instance Show Type where
  show tau = case tau of
    TypeArrow tau1 tau2   ->  "->(" ++ show tau1 ++ "," ++ show tau2 ++ ")"
    TypeBool              ->  "Bool"
    TypeInt               ->  "Int"
    TypeChar              ->  "Char"
    TypeUnit              ->  "Unit"
    TypeRecord taus       ->  "Record("
                                ++ intercalate ", " (zipWith (\ i tau' -> "<"
                                                                        ++ show i ++ ">" ++ ": "
                                                                        ++ show tau') ([0..] :: [Integer]) taus)
                                ++ ")"
    TypeVariant taus      ->  "Variant("
                                ++ intercalate ", " (zipWith (\ i tau' -> "<" ++ show i ++ ">" ++ ": " ++ show tau') ([0..] :: [Integer]) taus)
                                ++ ")"
    TypeVar xi            ->  xi
    TypeMu chi tau' -> "Mu (" ++ chi ++ "." ++ show tau' ++ ")"
    -- TypeMu 0 [xi] [tau]   ->  "Mu (" ++ xi ++ "." ++ show tau ++ ")"
    -- TypeMu i xis taus     ->  "Mu " ++ show i ++ " (" ++ intercalate "," xis ++ ").("
    --                             ++ intercalate "," (map show taus) ++ ")"

instance LatexShow Type where
  latexShow tau = case tau of
    TypeArrow tau1 tau2   ->  "$\\rightarrow$ (" ++ latexShow tau1 ++ ", " ++ latexShow tau2 ++ ")"
    TypeBool              ->  "Bool"
    TypeInt               ->  "Int"
    TypeChar              ->  "Char"
    TypeUnit              ->  "Unit"
    TypeRecord taus       ->  "$\\lbrace$"
                                ++ intercalate "," (zipWith (\ i tau' -> "$<$" ++ show i ++ "$>$" ++ ": " ++ latexShow tau')
                                                            ([0..] :: [Integer]) taus)
                                ++ "$\\rbrace$"
    TypeVariant taus      ->  "$\\langle$"
                                ++ intercalate "," (zipWith (\ i tau' -> "$<$" ++ show i ++ "$>$" ++ ": " ++ latexShow tau')
                                                            ([0..] :: [Integer]) taus)
                                ++ "$\\rangle$"
    TypeVar xi            ->  xi
    -- TypeMu 0 [xi] [tau]   ->  "$\\mu$(" ++ xi ++ "." ++ latexShow tau ++ ")"
    -- TypeMu i xis taus     ->  "$\\mu_{" ++ show i ++ "}$(" ++ intercalate "," xis ++ ").("
                                -- ++ intercalate "," (map latexShow taus) ++ ")"
    _ -> error "Tex not implemented"

-- instance Eq Type where
--   tau1 == tau2 = typeEq [] tau1 tau2

-- typeEq :: [(S.TypeVar, S.TypeVar)] -> Type -> Type -> Bool
-- typeEq = undefined

-- ftv :: Type -> [S.TypeVar]
-- ftv = undefined

pickfresh :: String -> [String] -> String
pickfresh v avoidlist
  | v `elem` avoidlist  =  pickfresh (v++"'") avoidlist
  | otherwise           =  v

-- typeSubst :: [S.TypeVar] -> [Type] -> Type -> Type
-- typeSubst = undefined

typeExpand :: Type -> Type
typeExpand = undefined

-- instance Ord Type where
--   a <= b = a == b || show a < show b

data Term  =
              -- lambda-calculus forms
              Var         Int
           |  Abs         Type Term
           |  App         Term Term
              -- extensions (lazy conditional; general recursion; and let-binding)
           |  If          Term Term Term
           |  Fix         Term
           |  Let         Term Term
              -- constants
           |  Const       Const
              -- primitive operator applications
           |  PrimApp     PrimOp [Term]
              -- data structures
           |  Record      [Term]
           |  Project     Term Int Int
           |  Tag         Int Term Type
           |  Case        Term Type [(Int,Term)]
           |  Fold        Type Term
           |  Unfold      Type Term

instance Show Term where
  show t = case t of
    Var n            ->  "_" ++ show n ++ "_"
    Abs tau t        ->  "abs(:" ++ show tau ++ "." ++ show t ++ ")"
    App t1 t2        ->  "app(" ++ show t1  ++ "," ++ show t2 ++ ")"
    If t1 t2 t3      ->  "if " ++ show t1 ++ " then " ++ show t2 ++ " else " ++ show t3 ++ " fi"
    Fix t1           ->  "fix(" ++ show t1 ++ ")"
    Let t1 t2        ->  "let " ++ show t1 ++ " in " ++ show t2 ++ " end"
    Const c          ->  show c
    PrimApp p ts     ->  show p ++ "(" ++ intercalate "," (map show ts) ++ ")"
    Record ts        ->  "record("
                           ++ intercalate "," (map (\(i,t) -> "<" ++ show i ++ ">" ++ "=" ++ show t) (zip [0..] ts))
                           ++ ")"
    Project t1 i k    ->  "project(" ++ show t1 ++ "." ++ "<" ++ show i ++ ">" ++ ")"
    Tag i t1 tau     ->  "tag(#" ++ show i ++ "=" ++ show t1 ++ " as " ++ show tau ++ ")"
    Case t1 tau its      ->  "case " ++ show t1 ++ " of "
                         ++ intercalate " || " (map (\(i,t) -> "<" ++ show i ++ ">" ++ "=>" ++ show t) its)
                         ++ " esac"
    Fold tau t1      ->  "fold(" ++ show tau ++ "," ++ show t1 ++ ")"
    Unfold tau t1    ->  "unfold(" ++ show tau ++ "," ++ show t1 ++ ")"

instance LatexShow Term where
  latexShow t = case t of
    Var n           ->  "\\underline{" ++ show n ++ "}"
    Abs tau t1       ->  "$\\lambda$: " ++ latexShow tau
                         ++ ". " ++ latexShow t1
    App t1 t2       ->  "$\\blacktriangleright$ (" ++ latexShow t1  ++ ", " ++ latexShow t2 ++ ")"
    If t1 t2 t3     ->  "if " ++ latexShow t1 ++ " then " ++ latexShow t2
                         ++ " else " ++ latexShow t3 ++ " fi"
    Fix t1          ->  "fix (" ++ latexShow t1 ++ ")"
    Let t1 t2       ->  "let " ++ latexShow t1 ++ " in " ++ latexShow t2 ++ " end"
    Const c         ->  latexShow c
    PrimApp p ts    ->  latexShow p ++ " (" ++ intercalate ", " (map latexShow ts) ++ ")"
    Record  ts      ->  "$\\lbrace$"
                          ++ intercalate ", " (map  (\(i,t') -> "$<$" ++ show i ++ "$>$" ++ " $=$ " ++ latexShow t')
                                                    (zip ([0..] :: [Integer]) ts))
                          ++ "$\\rbrace$"
    Project t1 i _   ->  latexShow t1 ++ "." ++ "$<$" ++ show i ++ "$>$"
    Tag i t1 tau    ->  "$\\langle$" ++ show i ++ " $=$ " ++ latexShow t1 ++ "$\\rangle$ as " ++ latexShow tau
    Case t1 _ its     ->  "case " ++ latexShow t1 ++ " of "
                        ++ intercalate " $\\talloblong$ " (map  (\(i,t') ->  "$<$" ++ show i ++ "$>$"
                                                                            ++ "$\\Rightarrow$" ++ latexShow t')
                                                                its)
                        ++ " esac"
    Fold tau t1     ->  "fold [" ++ latexShow tau ++ "] " ++ latexShow t1
    Unfold tau t1   ->  "unfold [" ++ latexShow tau ++ "] " ++ latexShow t1

toDeBruijnType :: S.Type -> Type
toDeBruijnType tau =
  case tau of
    S.TypeArrow tau1 tau2   ->  TypeArrow (toDeBruijnType tau1) (toDeBruijnType tau2)
    S.TypeBool              ->  TypeBool
    S.TypeInt               ->  TypeInt
    S.TypeChar              ->  TypeChar
    S.TypeUnit              ->  TypeUnit
    S.TypeRecord ltaus      ->  TypeRecord (map toDeBruijnType (map snd (sortBy (compare `on` fst) ltaus)))
    S.TypeVariant ltaus     ->  TypeVariant (map toDeBruijnType (map snd (sortBy (compare `on` fst) ltaus)))
    S.TypeVar xi            ->  TypeVar xi
    S.TypeMu chi tau1     ->  TypeMu chi (toDeBruijnType tau1)
    S.TypeError _ -> undefined

toDeBruijn :: S.Term -> Term
toDeBruijn tStart = f [] T.Empty tStart
  where
    f :: [S.Var] -> T.Context -> S.Term -> Term
    f bvs capGamma t = case t of
      S.Var x         ->  Var (fromJust (elemIndex x bvs))
      S.Abs x tau t1   ->  Abs (toDeBruijnType tau) (f (x:bvs) (T.Bind capGamma (x, tau)) t1)
      S.App t1 t2     ->  App (f bvs capGamma t1) (f bvs capGamma t2)
      S.PrimApp op ts -> PrimApp op (map (f bvs capGamma) ts)
      S.If t1 t2 t3         -> If (f bvs capGamma t1) (f bvs capGamma t2) (f bvs capGamma t3)
      S.Fix t1        -> Fix (f bvs capGamma t1)
      S.Let x t1 t2        -> Let (f bvs capGamma t1) (f (x:bvs) (T.Bind capGamma (x, tau1)) t2)
        where tau1 = fromRight (error "type error") $ T.typing capGamma t2
      S.Const c        -> Const c
      S.Record lts         -> Record (map (f bvs capGamma . snd) lts)
      S.Project t1 l        -> Project (f bvs capGamma t1) (fromJust $ elemIndex l (map fst ltaus')) (length ltaus')
        where
          ltaus' = case T.typing capGamma t1 of Right (S.TypeRecord ltaus) -> ltaus; _ -> error "type error"
      S.Tag l t1 tau1        -> Tag i (f bvs capGamma t1) (toDeBruijnType tau1)
        where i = case tau1 of S.TypeVariant lts -> fromJust $ elemIndex l (map fst lts); _ -> error "type error"
      S.Case t1 lxts         -> Case (f bvs capGamma t1) (toDeBruijnType tau1) its
        where
          (tau1, ltaus) = case T.typing capGamma t1 of (Right tau'@(S.TypeVariant ltaus')) -> (tau', ltaus'); _ -> error "type error"
          ls = map fst ltaus
          caseHelper :: (S.Label, S.Var, S.Term) -> (Int, Term)
          caseHelper (l', x', t') =
            (fromJust $ elemIndex l' ls,
            f (x':bvs) (T.Bind capGamma (x', fromJust $ lookup l' ltaus)) t')
          its = map caseHelper lxts
      S.Fold {}         -> undefined
      S.Unfold {}         -> undefined
      _ -> error $ "cannot convert to DB: " ++ show t

-- typeOfTagInType :: S.Label -> S.Type -> S.Type
-- typeOfTagInType l tau =
--   case tau of
--     S.TypeVariant ltaus -> snd (fromJust (find ((==l).fst) ltaus))

-- indexOfTagInType :: S.Label -> S.Type -> Int
-- indexOfTagInType l tau =
--   case tau of
--     S.TypeVariant ltaus -> fromJust (findIndex (==l) (sort (fst (unzip ltaus))))

-- indexOfRecordLabel :: S.Label -> S.Term -> T.Context -> Int
-- indexOfRecordLabel l t capGamma =
--   case T.typing capGamma t of
--     Right (S.TypeRecord ltaus) -> fromJust (findIndex (==l) (sort (fst (unzip ltaus))))

-- lengthOfRecord :: S.Term -> T.Context -> Int
-- lengthOfRecord t capGamma =
--   case T.typing capGamma t of
--     Right (S.TypeRecord ltaus) -> length ltaus

-- We define this to avoid code duplication in primOpEval (only the Const case is needed).
constFromDeBruijn :: Term -> S.Term
constFromDeBruijn t = case t of
  Const c -> S.Const c
  _       -> S.ErrorTerm $ "cannot convert \"" ++ show t ++ "\"  from DB to a const"

fromValueDeBruijn :: Term -> [String] -> S.Term
fromValueDeBruijn t usedVars = case t of
    Const _    -> constFromDeBruijn t
    -- Abs tau t1   -> S.Abs x tau (fromValueDeBruijn t1 (x:usedVars)) where x = (pickfresh "x" usedVars)
    Record ts  ->  undefined
    Tag _ t1 _ ->  undefined
    Fold _ t1  ->  undefined
    _          -> error $ "cannot conver form DB to regular: " ++ show t

primOpEval :: PrimOp -> [Term] -> Term
primOpEval p ts = toDeBruijn (S.primOpEval p (map constFromDeBruijn ts))


isValue :: Term -> Bool
isValue t = case t of
  Abs _ _    ->  True
  Const _    ->  True
  Record ts  ->  all isValue ts
  Tag _ t1 _ ->  isValue t1
  Fold _ t1  ->  isValue t1
  _          ->  False

-- | See TAPL pa. 79 for details
shift :: Int -> Int -> Term -> Term
shift c d t = case t of
  Var k            -> Var (if k < c then k else k + d)
  Abs tau t1       -> Abs tau (shift (c+1) d t1)
  App t1 t2        -> App (shift c d t1) (shift c d t2)
  If y z w         -> If (shift c d y) (shift c d z ) (shift c d w)
  Const _          -> t
  PrimApp func xs  -> PrimApp func (fmap (shift c d) xs)
  Fix t'           -> Fix (shift c d t') -- no idea if this works !!!!
  Project t1 i1 i2 -> Project (shift c d t1) i1 i2
  Case t1 tau1 its -> Case (shift c d t1) tau1 (second (shift (c+1) d) <$> its)
  Record ts        -> Record $ map (shift c d) ts
  Tag i1 t1 tau1   -> Tag i1 (shift c d t1) tau1
  -- let t1 in t2 == (.t2) t1
  Let t1 t2        -> Let (shift c d t1) (shift (c+1) d t2)
  Unfold tau t1    -> Unfold tau (shift c d t1)
  Fold tau t1      -> Fold tau (shift c d t1)
  -- _ -> ErrorTerm "Not a valid term in 'subst'"
--   _                -> error $ "not in DB shift: " ++ show t

(↑) :: Int -> Int -> Term -> Term
(↑) = shift


(|->) :: Int -> Term -> Term -> Term
(|->) = subst


subst :: Int -> Term -> Term -> Term
subst j s t = case t of
  Var k            -> if k == j then s else Var k
  Abs tau t1       -> Abs tau (((j+1) |-> (0 ↑ 1) s) t1)
  App t1 t2        -> App ((j |-> s) t1) ((j |-> s) t2)
  If y z w         -> If (subst j s y) (subst j s z ) (subst j s w)
  Const _          -> t
  PrimApp func xs  -> PrimApp func (fmap (subst j s) xs)
  Fix t'           -> Fix (subst j s t') -- no idea if this works !!!!
  Project t1 i1 i2 -> Project (subst j s t1) i1 i2
  Case t1 tau1 its -> Case ((j |-> s) t1) tau1 (second ((j+1) |-> shift 1 1 s) <$> its)
  Record ts        -> Record $ map (subst j s) ts
  Tag i1 t1 tau1   -> Tag i1 (subst j s t1) tau1
  -- let t1 in t2 == (.t2) t1
  Let t1 t2        -> Let (subst j s t1) (subst (j+1) (shift 0 1 s) t2)
  Unfold tau t1    -> Unfold tau (subst j s t1)
  Fold tau t1      -> Fold tau (subst j s t1)
--   _                -> error $ "not in DB subst: " ++ show t

