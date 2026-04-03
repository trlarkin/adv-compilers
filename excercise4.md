Exercise 4
==========

Andrew: CEK Machine, Tracing

Tristan: CK Machine, Natural Semantics

Overview
--------
This project was the implementation of Natural Semantics (normal, environments, DeBruijn), CK Machine, and CEK Machine. We only implement `functions`, `application`, `constants`, `if-then-else`, `let`, and `fix`.

Running it
----------
If you compile the code (in `app\main.hs`) and pass the filename for a corelambda source file. You can run the same function in ghci with `mainCompiler`. The output will look like:
```bash
ghci> mainCompiler "corelambda_files/sumn100.corelambda" 
app(fix(abs(f: ->(Int,Int). abs(x: Int. 
if IntEq(0, x) then 0 
else IntAdd(x, app(f, IntSub(x, 1))) fi))), 100)
Free Variables:[]
Type:Int
Call-by-value evaluation: 
        5050
Natural CBV: 
        5050
Natural CBV Closures: 
        5050
Natural CBV Closures & DB: 
        5050
BeBruijn evaluation: 
        5050
Standard Reduction evaluation: 
        5050
CC Machine evaluation: 
        5050
CK Machine evaluation: 
        5050
CEK Machine evaluation: 
        "not working :("
```

Natural Semantics
-----------------
Natural (or Big-Step) semantics takes larger steps than the small step rules we have been using, [defined here](https://www.cs.tufts.edu/~nr/cs257/archive/gilles-kahn/natural-semantics.pdf). The general constraint here is that everything should be done with one pattern match. For example:

```haskell
-- in small step cbv we would do:
...
S.If (S.Const S.Tru) t2 _   ->  ...
S.If (S.Const S.Fls) _ t3   ->  ...
S.If t1 t2 t3               ->  ...

-- while in big step we do:
S.If t1 t2 t3 -> do
        S.Const b <- eval t1
        if b == S.Tru
                then eval t2
                else eval t3
```
Having this constraint leads to natural semantics. There is really nothing else special here.


Natural Semantics with Environments and Closures
------------------------------------------------
We introduce a few new things:

1. Environment: An environment is a map of variables to values. Instead of substituting (x `|->` t) we hold all the variables in a mapping so that when we need them they are available. 
2. Closures: Closures are a term that needs to be evaluated in a certain environment.

With these we can perform out big steps without any substitution. In fact, we used that as our condition for being correct: no `|->` allowed.
```haskell
-- big step without closures
S.Let x t1 t2   -> do
        v1' <- evalInEnv e t1
        eval ((x |-> v1') t2)

-- big step with closures
S.Let x t1 t2   -> do
        v1' <- evalInEnv e t1
        evalInEnv ((x,v1'):e) t2
```
 By far the most challenging part of this was fix, which has a very simple implementation with substitution, but a far less obvious one (at least for me) with environments. Our solution is:
 ```haskell
S.Fix t1 -> do
        Clo (S.Abs f _ tBody) e' <- evalInEnv e t1
        let eRec = (f, Clo tBody [eRec])
        evalInEnv (eRec:e') tBody
```
This solution relies on Haskell's laziness. We create a closure for the body of the fixed function, which can contain reference to the variable `f`. Since Haskell is lazy it only tries to grab the value of `f` when needed, and if fix is going to terminate it will stop asking for `f` eventually. In a strict language it would attempt to make all of `eRec` right away and spin forever. 


Natural Semantics with Env, Clo, and DB Indices
-----------------------------------------------
This is the same as the last one but we use DeBruijn form. In this case we don't need to worry about keeping track of the names of the variables, since all variables are thrown onto the environment and the `i`th DB index is the `i`th from the top.  If we want to continue the theme of listing the constraints we are given:

1. One pattern match per constructor of term
2. No shifting with `|->`
3. Use DB indices (this one is not a concern since the type signature of the function requires we use DB)

```haskell
S.Var i ->  Just (e!!i) -- variables are very easy

S.App t1 t2  ->  do  -- without shifting DB is very smooth
        Clo (S.Abs _ t') e' <- evalInEnv e t1
        v' <- evalInEnv e t2
        evalInEnv (v':e') t'

S.Fix t1 -> do  -- fix was not much different from last section
        Clo (S.Abs _ tBody) e' <- evalInEnv e t1
        let eRec = (Clo tBody [eRec])
        evalInEnv (eRec:e') tBody
```
Overall this was very simple. The use of DB indices with environments is very clean, since we are putting the variable values on a stack then the `i`the most recent variable declared becomes trivial. Once again we did not figure out fix, which could be the interesting case. 

*I want to make sure that the DeBruijn version of my code checks out. In the small step implementation of DB we needed to do some shifting around of indices:*
```haskell
t :: Term
v :: Term -- value
shift 0 (-1) ((0 |-> (shift 0 1 v)) t)
```
*when we did shifting. This does not appear in the environment version. My understanding is that this no longer matters because now we are using closures to keep the correct frame of reference for the indices.* 
***Is this correct?***

CK Machine
----------
The CK machine is also quite simple. It basically just performs small step operational semantics, but the steps make the staging very explicit. The results is essentially two types of actions: staging or evaluating. This can also be seen as putting things into the continuation or taking them out of it. Other than the given ck options from the book, we have:
```haskell
(S.If t1 t2 t3, kappa) 
    -> return (t1, KIf t2 t3 kappa) -- ck make if
(S.Const b, KIf t2 t3 kappa) -- ck eval if
    | S.Tru <- b -> return (t2, kappa)
    | S.Fls <- b -> return (t3, kappa)

(S.Fix t1, kappa) 
    -> return (t1, KFix kappa) -- ck make fix
(v@(S.Abs x _ m), KFix kappa) 
    -> return ((x |-> S.Fix v) m, kappa) -- ck eval fix

(S.Let x t1 t2, kappa) 
    -> return (t1, KLet x t2 kappa) -- ck make let
(v, KLet x t2 kappa) 
    | S.isValue v -> return ((x |-> v) t2, kappa) -- ck eval let
```
There was really nothing particularly difficult here.


CEK Machine
-----------
...
