Exercise 5
==========

Andrew: Danvy Filinski

Tristan: Fischer Plotkin


Fischer Plotkin
--------------
If you `import Public` and use `cpsFischerPlotkin :: S.Term -> S.Term` it will convert a standard term into the CPS version without any optimization. The working parts are:
- `Abs`
- `App`
- `PrimApp`
- `Var`
- `Const`
- `Let`
- `If` (lazy)

But the `fix` operator does not work.

We determined that for the $\kappa$ variable that all CPS transformation steps use does not need to be unique and so we just use the letter "k" and we have `k` defined as the string "k" and `tk` defined as the variable term of "k" to use anywhere. There are a few other variables we need which we use "v1," "v2," or "v3" for the other ones. There were two interesting ones to me: `let` and `primApp`. Debugging this was a mess since it produces such long terms.

### Let
The code for `Let` is
```haskell
S.Let x t1 t2 -> S.Abs k tau 
    (S.App t1CPS (S.Abs v1 tau 
        (S.App (S.Let x tv1 t2CPS) tk)))
```
I am not 100% sure this is correct, but it does produce the correct answer. 

### PrimApp
The code for `PrimApp` is
```haskell
S.PrimApp op ts -> S.Abs k answerT $ foldl' makeOpCPS final (reverse $ zip xNames tsCPS)
  where
    xNames = [replicate i '#' | i <- [1..length ts]] -- make var names
    xs = S.Var <$> xNames                            -- make terms
    tsCPS = toCPS_FischerPlotkin tau <$> ts          -- make all original terms CPS
    final = S.App tk (S.PrimApp op xs)               -- create the base for fold
    makeOpCPS :: S.Term -> (S.Var, S.Term) -> S.Term -- the function to fold over
    makeOpCPS t0 (x, tApp) = S.App tApp (S.Abs x tau t0)
```
This is the generalized prim app for any arity operator. 

DanvyFilinski_HigherOrder
-------------------------
...
