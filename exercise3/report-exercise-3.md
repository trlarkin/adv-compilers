Advanced Compiler Construction (CS 491): Exercise 3
===================================================

Tristan & Andrew
Work Distribution:

Tristan - Reduction Semantics / CC Machine / De Bruijn

Andrew - Recursive Types / Debugging Evaluation

Running it
----------
To get the executable run `cabal install` while in the directory, and that should put an executable in your `~/.cabal/bin` directory. Otherwise use `cabal repl` and use the function `ghci> parseFile "filepath"`. The command `cabal run test` will run many of the tests. 

Assignment Additions
--------------------

In this assignment, we added reduction semantics, the CC machine, de Bruijn notation, and recursive types.

Completion Matrix
-----------------
| | Parsing | Typing | CBV | DB | RedSem | CC | 
|-|---------|--------|-----|----|--------|----|
| Abs, App, Var    |✅|✅|✅|✅|✅|✅|
| Const & PrimOp   |✅|✅|✅|✅|✅|✅|
| Bool             |✅|✅|✅|✅|✅|✅|
| Char             |✅|✅|✅|✅|✅|✅|
| Unit             |✅|✅|✅|✅|✅|✅|
| Record           |✅|✅|✅|✅|✅|✅|
| Variant          |✅|✅|✅|✅|✅|✅|
| Rec Type         |✅|✅|✅|🟥|🟥|🟥|
| Mut Rec types    |✅|✅|✅|🟥|🟥|🟥|
| If               |✅|✅|✅|✅|✅|✅|
| Fix              |✅|✅|✅|✅|✅|✅|
| Let              |✅|✅|✅|✅|✅|✅|


Reduction Semantics
-------------------
The reduction semantics first required making the EvaluationContext, which follows from the in class examples. We instanced it into `Show` for debugging purposes, but I also wanted to use more unicode. The Reduction Semantics evaluator has three actions:

- `makeEvalContext`: this finds the next action to take in the term given, and remembers where that term goes in a context.
- `makeContractum`: this acts on a term and takes a small step on it.
- `fillWithTerm`: this puts a term back into a context where ther hole is.

Looping over these three steps until we have a value is equivalent to the small step semantics we have defined. It really just splits of the searching and evaluating sections.  

The `show` function proved very helpful for some debugging
```haskell
instance Show Context where
    show e = case e of
        Hole         -> "□"
        AppT e t2    -> "app(" ++ show e ++ ", " 
                            ++ show t2 ++ ")"
        ...
```
Everything else was very straight forward.

CC Machine
----------
This uses the Evauation Contexts and `makeEvalContext` from Reduction Semantics. The CC machine repeatedly makes `ccMachineStep` calls which each takes an action to get us closer to the solution. This works by continuously making small step changes and putting where that item goes into a context until it reaches a point where it has some value and a context. Then it finds the next point in that context to take a small step on. We implement this by reusing the `makeEvalContext` funciton, since it finds the next location that needs to be evaluated. 

The CC machine has a state that is 
```haskell
data MachineState = (Term, Context)
```
and the function that runs it is:
```haskell
ccMachineLoop :: MachineState -> Maybe MachineState
```
We avoided rewriting the logic in `shift` by using the `makeEvalContext` function
```haskell
shift :: S.Term -> E.Context -> Maybe MachineState
shift _ E.Hole = Nothing
shift v' e'    = RS.makeEvalContext $ e' `E.fillWithTerm` v'
```


DeBruijn
--------
Implementing DeBruijn CBV requires a new set of Term data types, a new `|->` implementation, and shift function now that we do not have named variables. Instead of writing a new parser we use the same parser and add a function that converts from a regular term to a DeBruijn term. 

The most novel part of DeBruijn is the `shift function
```haskell
-- | See TAPL pg. 79 for details
shift :: Int -> Int -> Term -> Term
shift c d t = case t of
    Var k       -> Var (if k < c then k else k + d)
    Abs tau t1  -> Abs tau (shift (c+1) d t1)
    App t1 t2   -> App (shift c d t1) (shift c d t2)
    ...
```
When writing the evalutator for the DeBruijn terms it was almost identical to the standard CBV. Instead of substituting a variable or grabbing a value with a label we instead shift by a number and index into things:
```haskell
S.Project t1@(S.Record labelsAndTerms) l1
    | isValue t1 -> lookupOrElse l1 labelsAndTerms "not in record"
-- becomes
S.Project t1@(S.Record ts) i1 _
    | isValue t1 -> return $ ts!!i1

```
When performing applications we have to be careful. We need to shift indecies inside `v2` up, then replace all isntances of zero with the shifted v2, and finally shift all the values back down afterwards. 
```haskell
-- pg 103: E-AppAbs
S.App (S.Abs _ t12) v2
    | S.isValue v2 -> return 
        (S.shift 0 (-1) ((0 |-> S.shift 0 1 v2) t12))

{- OR LIKE THE OTHER TEAM -}

apply :: S.Term -> S.Term -> S.Term
apply tBody v2 = S.shift 0 (-1) ((0 |-> S.shift 0 1 v2) tBody)
-- then just use apply
```

I also added a unicode alias to `shift` but its not used right now
```haskell
(↑) = shift
```

Sections
--------
Tristan: Reduction Semantics, DeBruijn, CCMachine  
Andrew: ... Furthermore, we added a more in-depth debugging evaluation mechanism, which is akin to a "proof" of evaluation results.

### Recursive Types

Recursive types are introduced using the mu operator, and are interacted with using the fold/unfold syntax. The trouble we were running into when presenting was not actually due to any faults in our implementation, but rather we had an incorrect handling of substitution within record/variant types. In the typing world, we added two new types:

```Haskell
TypeVar TypeVar
TypeMu TypeVar Type
```

Furthermore, in the term world, we add two new terms:

```Haskell
Fold Type Term
Unfold Type Term
```

According to TAPL, we need to add two new typing rules to our core language:

```Haskell
S.Fold u t1 -- pg 276: T-Fld
   | S.TypeMu chi tau1 <- u -> enforceType t1 ((chi |-> u) tau1) gamma >> return u
   | otherwise -> Left $ "folding without mu operator in " ++ show t
S.Unfold u t1 -- pg 276: T-Unfld
   | S.TypeMu chi tau1 <- u -> enforceType t1 u gamma >> return ((chi |-> u) tau1)
   | otherwise -> Left $ "folding without a mu operator in " ++ show t
```

To do this, we needed to add a new "substT" function to be able to substitute into types. We added a new typeclass called "Substitutable" so we could reuse the arrow syntax.

Then, we also needed new evaluation rules, added as follows:

```Haskell
-- pg 276 E-Fld
    S.Fold tau1 t1 
        | S.isNotValue t1 -> do t1' <- eval_small t1; return $ S.Fold tau1 t1'
        | otherwise       -> return t
-- pg 276 E-UnfldFld
    S.Unfold tau1 (S.Fold tau2 t1)
        | S.isValue t1 -> return t1
        | otherwise    -> do t1' <- eval_small t1; return $ S.Unfold tau1 (S.Fold tau2 t1')
-- pg 276 E-Unfld
    S.Unfold tau1 t1
        | S.isNotValue t1 -> do t1' <- eval_small t1; return $ S.Unfold tau1 t1'
```

Note, we have only implemented recursive types for operational semantics so far, but their extensions to other evaluation schemas (exluded De Bruijn) is straightforward.

### Debugging Evaluation
To add debugging evaluation, we added a new evaluation stategy which adds in calls to trace to print every step of evaluation. Although the way we output it is informal, this trace is equivalent to a proof of evaluation. If we were to use a state monad to thread these steps through, we could easily print this more prettily. To avoid our code being convoluted, we used the traceM function to be able to incorporate tracing with our do syntax. As an example of a few lines from this new evaluation strategy:

```Haskell
S.App t1@(S.Abs x _ t12) v2 
   | S.isValue v2 -> do traceM ("Substituting Value Into App" ++ "\n" ++ (show t) ++ "\n\n\n") 
                        return ((x |-> v2) t12)
S.App v1 t2 
   | S.isValue v1 -> do traceM ("Evaluating Second Argument of Application" ++ "\n" ++ (show t) ++ "\n\n\n")
                        t2' <- eval_small_trace t2 
                        return (S.App v1 t2')
S.App t1 t2 ->       do traceM ("Evaluating First Argument of Application" ++ "\n" ++ (show t) ++ "\n\n\n")
                        t1' <-  eval_small_trace t1
                        return (S.App t1' t2)
```
