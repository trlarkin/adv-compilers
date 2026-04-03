Advance Compilers
=================
A class that explores the beauty of functional compilers. All implemented in Haskell with Parsec.

Topics
------
- Lambda Calculus as a programming language
- Small step and big step semantics
- Simply Typed Languages
- Recursive functions and types
- De Bruijn variables
- (Not implemented) Continuation Passing Style

Example Program
---------------
app(fix (abs (f:->(Int,Int). abs (x: Int. if =(0,x) then 1 else *(x, app(f, -(x,1))) fi))), 5)
