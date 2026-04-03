-- | Contain error message generators. Add to it when it is easy.
module ErrorMessages where

import           AbstractSyntax

wrongType :: (Term, Type, Type, Term) -> String
wrongType (tGiven, tauGiven, tauExpected, parentTerm) =
    "Expected a '" ++ show tauExpected ++ ",' but given the '"
    ++ show tauGiven ++ "' " ++ show tGiven ++ " in: \"" ++ show parentTerm ++ "\""

notVariantInCase :: (Term, Term) -> String
notVariantInCase (tauNotVariant, parentTerm) =
    "'" ++ show tauNotVariant ++ "' is not a Variant in case statement: \""
    ++ show parentTerm ++ "\""

ifMismatch :: (Term, Type, Term, Type, Term) -> String
ifMismatch (t2, tau2, t3, tau3, parentTerm) =
    "The '" ++ show tau2 ++ "' \""
    ++ show t2 ++ "\" and '" ++ show tau3 ++ "' \""
    ++ show t3 ++ "\" do not have the same type in \""
    ++ show parentTerm ++ "\"."

fixErr :: (Type, Term) -> String
fixErr (tauFixedTerm, parentTerm) =
    "Fix takes a function, not a " ++ show tauFixedTerm ++ " in: " ++ show parentTerm
