module UnsignedVectorWords

import Data.Vect
%default total

Str : Nat -> Type -> Type
Str n t = Vect n t 

strConcat : (Str n t) -> (Str m t)-> (Str (n + m) t)
strConcat x x1 = x ++ x1

{-
strConcatIsAssoc: (l : Str n) -> (c: Str m) -> (r: Str o) -> l `strConcat` (c `strConcat` r) = (l `strConcat` c) `strConcat` r
strConcatIsAssoc [] c r = Refl
strConcatIsAssoc (x :: xs) c r = let inductiveHypothesis = strConcatIsAssoc xs c r in
                                     rewrite inductiveHypothesis in ?strConcatIsAssocStepCase

-}
-- TODO for signed vectors we can't know this at 'compile' time, because:
-- pf, spse n=m, then the type sig says w1::w2 has length 2n
-- but w1^-1 has length n, therefore if w2 = w1^-1 then w1::w2 = Empty
-- and length of empty = 0.




-- TODO interesting, we have to be a little sneaky about types here
--      if we declare the full type to be Vect n Char, then s=ab belongs to G2 but s2=abc belongs to G3
                                                       -- so we don't have closure
--instance Semigroup (Str n) where
--  (<+>) a b = a ++ b

{-
instance VerifiedSemigroup (Str n) where
  semigroupOpIsAssociative = ?listAppendIsAssociative 

instance Monoid (Str n) where


instance VerifiedMonoid (Str n) where
  monoidNeutralIsNeutralL = ?listAppendNeutralIsNeutralL
  monoidNeutralIsNeutralR = ?listAppendNeutralIsNeutralR
  -}
