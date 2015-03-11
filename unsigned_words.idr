module UnsignedWords

%default total

Str : Type
Str = List Char

strLength : Str -> Nat
strLength [] = Z 
strLength (x :: xs) = S( strLength xs ) 

listAppendIsAssociative : (l : List Char) -> (c : List Char) -> (r : List Char) -> (l ++ (c ++ r)) = ((l ++ c) ++ r)
listAppendIsAssociative [] c r = Refl
listAppendIsAssociative (x :: xs) c r = let inductiveHypothesis = listAppendIsAssociative xs c r in
                                            ?listAppendIsAssociativeStepCase

-- list a already gives us Eq, Semigroup, Monoid
instance VerifiedSemigroup Str where
  semigroupOpIsAssociative = listAppendIsAssociative 


listAppendNeutralIsNeutralL : (l : List Char) -> (l ++ []) = l
listAppendNeutralIsNeutralL [] = Refl
listAppendNeutralIsNeutralL (x :: xs) = let inductiveHypothesis = listAppendNeutralIsNeutralL xs in
                                            ?listAppendNeutralIsNeutralLStepCase

listAppendNeutralIsNeutralR : (r : List Char) -> [] ++ r = r
listAppendNeutralIsNeutralR [] = Refl
listAppendNeutralIsNeutralR (x :: xs) = let inductiveHypothesis = listAppendNeutralIsNeutralR xs in
                                            ?listAppendNeutralIsNeutralRStepCase

instance VerifiedMonoid Str where
  monoidNeutralIsNeutralL = listAppendNeutralIsNeutralL
  monoidNeutralIsNeutralR = listAppendNeutralIsNeutralR

--TODO predicates & decision properties



concatIsInvInjective : (c : Char) -> (s1 : Str) -> (s2 : Str) -> (pf : s1 = s2) -> c :: s1 = c :: s2
concatIsInvInjective c s1 s2 pf = ?concatIsInvInjectivePf


concatIsInjective : (c : Char) -> (s1 : Str)  -> (s2 : Str) -> {auto pf : c :: s1 = c :: s2 } -> s1 = s2 
concatIsInjective _ _ _ {pf = Refl} = Refl




{- TODO this doesnt help.
concatIsInjective : (c : Char) -> (s1 : Str)  -> (s2 : Str) -> (pf : c :: s1 = c :: s2) -> s1 = s2 
concatIsInjective c [] (a::b) Refl impossible
concatIsInjective c (a::b) [] Refl impossible
concatIsInjective c [] [] pf = Refl
concatIsInjective c (a::s11) (b::s21) pf = ?concatIsInjectivePf
-}




---------- Proofs ----------

UnsignedWords.concatIsInvInjectivePf = proof
  intros
  rewrite pf
  trivial


UnsignedWords.listAppendNeutralIsNeutralRStepCase = proof
  intros
  trivial


UnsignedWords.listAppendNeutralIsNeutralLStepCase = proof
  intros
  rewrite inductiveHypothesis 
  trivial


UnsignedWords.listAppendIsAssociativeStepCase = proof
  intros
  rewrite inductiveHypothesis 
  trivial


