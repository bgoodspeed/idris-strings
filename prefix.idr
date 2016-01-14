module Prefix

infixr 8 #
data Word t = Empty | (#) t (Word t)

wordLength : Word t -> Nat
wordLength Empty = Z 
wordLength (x # y) = S (wordLength y) 


infixr 2 ##
(##) : Word t -> Word t -> Word t
(##) Empty w    = w
(##) (c # w) w2 = c # (w ## w2)

--concatLengthIsCombined : (w : Word t) -> (w2 : Word t) -> wordLength (w ## w2) = (wordLength w) + (wordLength w2)
--concatLengthIsCombined w w2 = ?concatLengthIsCombined_rhs


aEmptyIsA : (a : List Char) -> [] ++ a = a
aEmptyIsA a = Refl

emptyAisA : (a : List Char) -> a ++ [] = a
emptyAisA a = ?emptyAisA_rhs

lengthOfConcatIsSucc : (a : List Char) -> (c : Char) -> length (c :: a) = S (length a) 
lengthOfConcatIsSucc a c = ?lengthOfConcatIsSucc_rhs


lengthConcatAppend : (a : List Char) -> (c : Char) -> (cs : List Char) -> length (a ++ c :: cs) = S( length (cs ++ a))
lengthConcatAppend a c cs = ?lengthOfConcatAppendPf

concatLetterDoesNotMatter : (as : List Char) -> (a : Char) -> (b : Char) -> length (a :: as) = length (b :: as)
concatLetterDoesNotMatter as a b = ?concatLetterDoesNotMatter_rhs

concatMiddleDoesNotMatter : (as : List Char) -> (bs : List Char) -> (a : Char) -> (b : Char) -> length (as ++ a :: bs) = length (bs ++ b :: as)
concatMiddleDoesNotMatter as bs a b = ?concatMiddleDoesNotMatter_rhs

{-
lenghtSym : (a : List Char) -> (b : List Char) -> length (a ++ b) = length (b ++ a)
lenghtSym a [] = ?lenghtSym_rhs_BASE
lenghtSym a (x :: xs) = ?lenghtSym_IND
-}

--lenghtSym : (a : List Char) -> (b : List Char) -> length (a ++ b) = length (b ++ a)
--lenghtSym a b = ?lenghtSym_rhs

lenghtSym2 : (a : List Char) -> (b : List Char) -> length (a ++ b) = length (b ++ a)
lenghtSym2 [] b = ?lenghtSym_rhs_3
lenghtSym2 (x :: xs) [] = ?lenghtSym_rhs_2
lenghtSym2 (x :: xs) (y :: ys) = ?lenghtSym_rhs_4


plusXZeroIsX : (n : Nat) -> n = plus n 0
plusXZeroIsX Z = Refl
plusXZeroIsX (S k) = let rec = plusXZeroIsX {n=k} in
                         ?plusXZeroStepCase


plusplusLength : (a : List Char) -> (b : List Char) -> (length (a ++ b)) = (length a) + (length b)
plusplusLength a b = ?plusplusLength_rhs
{-
plusplusLength [] b = Refl
plusplusLength (x :: xs) [] = ?plusplusLength_rhs1_2
plusplusLength (x :: xs) (y :: ys) = ?plusplusLength_rhs1_3
-}
---------- Proofs ----------

Prefix.plusXZeroStepCase = proof
  intros
  rewrite rec
  trivial


Prefix.concatLetterDoesNotMatter_rhs = proof
  intros
  trivial


Prefix.lengthOfConcatIsSucc_rhs = proof
  intros
  induction a
  trivial
  intros
  trivial


Prefix.lenghtSym_rhs_2 = proof
  intros
  rewrite emptyAisA {a = xs}
  trivial


Prefix.lenghtSym_rhs_3 = proof
  intros
  rewrite emptyAisA {a = b}
  trivial


Prefix.emptyAisA_rhs = proof
  intros
  compute
  induction a
  trivial
  intros
  compute
  rewrite ihl__0
  trivial


