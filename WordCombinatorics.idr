--   Inspired by A second course in formal languages and automata by Shallit.

module WordCombinatorics

import DecHelper

Word : Type
Word = String

%default total


intDivCeil2 : Nat -> Nat
intDivCeil2 k = (div k 2) + (mod k 2)


prefixLengthRange : Word -> List Nat
prefixLengthRange w = [0..(intDivCeil2 (length w))]


--TODONOTE TODO this is a handy utility function for the string library
prefixesOf : Word -> List Word
prefixesOf w with (unpack w)
  | [] = []
  | xs = let segs = inits xs in
             map pack segs


primitivePrefixCandidatesOf : Word -> List Word
primitivePrefixCandidatesOf w = let prefixes = prefixesOf w in
                                    filter (\x => (length x > 0) && (length x <= intDivCeil2 (length w)) && (mod (length w) (length x) == 0 ) ) prefixes 

primitivePrefixCandidateLengthPairsOf : Word -> List (Word, Nat)
primitivePrefixCandidateLengthPairsOf w = let prefixes = primitivePrefixCandidatesOf w in
                                              map (\x => (x, div (length w) (length x))) prefixes 


wordMult : Word -> Nat -> Word
wordMult x Z = "" 
wordMult x (S k) = x ++ (wordMult x k)

computeCandidates : List (Word, Nat) -> List (Word)
computeCandidates xs = map (\(w,n) => wordMult w n) xs


prefixPowerOf : Word -> (Word, Nat)
prefixPowerOf x = let candidatePairs = primitivePrefixCandidateLengthPairsOf x 
                      validCandidates = filter (\(w,n) => (wordMult w n) == x) candidatePairs in
                      case validCandidates of
                           []               => (x, 1)
                           (apair :: pairs) => apair

isPrimitive : Word -> Bool
isPrimitive w = let (p,n) = prefixPowerOf w in
                    p == w

isPower : Word -> Bool
isPower w = not (isPrimitive w)

isPrimitiveP1 : isPrimitive "dodo" = False
isPrimitiveP1 = Refl 


isPrimitiveP2 : isPrimitive "door" = True
isPrimitiveP2 = Refl

--TODONOTE could make a circular shift dat structures

cyclicShift : List a -> List a
cyclicShift [] = [] 
cyclicShift (x :: xs) = xs ++ [x]

cyclicShiftWord : Word -> Word
cyclicShiftWord w = pack . cyclicShift $ unpack w 

--TODONOTE TODO iterateN is a handy utility function
iterateN : Nat -> (f : a -> a) -> (x : a) -> List a
iterateN Z     f x = [] 
iterateN (S n) f x = x :: iterateN n f (f x)
-- TODO This is not specific to words, could be List a -> List (List a) based on length l
allCyclicShiftsOf : Word -> List Word
allCyclicShiftsOf w = iterateN (length w) cyclicShiftWord w

isConjugateOf : Word -> Word -> Bool
isConjugateOf w1 w2 = any (== w2) (allCyclicShiftsOf w1) 

isConjugateOfP1 : isConjugateOf "listen" "enlist" = True
isConjugateOfP1 = Refl 




isPrimitiveT : Word -> Type
isPrimitiveT x = isPrimitive x = True


isPrimitiveDec : (w : Word) -> Dec (isPrimitiveT w)
isPrimitiveDec w with (isPrimitive w)
  | True  = Yes Refl
  | False = No falseNotTrue

isPowerT : Word -> Type
isPowerT x = isPower x = True


isPowerDec : (w : Word) -> Dec (isPowerT w)
isPowerDec w with (isPower w)
  | True  = Yes Refl
  | False = No falseNotTrue


isConjugateOfT : Word -> Word -> Type
isConjugateOfT x x1 = isConjugateOf x x1 = True

isConjugateOfDec : (w1 : Word) -> (w2 : Word) -> Dec (isConjugateOfT w1 w2)
isConjugateOfDec w1 w2 with (isConjugateOf w1 w2) 
  | True  = Yes Refl
  | False = No falseNotTrue

-- TODO
-- define Power w -> p:Word n:Nat -> w = p*n 
-- as a constructor, then when we say ispower w we can get p and n
-- likewise define conjugate w x -> w n -> w cyclicshift n = x, use that constructor


nthConjugateOf : Nat -> Word -> Word
nthConjugateOf Z x = x 
nthConjugateOf (S k) x = nthConjugateOf k (cyclicShiftWord x) 

cyclicShiftIsConjugate : (w1 : Word) -> (w2 : Word) -> { auto ok: cyclicShiftWord w1 = w2 } -> isConjugateOfT w1 w2
cyclicShiftIsConjugate w1 w2 = ?cyclicShiftIsConjugate_pf

data Power : Word -> Word -> Nat -> Type where
  MkPower : (w : Word) -> (p : Word) -> (n : Nat) -> { auto ok: wordMult p n = w } -> Power w p n


data Conjugate : Word -> Word -> Nat -> Type where
  MkConjugate : (w : Word) -> (x : Word) -> (n : Nat) -> { auto ok: nthConjugateOf n x = w } -> Conjugate w x n


--splitConjugate : (Conjugate w x n) -> ((u : Word, v : Word) ** ((w = u ++ v), (x = v ++ u)))
splitConjugate : (Conjugate w x n) -> {u : Word} -> {v : Word} -> ((Word, Word) , ((w = u ++ v), (x = v ++ u)))
splitConjugate (MkConjugate w x n ) = ?splitConjugateProof
                 
                 --((u : Word, v : Word) ** ((w = u ++ v), (x = v ++ u)))


-- This is what it would look like with primitives, can't use any of the properties usefully
--theorem2_4_2 : (w : Word) -> (x : Word) -> (isConjugateOfT w x) -> (isPowerT w) -> isPowerT x
--theorem2_4_2 w x isConj isPow = ?theorem2_4_2_rhs
-- This is what it looks like if you use too many types
-- theorem2_4_2DT : (w : Word) -> (x : Word) -> (Conjugate w x n) -> (Power w pw kw) -> (Power x px kx)  
theorem2_4_2DT : (w : Word) -> (x : Word) -> (Conjugate w x n) -> (Power w pw kw) -> wordMult px kx = x
theorem2_4_2DT w x (MkConjugate w x n) (MkPower w pw kw) = ?thm242Proof


