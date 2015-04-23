--   Inspired by A second course in formal languages and automata by Shallit.

module WordCombinatorics

import DecHelper
infixr 8 #
data Word t = Empty | (#) t (Word t)

infixr 2 ##
(##) : Word t -> Word t -> Word t
(##) Empty w    = w
(##) (c # w) w2 = c # (w ## w2)

instance (Eq t) =>  Eq (Word t) where
    Empty   == Empty   = True
    (a # x) == Empty   = False
    Empty   == (b # y) = False
    (a # x) == (b # y) = (a == b) && (x == y)

%default total


intDivCeil2 : Nat -> Nat
intDivCeil2 k = (div k 2) + (mod k 2)

length : Word t -> Nat
length Empty = Z 
length (x # y) = S (length y) 


prefixLengthRange : Word t -> List Nat
prefixLengthRange w = [0..(intDivCeil2 (length w))]


unpack : Word t -> List t
unpack Empty = [] 
unpack (x # y) = x :: (unpack y)


pack : List t -> Word t
pack [] = Empty 
pack (x :: xs) = x # (pack xs) 


--TODONOTE TODO this is a handy utility function for the string library
prefixesOf : Word t -> List (Word t)
prefixesOf w with (unpack w)
  | [] = []
  | xs = let segs = inits xs in
             map pack segs


primitivePrefixCandidatesOf : Word t -> List (Word t)
primitivePrefixCandidatesOf w = let prefixes = prefixesOf w in
                                    filter (\x => (length x > 0) && (length x <= intDivCeil2 (length w)) && (mod (length w) (length x) == 0 ) ) prefixes 

primitivePrefixCandidateLengthPairsOf : Word t -> List (Word t, Nat)
primitivePrefixCandidateLengthPairsOf w = let prefixes = primitivePrefixCandidatesOf w in
                                              map (\x => (x, div (length w) (length x))) prefixes 


wordMult : Word t -> Nat -> Word t
wordMult x Z = Empty 
wordMult x (S k) = x ## (wordMult x k)

computeCandidates : List (Word t, Nat) -> List (Word t)
computeCandidates xs = map (\(w,n) => wordMult w n) xs


prefixPowerOf : (Eq t) => Word t -> (Word t, Nat)
prefixPowerOf x = let candidatePairs = primitivePrefixCandidateLengthPairsOf x 
                      validCandidates = filter (\(w,n) => (wordMult w n) == x) candidatePairs in
                      case validCandidates of
                           []               => (x, 1)
                           (apair :: pairs) => apair

isPrimitive : (Eq t) => Word t -> Bool
isPrimitive w = let (p,n) = prefixPowerOf w in
                    p == w

isPower : (Eq t) => Word t -> Bool
isPower w = not (isPrimitive w)

--TODONOTE could make a circular shift dat structures

cyclicShift : List a -> List a
cyclicShift [] = [] 
cyclicShift (x :: xs) = xs ++ [x]

cyclicShiftWord : Word t -> Word t
cyclicShiftWord w = pack . cyclicShift $ unpack w 

--TODONOTE TODO iterateN is a handy utility function
iterateN : Nat -> (f : a -> a) -> (x : a) -> List a
iterateN Z     f x = [] 
iterateN (S n) f x = x :: iterateN n f (f x)
-- TODO This is not specific to words, could be List a -> List (List a) based on length l
allCyclicShiftsOf : Word t -> List (Word t)
allCyclicShiftsOf w = iterateN (length w) cyclicShiftWord w

isConjugateOf : (Eq t) => Word t -> Word t -> Bool
isConjugateOf w1 w2 = any (== w2) (allCyclicShiftsOf w1) 




isPrimitiveT : (Eq t) => Word t -> Type
isPrimitiveT x = isPrimitive x = True


isPrimitiveDec : (Eq t) => (w : Word t) -> Dec (isPrimitiveT w)
isPrimitiveDec w with (isPrimitive w)
  | True  = Yes Refl
  | False = No falseNotTrue

isPowerT : (Eq t) => Word t -> Type
isPowerT x = isPower x = True


isPowerDec : (Eq t) => (w : Word t) -> Dec (isPowerT w)
isPowerDec w with (isPower w)
  | True  = Yes Refl
  | False = No falseNotTrue


isConjugateOfT : (Eq t) => Word t -> Word t -> Type
isConjugateOfT x x1 = isConjugateOf x x1 = True

isConjugateOfDec : (Eq t) => (w1 : Word t) -> (w2 : Word t) -> Dec (isConjugateOfT w1 w2)
isConjugateOfDec w1 w2 with (isConjugateOf w1 w2) 
  | True  = Yes Refl
  | False = No falseNotTrue

-- TODO
-- define Power w -> p:Word n:Nat -> w = p*n 
-- as a constructor, then when we say ispower w we can get p and n
-- likewise define conjugate w x -> w n -> w cyclicshift n = x, use that constructor


nthConjugateOf : Nat -> Word t -> Word t
nthConjugateOf Z x = x 
nthConjugateOf (S k) x = nthConjugateOf k (cyclicShiftWord x) 



cyclicShiftIsConjugate : (Eq t) => (w1 : Word t) -> (w2 : Word t) -> { auto ok: cyclicShiftWord w1 = w2 } -> isConjugateOfT w1 w2
cyclicShiftIsConjugate w1 w2 = ?cyclicShiftIsConjugate_pf

data Power : (Eq t) => Word t -> Word t -> Nat -> Type where
  MkPower : (Eq t) => (w : Word t) -> (p : Word t) -> (n : Nat) -> { auto ok: wordMult p n = w } -> Power w p n


data Conjugate : (Eq t) => Word t -> Word t -> Nat -> Type where
  MkConjugate : (Eq t) => (w : Word t) -> (x : Word t) -> (n : Nat) -> { auto ok: nthConjugateOf n x = w } -> Conjugate w x n


--splitConjugate : (Conjugate w x n) -> ((u : Word, v : Word) ** ((w = u ++ v), (x = v ++ u)))
splitConjugate : (Eq t) => (Conjugate w x n) -> {u : Word t} -> {v : Word t} -> ((w = u ## v), (x = v ## u))
splitConjugate (MkConjugate w x n ) = ?splitConjugateProof
                 
                 --((u : Word, v : Word) ** ((w = u ++ v), (x = v ++ u)))
nthConj : (Eq t) => (n : Nat) -> (w : Word) -> Bool -- should be able to do something with the prefix and hten reconstructing the new word?


-- This is what it would look like with primitives, can't use any of the properties usefully
--theorem2_4_2 : (w : Word) -> (x : Word) -> (isConjugateOfT w x) -> (isPowerT w) -> isPowerT x
--theorem2_4_2 w x isConj isPow = ?theorem2_4_2_rhs
-- This is what it looks like if you use too many types
-- theorem2_4_2DT : (w : Word) -> (x : Word) -> (Conjugate w x n) -> (Power w pw kw) -> (Power x px kx)  
--theorem2_4_2DT : (Eq t) => (w : Word t) -> (x : Word t) -> (Conjugate w x n) -> { pw : Word t } ->  (Power w pw kw) -> {px : Word t}  -> wordMult px kx = x
-- theorem2_4_2DT w x x1 x2 = ?theorem2_4_2DT_rhs_1

--theorem2_4_2DT w x (MkConjugate w x n) (MkPower w pw kw) = ?thm242Proof
