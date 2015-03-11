module ListQuantifiers

import DecHelper
-- This is identical to the Data.Vect.Quantifiers but for lists.

%default total

data Any : (P : a -> Type)-> List a -> Type where
  Here  : {P : a -> Type} -> {xs : List a} -> P x -> Any P (x :: xs)
  There : {P : a -> Type} -> {xs : List a} -> Any P xs -> Any P (x :: xs)

anyNilAbsurd : {P : a -> Type} -> Any P Nil -> Void
anyNilAbsurd (Here _) impossible
anyNilAbsurd (There _) impossible

anyElim : {xs : List a} -> {P : a -> Type} -> (Any P xs -> b) -> (P x -> b) -> Any P (x :: xs) -> b
anyElim _ g (Here p)  = g p
anyElim f _ (There p) = f p

any : {P : a -> Type} -> (dec : (x : a) -> Dec (P x)) -> (xs : List a) -> Dec (Any P xs)
any _ [] = No anyNilAbsurd
any p (x :: xs) with (p x)
  | Yes prf = Yes (Here prf)
  | No prf  = case any p xs of
                   Yes prf' => Yes (There prf')
                   No  prf' => No  (anyElim prf' prf)


data All : (P : a -> Type) -> List a -> Type where
  Nil : {P : a -> Type} -> All P Nil
  (::) : {P : a -> Type} -> {xs : List a} -> P x -> All P xs -> All P (x :: xs)


negAnyAll : {P : a -> Type} -> {xs : List a} -> Not (Any P xs) -> All (\x => Not (P x)) xs
negAnyAll {xs=Nil} _ = Nil
negAnyAll {xs=(x::xs)} f = (\x => f (Here x)) :: negAnyAll (\x => f (There x))

notAllHere : {P : a -> Type} -> {xs : List a} -> Not (P x) -> All P (x :: xs) -> Void
notAllHere _ Nil impossible
notAllHere np (p :: _) = np p

notAllThere : {P : a -> Type} -> {xs : List a} -> Not (All P xs) -> All P (x :: xs) -> Void
notAllThere _ Nil impossible
notAllThere np (_ :: ps) = np ps

all : {P : a -> Type} -> (dec : (x : a) -> Dec (P x)) -> (xs : List a) -> Dec (All P xs)
all _ Nil = Yes Nil
all d (x :: xs) with (d x)
  | No prf = No (notAllHere prf)
  | Yes prf = case all d xs of
                   Yes prf' => Yes (prf :: prf')
                   No  prf' => No (notAllThere prf')

