
module ListDecisions

import Decidable.Equality
import DecHelper
import Utilities

isPrefixOfT : (Eq a) => List a -> List a -> Type
isPrefixOfT xs ys = isPrefixOf xs ys = True 

isPrefixOfDec : (Eq a) => (xs : List a) -> (ys : List a) -> Dec (isPrefixOfT xs ys)
isPrefixOfDec xs ys with (isPrefixOf xs ys) 
  | True  = Yes Refl
  | False = No  falseNotTrue


isSuffixOfT : (Eq a) => List a -> List a -> Type
isSuffixOfT xs ys = isSuffixOf xs ys = True 

isSuffixOfDec : (Eq a) => (xs : List a) -> (ys : List a) -> Dec (isSuffixOfT xs ys)
isSuffixOfDec xs ys with (isSuffixOf xs ys) 
  | True  = Yes Refl
  | False = No  falseNotTrue

isPalindrome : (Eq a) => List a -> Bool
isPalindrome xs = (reverse xs) == xs

isPalindromeT : (Eq a) => List a -> Type
isPalindromeT xs = isPalindrome xs = True

isPalindromeDec : (Eq a) => (xs : List a) -> Dec (isPalindromeT xs)
isPalindromeDec xs with (isPalindrome xs)
  | True  = Yes Refl 
  | False = No falseNotTrue 


possibleBordersFor : (Eq a) =>  List a -> List (List a)
possibleBordersFor xs = let prefixes = inits xs 
                            lxs = (div (length xs) 2) in 
                            filter (\x => (length x > 0) && (length x <= lxs)) prefixes

isBordered : (Eq a) => List a -> Bool
isBordered xs = let valid_prefixes = possibleBordersFor xs in
                    any (\pfx => isSuffixOf pfx xs) valid_prefixes
                    

isBorderedT : (Eq a) => List a -> Type
isBorderedT xs = isBordered xs = True

isBorderedDec : (Eq a) => (xs : List a) -> Dec (isBorderedT xs)
isBorderedDec xs with (isBordered xs) 
  | True  = Yes Refl
  | False = No falseNotTrue
