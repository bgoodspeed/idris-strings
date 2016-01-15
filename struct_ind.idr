module Prefix

infixr 8 #
%elim
data Word t = Empty | (#) t (Word t)

wordLength : Word t -> Nat
wordLength Empty = Z 
wordLength (x # y) = S (wordLength y) 


infixr 2 ##
(##) : Word t -> Word t -> Word t
(##) Empty w    = w
(##) (c # w) w2 = c # (w ## w2)


lengthComposite : (l : Word t) -> (m : Word t) -> 
                  wordLength (l ## m) = (wordLength l) + (wordLength m)
lengthComposite l m = ?lengthComposite_rhs


prefixLengthLess : (pre : Word t) -> (rest : Word t) -> 
                   Dec ( LTE (wordLength (pre)) (wordLength (pre ## rest)))
prefixLengthLess pre rest = ?prefixLengthLess_rhs


suffixLengthLess : (pre : Word t) -> (rest : Word t) -> 
                   Dec ( LTE (wordLength (rest)) (wordLength (pre ## rest)))
suffixLengthLess pre rest = ?suffixLengthLess_rhs


---------- Proofs ----------

Prefix.suffixLengthLess_rhs = proof
  intros
  rewrite sym (lengthComposite pre rest)
  mrefine isLTE 


Prefix.prefixLengthLess_rhs = proof
  intros
  rewrite sym (lengthComposite pre rest)
  mrefine isLTE 

Prefix.lengthComposite_rhs = proof
  intros
  induction l
  compute
  trivial
  intros
  compute
  rewrite ihw__0 
  trivial


