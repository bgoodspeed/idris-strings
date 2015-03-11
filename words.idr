module Words

%default total

-- Data Types
%elim
data SignedChar : Type where
  Pos : Char -> SignedChar
  Neg : Char -> SignedChar


%name SignedChar c,x,y,z


infixr 8 #
%elim
data Word = Empty | (#) SignedChar Word

%name Word w, w2, w3, w4

-- Equivalence

instance Eq SignedChar where
  (Pos x) == (Neg y) = False
  (Neg x) == (Pos y) = False
  (Pos x) == (Pos y) = x == y
  (Neg x) == (Neg y) = x == y

  x /= y = not (x == y)

instance Eq Word where
  (a # b) == Empty   = False
  Empty   == (a # b) = False
  Empty   == Empty   = True
  (a # b) == (c # d) = (a == c) && (b == d)

  x /= y             = not (x == y)

-- Methods
signedCharInverse : SignedChar -> SignedChar
signedCharInverse (Pos x) = Neg x
signedCharInverse (Neg x) = Pos x


wordLength : Word -> Nat
wordLength Empty = Z 
wordLength (x # y) = S (wordLength y)


wordSignedFromCharList : (Char -> SignedChar) -> List Char -> Word
wordSignedFromCharList f [] = Empty
wordSignedFromCharList f (x :: xs) = (f x) # (wordSignedFromCharList f xs) 

wordFromCharList : List Char -> Word
wordFromCharList xs = wordSignedFromCharList Pos xs

wordInverseFromCharList : List Char -> Word
wordInverseFromCharList xs = wordSignedFromCharList Neg xs


wordFromString : String -> Word
wordFromString x = wordFromCharList (unpack x)

-- TODO note in the docs this function reverses the string, but the list of chars does not
wordInverseFromString : String -> Word
wordInverseFromString x = wordInverseFromCharList (unpack (reverse x))

stringFromWord : Word -> String
stringFromWord Empty = ""
stringFromWord ((Pos x) # y) = (singleton x) ++ stringFromWord y
stringFromWord ((Neg x) # y) = (singleton x) ++ stringFromWord y

wordConcat : Word -> Word -> Word
wordConcat Empty x1 = x1 
wordConcat (x # y) x1 = x # (wordConcat y x1)

isInverseOf : SignedChar -> SignedChar -> Bool
isInverseOf (Pos _) (Pos _) = False
isInverseOf (Neg _) (Neg _) = False
isInverseOf (Neg x) (Pos y) = x == y
isInverseOf (Pos x) (Neg y) = x == y

%assert_total
wordCollapseOneLevel : Word -> Word
wordCollapseOneLevel Empty = Empty
wordCollapseOneLevel (x # Empty) = x # Empty
wordCollapseOneLevel (x # (y # z)) = case (x `isInverseOf` y) of
                                          True  => wordCollapseOneLevel z
                                          False => x # wordCollapseOneLevel (y # z) -- TODO this is where it can't detect that the function is total, might be due to the same problem as: https://groups.google.com/forum/#!topic/idris-lang/3k45xqR9BLs (Totality and With Rule)

%assert_total
wordCollapse : Word -> Word
wordCollapse x = let y = wordCollapseOneLevel x in
                     case (x == y) of
                          True  => x
                          False => wordCollapse y


wordConcatAndCollapse : Word -> Word -> Word
wordConcatAndCollapse w1 w2 = let w = wordConcat w1 w2 in
                                  wordCollapse w

--TODO it would be sweet to have new intentions
-- like \l to make a lemma, one for inlining, one for rename etc, livetemplates for new methods?


wordSignedCharAtMaybe : Nat -> Word -> Maybe SignedChar
wordSignedCharAtMaybe Z Empty    = Nothing
wordSignedCharAtMaybe Z (x # xs) = Just x
wordSignedCharAtMaybe (S k) Empty = Nothing
wordSignedCharAtMaybe (S k) (x # xs) = wordSignedCharAtMaybe k xs

wordInverse : Word -> Word
wordInverse Empty = Empty
wordInverse (x # y) = wordConcat (wordInverse y) (signedCharInverse (x) # Empty)

{-

wordLengthZeroImpliesEmpty : (w : Word) -> {auto wordLengthIsZero : wordLength w = Z } -> w = Empty
wordLengthZeroImpliesEmpty Empty = Refl
wordLengthZeroImpliesEmpty (x # y) = ?foo_2 -- impossible how to show contradiction
-}



-- TODO assert complete w/o the _ Empty case?  why do i need to show this?

{- TODO this is tougher than it seems 
wordSignedCharAt : (n : Nat) -> (w : Word) -> {auto w_nonempty : w = a # ws } -> {auto len_ok : (wordLength w > n) = True} -> SignedChar
wordSignedCharAt _ Empty    = Pos 'Z' -- this is impossible
wordSignedCharAt Z (c # cs) = wordSignedCharAtZ w_nonempty len_ok 
wordSignedCharAt (S k) (c # cs) = ?wordSignedCharAtSk
--wordSignedCharAt (S k) (c # cs) = let rec = wordSignedCharAt k cs { ?foo }   
-}
isPrefixOf : Word -> Word -> Bool
isPrefixOf Empty w2 = True
isPrefixOf (x # y) Empty = False
isPrefixOf (x # y) (z # w) = (x == z) && (isPrefixOf y w) 

-- Semigroup Properties

instance Semigroup Word where
  x <+> y   =  wordConcatAndCollapse x y

wordInduction : (P : Word -> Type)  -> -- Property to show
                (P Empty)           -> -- Base case
                ( (c : SignedChar) -> (w : Word) ->  P w -> P (c # w)) -> -- Inductive Step
                ( a : Word ) ->        -- Show for all a
                P a
wordInduction P p_Empty p_Concat Empty   = p_Empty
wordInduction P p_Empty p_Concat (c # w) = p_Concat c w (wordInduction P p_Empty p_Concat w) 
-- TODO bring in all the functions from https://github.com/idris-lang/Idris-dev/blob/master/libs/prelude/Prelude/List.idr
-- and from the string lib
{-
wordConcatAndCollapseIsAssociative : (l : Word) -> (c : Word) -> (r: Word) -> wordConcatAndCollapse l (wordConcatAndCollapse c r) = wordConcatAndCollapse (wordConcatAndCollapse l c) r
wordConcatAndCollapseIsAssociative Empty c r = Refl
wordConcatAndCollapseIsAssociative (x # w) c r = let inductiveHypothesis = wordConcatAndCollapseIsAssociative w c r in 
                                          ?wordConcatAndCollapseIsAssociativeStepCase



instance VerifiedSemigroup Word where
  semigroupOpIsAssociative = wordConcatAndCollapseIsAssociative
  -}

instance Monoid Word where
  neutral = Empty

{-

wordConcatInnerAssociativeWithInverse : (w : Word) -> wordConcat w (wordConcat (wordInverse w) (Empty)) = (wordConcat (wordConcat w (wordInverse w)) ( Empty)) 
wordConcatInnerAssociativeWithInverse Empty = Refl
wordConcatInnerAssociativeWithInverse (c # w) = let inductiveHypothesis = wordConcatInnerAssociativeWithInverse w in
                                                    ?wordConcatInnerAssociativeWithInverseStepCase


wordConcatInnerAssociative : (c : SignedChar) -> (w : Word) -> c # wordConcat w (wordConcat (wordInverse w) (signedCharInverse c # Empty)) = c # (wordConcat (wordConcat w (wordInverse w)) (signedCharInverse c # Empty)) 
wordConcatInnerAssociative c Empty = Refl
wordConcatInnerAssociative c (x # w) = let inductiveHypothesis = wordConcatInnerAssociative c w in
                                           ?wordConcatInnerAssociativeStepCase


-}

wordConcatEmptyRightNeutral : (w : Word) -> wordConcat w Empty = w
wordConcatEmptyRightNeutral Empty = Refl
wordConcatEmptyRightNeutral (c # w) = let inductiveHypothesis = wordConcatEmptyRightNeutral w in
                                           ?wordConcatEmptyRightNeutralStepCase


wordConcatAndCollapseEmptyRightNeutral : (w : Word) -> wordConcatAndCollapse w Empty = w
wordConcatAndCollapseEmptyRightNeutral Empty = Refl
wordConcatAndCollapseEmptyRightNeutral (c # w) = let inductiveHypothesis = wordConcatAndCollapseEmptyRightNeutral w in 
                                          ?wordConcatAndCollapseEmptyRightNeutralStepCase
{-
instance VerifiedMonoid Word where
  monoidNeutralIsNeutralL = wordConcatEmptyRightNeutral
  monoidNeutralIsNeutralR xs = Refl

instance Group Word where
  inverse = wordInverse

wordInverseIsGroupInverseL : (l : Word) -> wordConcat l (wordInverse l) = Empty
wordInverseIsGroupInverseL Empty = Refl
wordInverseIsGroupInverseL (c # w) = let inductiveHypothesis = wordInverseIsGroupInverseL w in
                                         ?wordInverseIsGroupInverseLStepCase

instance VerifiedGroup Word where
  groupInverseIsInverseL = wordInverseIsGroupInverseL 
  groupInverseIsInverseR = ?wordInverseIsGroupInverseR


-}
---------- Proofs ----------
{-
Words.wordConcatEmptyRightNeutralStepCase = proof
  intros
  rewrite inductiveHypothesis 
  trivial
  -}

{-
Words.wordConcatAndCollapseIsAssociativeStepCase = proof
  intros
  rewrite inductiveHypothesis 
  trivial

-}

---------- Proofs ----------

Words.wordConcatEmptyRightNeutralStepCase = proof
  intros
  rewrite inductiveHypothesis 
  trivial


