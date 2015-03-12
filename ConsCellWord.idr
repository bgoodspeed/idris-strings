module ConsCellWord 

import Prelude.Functor

%default total
-- Data types
infixr 8 #
data Word t = Empty | (#) t (Word t)

infixr 2 ##
(##) : Word t -> Word t -> Word t
(##) Empty w    = w
(##) (c # w) w2 = c # (w ## w2)



-- Instances 
instance (Eq t) =>  Eq (Word t) where
  Empty   == Empty   = True
  (a # x) == Empty   = False
  Empty   == (b # y) = False
  (a # x) == (b # y) = (a == b) && (x == y)

  
instance Functor Word where
  map f Empty   = Empty
  map f (c # w) = (f c) # (map f w)


instance Semigroup (Word t) where
  (<+>) = (##)

instance Monoid (Word t) where
  neutral = Empty

instance (Show t) => Show (Word t) where
  show xs = "(" ++ show' "" xs ++ ")" where
    show' acc Empty       = acc
    show' acc (c # Empty) = acc ++ show c
    show' acc (c # w)     = show' (acc ++ show c ++ " # ") w

||| A tail recursive right fold on Words
total foldrImpl : (t -> acc -> acc) -> acc -> (acc -> acc) -> Word t -> acc
foldrImpl f e go Empty = go e
foldrImpl f e go (c # w) = foldrImpl f e (go . (f c)) w

instance Foldable Word where
    foldr f e xs = foldrImpl f e id xs



instance Applicative Word where
  pure x = x # Empty

  fs <$> vs = concatMap (\f => map f vs) fs


instance Traversable Word where
  traverse f Empty = pure Empty 
  traverse f (c # w) = [| (#) (f c) (traverse f w) |]


instance Monad Word where
   m >>= f = concatMap f m


instance Alternative Word where
  empty = Empty
  (<|>) = (##)


-- Proofs and properties
wordInduction : (P : (Word t) -> Type)  -> -- Property to show
                (P Empty)               -> -- Base case
                ( (c : t) -> (w : (Word t)) ->  P w -> P (c # w)) -> -- Inductive Step
                ( a : (Word t)) ->        -- Show for all a
                P a
wordInduction P p_Empty p_Concat Empty   = p_Empty
wordInduction P p_Empty p_Concat (c # w) = p_Concat c w (wordInduction P p_Empty p_Concat w)


wordConcatIsAssociative : (l : Word t) -> (c : Word t) -> (r : Word t) -> (l ## (c ## r)) = ((l ## c) ## r)
wordConcatIsAssociative Empty c r = Refl 
wordConcatIsAssociative (x # y) c r = let inductiveHypothesis = wordConcatIsAssociative y c r in
                                          ?wordConcatIsAssociativeStepCase

-- Building this via semigroupOpIsAssociative = ?lemmaName, extract lemma with \l, do define with \d on lemma, then case analysis on the first arg, then standard let expression pattern for step case
instance VerifiedSemigroup (Word t) where
  semigroupOpIsAssociative = wordConcatIsAssociative



wordConcatNeutralIsNeutralL : (w : (Word t)) -> (w ## Empty) = w
wordConcatNeutralIsNeutralL Empty = Refl
wordConcatNeutralIsNeutralL (x # y) = let inductiveHypothesis = wordConcatNeutralIsNeutralL y in
                                          ?wordConcatNeutralIsNeutralLStepCase

wordConcatNeutralIsNeutralR : (w : (Word t)) -> (Empty ## w) = w
wordConcatNeutralIsNeutralR Empty = Refl 
wordConcatNeutralIsNeutralR (x # y) = let inductiveHypothesis = wordConcatNeutralIsNeutralR y in
                                          ?wordConcatNeutralIsNeutralRStepCase 


instance VerifiedMonoid (Word t) where
  monoidNeutralIsNeutralL = wordConcatNeutralIsNeutralL
  monoidNeutralIsNeutralR = wordConcatNeutralIsNeutralR


wordConcatIsInvInjective : (c : t) -> (w1 : (Word t)) -> (w2 : (Word t)) -> (pf : w1 = w2 ) -> c # w1 = c # w2
wordConcatIsInvInjective c w1 w2 pf = ?wordConcatIsInvInjective_rhs

wordConcatIsInjective : (c : t) -> (w1 : (Word t)) -> (w2 : (Word t)) -> {auto pf : c # w1 = c # w2 } -> w1 = w2
wordConcatIsInjective _ _ _ {pf = Refl} = Refl


functorIdentityProof :  (x : Word t) -> map id x = x
functorIdentityProof Empty = Refl 
functorIdentityProof (x # y) = let inductiveHypothesis = functorIdentityProof y in
                                   ?functorIdentityProofStepCase




functorCompositionProof : (x : Word a) -> (g1 : a -> b) -> (g2 : b -> c) -> map (g2 . g1) x = map g2 (map g1 x)
functorCompositionProof Empty g1 g2 = Refl 
functorCompositionProof (x # y) g1 g2 = let inductiveHypothesis = functorCompositionProof y g1 g2 in
                                            ?functorCompositionProofStepCase


instance VerifiedFunctor Word where
  functorIdentity = functorIdentityProof 
  functorComposition = functorCompositionProof 




applicativeMapProof : (x : Word a) -> (g : a -> b) -> map g x = ((map g x) ## Empty)
applicativeMapProof Empty g = Refl 
applicativeMapProof (x # y) g = let inductiveHypothesis = applicativeMapProof y g in
                                    ?applicativeMapProofStepCase


applicativeIdentityProof : (x : Word a) ->  ((map id x) ## Empty) = x
applicativeIdentityProof Empty = Refl 
applicativeIdentityProof (x # y) = let inductiveHypothesis = applicativeIdentityProof y in
                                       ?applicativeIdentityProofStepCase



applicativeCompositionProof : (x : Word a) -> (g1 : Word (a -> b)) -> (g2 : Word (b -> c)) -> ((pure (.) <$> g2) <$> g1) <$> x = g2 <$> (g1 <$> x)
applicativeCompositionProof Empty g1 g2 = ?applicativeCompositionProofBaseCase 
applicativeCompositionProof (x # y) g1 g2 = ?applicativeCompositionProof_rhs_2

-- TODONOTE this statement seems off, might be a bug?
applicativeHomomorphismProof : (x : a) -> (g : a -> b) -> ((g x) # Empty) = ((g x) # Empty)
applicativeHomomorphismProof x g = Refl 



applicativeInterchangeProof : (x : a) -> (g : Word (a -> b)) -> g <$> pure x = pure (\g' : a -> b => g' x) <$> g
applicativeInterchangeProof x g = ?applicativeInterchangeProof_rhs_1

-- TODONOTE http://learnyouahaskell.com/functors-applicative-functors-and-monoids

instance VerifiedApplicative Word where
  applicativeMap = applicativeMapProof
  applicativeIdentity = applicativeIdentityProof
  applicativeComposition = applicativeCompositionProof 
  applicativeHomomorphism = applicativeHomomorphismProof
  applicativeInterchange = applicativeInterchangeProof 






instance VerifiedMonad Word where
  monadApplicative = ?monadApplicativeProof 
  monadLeftIdentity = ?monadLeftIdentityProof
  monadRightIdentity = ?monadRightIdentityProof 
  monadAssociativity = ?monadAssociativity 
  


---------- Proofs ----------

ConsCellWord.applicativeIdentityProofStepCase = proof
  intros
  rewrite inductiveHypothesis 
  trivial


ConsCellWord.applicativeMapProofStepCase = proof
  intros
  rewrite inductiveHypothesis 
  trivial


ConsCellWord.functorCompositionProofStepCase = proof
  intros
  rewrite inductiveHypothesis 
  trivial


ConsCellWord.functorIdentityProofStepCase = proof
  intros
  rewrite inductiveHypothesis 
  trivial



ConsCellWord.wordConcatIsInvInjective_rhs = proof
  intros
  rewrite pf
  trivial


ConsCellWord.wordConcatNeutralIsNeutralRStepCase = proof
  intros
  trivial


ConsCellWord.wordConcatNeutralIsNeutralLStepCase = proof
  intros
  rewrite inductiveHypothesis 
  trivial


ConsCellWord.wordConcatIsAssociativeStepCase = proof
  intros
  rewrite inductiveHypothesis 
  trivial


