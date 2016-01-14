module Transducers

-- http://web.cs.ucdavis.edu/~rogaway/classes/120/spring13/eric-transducers.pdf

data State = SA | SB | SC

InputAlphabetT : Type
InputAlphabetT = Char 

OutputAlphabetT : Type
OutputAlphabetT = Char


data DeterministicTransducer : Type where
  MkTransducer : List State ->
                 List InputAlphabetT ->
                 List OutputAlphabetT ->
                 (State -> InputAlphabetT -> State) ->
                 (State -> InputAlphabetT -> OutputAlphabetT) ->
                 State ->
                 (State -> Bool) -> DeterministicTransducer


evalTransducer' : DeterministicTransducer -> List InputAlphabetT -> State -> List OutputAlphabetT -> (Bool, List OutputAlphabetT)
evalTransducer' (MkTransducer states inputs outputs stateTrans outputFunc startState isFinalState) [] currentState accumulatedOutput =  ( isFinalState currentState, accumulatedOutput)
evalTransducer' dt@(MkTransducer states inputs outputs stateTrans outputFunc startState isFinalState) (c :: cs) currentState accumulatedOutput =  
  evalTransducer' dt cs (stateTrans currentState c) ( (outputFunc currentState c) :: accumulatedOutput) 


evalTransducer : DeterministicTransducer -> List InputAlphabetT -> (Bool, List OutputAlphabetT)
evalTransducer dt@(MkTransducer ys zs ws f g startState y) cs = let (a, b) = evalTransducer' dt cs startState [] in
                                                                    (a, reverse b)


sillyStateTrans : State -> InputAlphabetT -> State
sillyStateTrans s c = s 

sillyOutputFunc : State -> InputAlphabetT -> OutputAlphabetT
sillyOutputFunc x 'a' = 'A'
sillyOutputFunc x 'b' = 'A'
sillyOutputFunc x _   = 'C' 


sillyFinalState : State -> Bool
sillyFinalState x = True 


SillyDT : DeterministicTransducer
SillyDT = MkTransducer [SA] ['a', 'b', 'c'] ['A', 'B', 'C'] sillyStateTrans sillyOutputFunc SA sillyFinalState

testSillyDT : evalTransducer SillyDT ['a', 'a', 'c', 'b'] = (True, ['A', 'A', 'C', 'A'])
testSillyDT = Refl 

