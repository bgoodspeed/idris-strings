module Main 


import Control.Monad.Identity
import Control.Monad.State


-- Ported from http://pbrisbin.com/posts/regular_expression_evaluation_via_finite_automata/


data Pattern
   = Empty                   -- ""
   | Literal Char            -- "a"
   | Concat Pattern Pattern  -- "ab"
   | Choose Pattern Pattern  -- "a|b"
   | Repeat Pattern          -- "a*"

SID : Type
SID = Int -- State Identifier


record Rule : Type where
  MkRule : (fromState  : SID) -> (inputChar  : Maybe Char) -> (nextStates : List SID) -> Rule 

    
--any (`elem` acceptStates nfa) (currentStates nfa ++ freeStates nfa)
record NFA : Type where
  MkNFA : (rules : List Rule) -> (currentStates : List SID) -> (acceptStates : List SID) -> NFA



followRules : List Rule -> List SID
followRules = concatMap nextStates
    

freeMoves : NFA -> List SID -> List Rule
freeMoves nfa ss = filter (\r =>
    (fromState r `elem` ss) && (isNothing $ inputChar r)) $ rules nfa


go : NFA -> List SID -> List SID -> List SID
go n acc [] = acc 
go n acc ss =
    let ss' = followRules $ freeMoves n ss
    in go n (acc ++ ss') ss' 

freeStates : NFA -> List SID
freeStates nfa = go nfa [] (currentStates nfa)



availableStates : NFA -> List SID
availableStates nfa = currentStates nfa ++ freeStates nfa



ruleApplies : Char -> NFA -> Rule -> Bool
ruleApplies c nfa r =
    maybe False (c ==) (inputChar r) && (fromState r `elem` availableStates nfa)


findRules : Char -> NFA -> List Rule
findRules c nfa = filter (ruleApplies c nfa) $ rules nfa


    --any (`elem` acceptStates nfa) (currentStates nfa ++ freeStates nfa)
process : NFA -> Char -> NFA
process nfa c = case findRules c nfa of
    -- Invalid input should cause the NFA to go into a failed state. 
    -- We can do that easily, just remove any acceptStates.
    [] => record { acceptStates = [] } nfa
    rs => record { currentStates = followRules rs } nfa

--TODONOTE TODO add to porting guide record syntax
-- haskell version: record_var_name { thing_to_update = newvalue }
-- idris version  : record { name = "Jim" } fred

accepted : NFA -> Bool
accepted nfa = any (\x => x `elem` (acceptStates nfa)) (currentStates nfa ++ freeStates nfa)
      -- any (`elem` acceptStates nfa) (currentStates nfa ++ freeStates nfa)
    
{-  MkNFA (rules         : List Rule
    , currentStates : List SID
    , acceptStates  : List SID
    } 
    -}
accepts : NFA -> List Char -> Bool
accepts nfa = accepted . foldl process nfa


SIDPool : Type -> Type
SIDPool a = State (List SID) a

--data SIDPool a = State List SID a

nextId : SIDPool SID
nextId = do
    (x::xs) <- get
    put xs
    return x


freeMoveTo : NFA -> SID -> Rule
freeMoveTo nfa s = MkRule s Nothing (currentStates nfa)

buildNFA : Pattern -> SIDPool NFA
buildNFA p = do
    s1 <- nextId
    case p of
        Empty     => return $ MkNFA [] [s1] [s1]
        Literal c => do
            s2 <- nextId
            return $ MkNFA [MkRule s1 (Just c) [s2]] [s1] [s2]
        Concat p1 p2 => do
            nfa1 <- buildNFA p1
            nfa2 <- buildNFA p2

            let freeMoves = map (freeMoveTo nfa2) $ acceptStates nfa1

            return $ MkNFA
                (rules nfa1 ++ freeMoves ++ rules nfa2)
                (currentStates nfa1)
                (acceptStates nfa2)
        Choose p1 p2 => do
            s2 <- nextId
            nfa1 <- buildNFA p1
            nfa2 <- buildNFA p2

            let freeMoves =
                    [ freeMoveTo nfa1 s2
                    , freeMoveTo nfa2 s2
                    ]

            return $ MkNFA
                (freeMoves ++ rules nfa1 ++ rules nfa2) [s2]
                (acceptStates nfa1 ++ acceptStates nfa2)
        Repeat p => do
            s2 <- nextId
            nfa <- buildNFA p

            let freeMoves = map (freeMoveTo nfa) $ (acceptStates nfa)

            return $ MkNFA
                ((freeMoveTo nfa s2) :: rules nfa ++ freeMoves) [s2] (s2 :: acceptStates nfa)


concreteSidList : List SID
concreteSidList = [1..11111111111]  -- TODO should be infinite stream [1..]

runState : State s a -> s -> (a, s)
runState m = runIdentity . runStateT m 


evalState : State s a -> s -> a
evalState m s = fst (runState m s) 


toNFA : Pattern -> NFA
toNFA p = evalState (buildNFA p) [1..111111111111] 
--toNFA p = get (buildNFA p) [1..]
--toNFA p = get (buildNFA p) concreteSidList 


matches : String -> Pattern -> Bool
matches s = (\x => x `accepts` (unpack s)) . toNFA


doWhatever : Monad m => m a -> Bool
doWhatever m = True


main : IO ()
main = do
    -- This AST represents the pattern /ab|cd*/:
    let p = Choose
            (Concat (Literal 'a') (Literal 'b'))
            (Concat (Literal 'c') (Repeat (Literal 'd')))
    print $ "xyz" `matches` p
    -- => False
    print $ "cddd" `matches` p
    -- => True


