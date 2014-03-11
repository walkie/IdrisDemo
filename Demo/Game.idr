module Demo.Game

import Data.HVect

%default total


-------------------------------
-- Behavioral Game Simulator --
-------------------------------

-- Goals:
--   * "more realistic" example
--   * heavier use of dependent types
--   * small theorem proving example


--
-- Game Definition
--

-- A payoff is a vector of scores, one for each player.
Payoff : Nat -> Type
Payoff np = Vect np Integer

-- Each player may play a different type of move. This vector describes
-- the move type for all players.
MoveTypes : Nat -> Type
MoveTypes np = Vect np Type


using (mvs : MoveTypes np)

  -- A game is a tree with payoffs at the leaves. Each internal node
  -- represents a decision by one of the players.
  data Game : MoveTypes np -> Type where
    Turn : (i : Fin np) -> (index i mvs -> Game mvs) -> Game mvs
    End  : Payoff np -> Game mvs


--
-- Example: Prisoner's Dilemma
--

Dilemma : MoveTypes 2
Dilemma = [Bool, Bool]

dilemma : Game Dilemma
dilemma =
  Turn 0 (\mv0 =>
    Turn 1 (\mv1 =>
      case (mv0, mv1) of
        (True , True ) => End [2,2]
        (True , False) => End [0,3]
        (False, True ) => End [3,0]
        (False, False) => End [1,1]))


--
-- Example: Ultimatum Game
--

Ultimatum : MoveTypes 2
Ultimatum = [Fin 101, Bool]

ultimatum : Game [Fin 101, Bool]
ultimatum =
  Turn 0 (\amount =>
    Turn 1 (\accept =>
      if accept then let a = cast amount
                     in End [a, 100 - a]
      else End [0,0]))


--
-- Pure (boring) game execution
--

-- A pure strategy profile consists of a single move for each player,
-- which they always play on their turn.
PureProfile : MoveTypes np -> Type
PureProfile mvs = HVect mvs

using (mvs : MoveTypes np)

  playPure : Game mvs -> PureProfile mvs -> Payoff np
  playPure (Turn i f) ss = playPure (f (index i ss)) ss
  playPure (End p)    _  = p


--
-- Iterated game execution state
--

using (mvs : MoveTypes np)

  -- A game event is either a played move or a payoff at the end.
  data Event : MoveTypes np -> Type where
    Move : (i : Fin np) -> index i mvs -> Event mvs
    Pay  : Payoff np                   -> Event mvs

-- A game transcript is a sequence of events.
Transcript : MoveTypes np -> Type
Transcript mvs = List (Event mvs)


--
-- Strategies
--

-- A strategy for a particular player is a function from the transcript
-- so far to a move of the appropriate type.
Strategy : MoveTypes np -> Fin np -> Type
Strategy mvs i = Transcript mvs -> index i mvs


using (mvs : MoveTypes np)

  -- A pure strategy, always play the same move.
  pure : (i : Fin np) -> index i mvs -> Strategy mvs i
  pure i m = const m

  -- Get the last move played by the indicated player.
  lastMove : (i : Fin np) -> Transcript mvs -> Maybe (index i mvs)

  -- Want to write something like the following,
  -- but the types aren't right... See why?
  --
  -- lastMove i (Move j m :: t) = if i == j then Just m else lastMove i t
  -- 
  -- Instead, try to find a proof that i and j are equal.
  -- Idris needs our help to type check the Yes case.
  -- ?= means that we will provide a proof that the type is correct.
  -- The proof at the bottom of the file was constructed interactively
  -- in the Idris REPL.
  lastMove i (Move j m :: t) with (decEq i j)
    | Yes p ?= Just m
    | No  _  = lastMove i t
  lastMove i (_ :: t) = lastMove i t
  lastMove _ []       = Nothing


--
-- Some example strategies for our games
--

-- PD strategy for either player:
-- Cooperate on the first move, then do whatever the opponent did in the
-- previous iteration.
titForTat : (i : Fin 2) -> Strategy Dilemma i
titForTat (fZ)         t = fromMaybe True (lastMove 1 t)
titForTat (fS fZ)      t = fromMaybe True (lastMove 0 t)
titForTat (fS (fS fZ)) _ impossible

-- PD strategy for either player:
-- Alternate between cooperation and defection.
alternate : (i : Fin 2) -> Bool -> Strategy Dilemma i
alternate (fZ)         x t = maybe x not (lastMove 0 t)
alternate (fS fZ)      x t = maybe x not (lastMove 1 t)
alternate (fS (fS fZ)) _ _ impossible

-- Ultimatum strategy for first player:
-- Play the `from` bid in the first iteration, then increase bid by `step`
-- in each subsequent game.
increase : Fin 101 -> Nat -> Strategy Ultimatum 0
increase from step t = maybe from (inc step) (lastMove 0 t)
  where
    inc : Nat -> Fin 101 -> Fin 101
    inc s m = fromMaybe maxBound (natToFin (s + finToNat m) 101)

-- Ultimatum strategy for second player:
-- Accept the bid if it is below a certain threshold.
threshold : Fin 101 -> Strategy Ultimatum 1
threshold x t = maybe True (\m => (finToNat m <= finToNat x)) (lastMove 0 t)


--
-- Iterated game execution (two-player games only)
--

-- Execute a single iteration of the game.
iter : Game [mv1,mv2] -> Strategy [mv1,mv2] 0 -> Strategy [mv1,mv2] 1
    -> Transcript [mv1,mv2] -> (Payoff 2, Transcript [mv1,mv2])
iter (Turn fZ      f) s0 s1 t = let m = s0 t in iter (f m) s0 s1 (Move 0 m :: t)
iter (Turn (fS fZ) f) s0 s1 t = let m = s1 t in iter (f m) s0 s1 (Move 1 m :: t)
iter (End p)          _  _  t = (p, Pay p :: t)
iter (Turn (fS (fS fZ)) f) _ _ _ impossible

-- Execute games indefinitely, producing a stream of payoffs.
play : Game [mv1,mv2] -> Strategy [mv1,mv2] 0 -> Strategy [mv1,mv2] 1
    -> Transcript [mv1,mv2] -> Stream (Payoff 2)
play g s0 s1 t = let (p,t') = iter g s0 s1 t
                 in p :: play g s0 s1 t'

-- Calculate the score after the given number of games.
score : Nat -> Stream (Payoff np) -> Payoff np
score Z     _         = replicate _ 0
score (S n) (p :: ps) = zipWith (+) p (score n ps)


-- Examples from Idris REPL:
--
-- > take 4 (play dilemma (titForTat 0) (alternate 1 True) [])
-- [[2, 2], [0, 3], [3, 0], [0, 3]] : Vect 4 (Vect 2 Integer)
--
-- > take 4 (play ultimatum (increase 15 20) (threshold 60) [])
-- [[15, 85], [35, 65], [55, 45], [0, 0]] : Vect 4 (Vect 2 Integer)
--
-- > score 100 (play dilemma (titForTat 0) (titForTat 1) [])
-- [200, 200] : Vect 2 Integer


---------- Proofs ----------

Demo.Game.lastMove_lemma_1 = proof
  intros
  rewrite (sym p)
  trivial
