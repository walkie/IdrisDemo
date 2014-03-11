module Demo.Intro

%hide Prelude.Bool.Bool
%hide Prelude.Bool.boolElim
%hide Prelude.List.List
%hide Prelude.List.Nil
%hide Prelude.List.(::)
%hide Prelude.Foldable.sum
%hide Prelude.Stream.Stream
%hide Prelude.Stream.Nil
%hide Prelude.Stream.(::)
%hide Prelude.Stream.take

%default total


---------------------------
-- Introduction to Idris --
---------------------------

--
-- Q: What is Idris?
-- A: A functional programming language with *dependent types*
--

--
-- Features: 
--   * full dependent types + dependent pattern matching
--   * strict by default + statically typed laziness
--   * data and codata
--   * extensible syntax
--   * interactive tactic-based theorem prover
--   * effects system
-- 


---------------------
-- Outline of Talk --
---------------------

-- 1. Brief comparison to Haskell
-- 2. Example: Typed stack language interpreter
-- 3. Example: Behavioral game theory simulator



---------------------------
-- Comparison to Haskell --
---------------------------

-- Goals:
--   * see some Idris syntax
--   * basic examples of features in Prelude:
--     * typed laziness
--     * extensible syntax
--     * data vs. codata


-- Simple data types look just like Haskell:

data Bool = False | True


-- Typed laziness:

boolElim : Bool -> Lazy a -> Lazy a -> a
boolElim True  t f = Force t
boolElim False t f = Force f


-- Syntactic sugar:

syntax if [test] then [t] else [e] = boolElim test (Delay t) (Delay e)



---------------------
-- Data vs. Codata --
---------------------

--
-- Lists in Haskell:
-- 
--   data List a = Nil | a :: List a
--
-- 

-- Data:
--   * strict
--   * must be finite
--   * total functions *terminate*
--     * structural recursion: recurse on subexpressions

namespace Lists

  data List : Type -> Type where
    Nil  : List a
    (::) : a -> List a -> List a
  
  -- Guaranteed to terminate
  sum : List Integer -> Integer
  sum []        = 0
  sum (x :: xs) = x + sum xs


-- Codata:
--   * lazy
--   * can be infinite
--   * total functions are *productive*
--     * guarded recursion: recurse within constructor

namespace Streams

  codata Stream : Type -> Type where
    (::) : a -> Stream a -> Stream a

  -- Consume a stream (dependent types sneak peak)
  take : (n : Nat) -> Stream a -> Vect n a
  take Z     _         = []
  take (S n) (x :: xs) = x :: take n xs

  -- Generate a stream
  from : Integer -> Stream Integer
  from n = n :: from (n+1)

  -- Consume a stream, producing a new stream (scan)
  runningSum : Integer -> Stream Integer -> Stream Integer
  runningSum y (x :: xs) = y :: runningSum (x+y) xs
