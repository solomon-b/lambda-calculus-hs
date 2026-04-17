{-# LANGUAGE DeriveTraversable #-}

module Utils
  ( SnocList (..),
    nth,
    alignWithM,
    allM,
    iter,
    iterM,
  )
where

import Data.Align (Semialign, align)
import Data.These (These)

-- | A list that grows on the right. We use this as our environment
-- representation because it matches the structure of de Bruijn
-- indices: the most recently bound variable is at the end (index 0),
-- and older bindings are further left (higher indices).
--
-- A regular list would work too, but snoc lists make the
-- correspondence between binding order and index explicit.
data SnocList a
  = Snoc (SnocList a) a
  | Nil
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- | Look up a value by de Bruijn index, counting from the right
-- (most recent binding).
nth :: SnocList a -> Int -> Maybe a
nth xs i
  | i < 0 = Nothing
  | otherwise =
      let go = \case
            (Nil, _) -> Nothing
            (Snoc _ x, 0) -> Just x
            (Snoc xs' _, i') -> go (xs', i' - 1)
       in go (xs, i)

-- | Align two structures and traverse the result. Used by record
-- tactics to check term fields against type fields: 'These' means
-- both present, 'This' means a field in the type but not the term
-- (missing), 'That' means a field in the term but not the type
-- (extra).
alignWithM ::
  (Traversable t, Applicative f, Semialign t) =>
  (These a b1 -> f b2) ->
  t a ->
  t b1 ->
  f (t b2)
alignWithM f as = traverse f . align as

allM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
allM _ [] = pure True
allM f (x : xs) =
  f x >>= \case
    False -> pure False
    True -> allM f xs

iter :: (a -> a) -> a -> Word -> a
iter _s z 0 = z
iter s z n = s (iter s z (n - 1))

iterM :: (Monad m) => (a -> m a) -> a -> Word -> m a
iterM s z 0 = pure z
iterM s z n = s =<< iterM s z (n - 1)
