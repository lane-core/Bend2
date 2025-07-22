{-./Type.hs-}

module Core.Adjust where

import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

import Core.Bind
import Core.Deps
import Core.EtaForm
import Core.Flatten
import Core.Type
import Core.WHNF

-- | Adjusts a single term, simplifying pattern matching and other constructs.
-- It uses a book of already-adjusted definitions for context during flattening.
adjust :: Book -> Term -> Term
adjust book term =
  trace ("done: " ++ show done) $
  done
  where
    flat  = flatten 0 book term
    npat = unpat 0 flat
    nfrk = unfrk 0 npat
    etas = etaForm 0 nfrk
    done = bind etas

-- | Adjusts a term. simplifying patterns but leaving terms as Pats.
adjustWithPats :: Book -> Term -> Term
adjustWithPats book term =
  ret
  where ret = bind (unfrk 0 (flatten 0 book term))

-- The state for the adjustment process. It holds:
-- 1. The book of already-adjusted definitions.
-- 2. A set of names that have been processed to avoid redundant work (memoization).
type AdjustState = (Book, S.Set Name)

-- | Adjusts an entire book of definitions, respecting dependencies.
-- It performs a topological sort of the definitions based on their references
-- and adjusts them in order. This ensures that when a definition is adjusted,
-- all definitions it depends on have already been adjusted.
-- This is crucial for functions like `flatten` which may look up references.
adjustBook :: Book -> Book
adjustBook book@(Book defs) =
  -- The final adjusted book is extracted from the state after processing all definitions.
  fst $ execState (mapM_ (adjustDef book S.empty adjust) (M.keys defs)) (Book M.empty, S.empty)

-- | Adjusts the entire book, simplifying patterns but without removing Pat terms.
adjustBookWithPats :: Book -> Book
adjustBookWithPats book@(Book defs) =
  fst $ execState (mapM_ (adjustDef book S.empty adjustWithPats) (M.keys defs)) (Book M.empty, S.empty)

-- | The recursive worker function that adjusts a single definition.adjustBook
-- It takes a set of names currently in the recursion stack to detect cycles.
adjustDef :: Book -> S.Set Name -> (Book -> Term -> Term) -> Name -> State AdjustState ()
adjustDef book visiting adjustFn name = do
  (_, adjustedSet) <- get

  -- Process the definition only if it's not in the current recursion path (to avoid cycles)
  -- and has not been adjusted yet (for memoization).
  if name `S.member` visiting || name `S.member` adjustedSet
    then return ()
    else case getDefn book name of
      -- This case should not be reachable if `name` comes from `M.keys defs`.
      Nothing -> return ()
      Just (inj, term, typ) -> do
        -- 1. Collect all dependencies (references) from the term and its type.
        -- We use a custom collector that correctly handles variable scope and
        -- treats function heads in patterns as dependencies.
        let deps = S.union (getDeps term) (getDeps typ)

        -- 2. Recursively adjust all dependencies.
        -- The current name is added to the `visiting` set for cycle detection.
        let newVisiting = S.insert name visiting
        mapM_ (adjustDef book newVisiting adjustFn) (S.toList deps)

        -- 3. After dependencies are adjusted, adjust the current definition.
        -- We need to get the latest version of the adjusted book from the state,
        -- as it has been updated by the recursive calls.
        (partialAdjBook, _) <- get

        let adjTerm = adjustFn partialAdjBook term
        let adjType = adjustFn partialAdjBook typ

        -- 4. Update the state with the newly adjusted definition.
        -- The name is added to the `adjustedSet` to mark it as complete.
        modify $ \(Book adjMap, doneSet) ->
          let newAdjMap  = M.insert name (inj, adjTerm, adjType) adjMap
              newDoneSet = S.insert name doneSet
          in (Book newAdjMap, newDoneSet)

