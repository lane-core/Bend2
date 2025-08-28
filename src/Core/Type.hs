-- Streamlined Public Interface for Bend2 Type System
-- ==================================================
-- Clean, ergonomic API consolidating the essential operations

module Core.Type (
  -- * Essential Types (from Core.Sort)
  Term(..), Val(..), Ne(..), Cmd(..), 
  Idx(..), Expr, Book, SomeTerm(..),
  
  -- * Core NbE Operations (from Core.Eval + Core.Val)
  eval, quote, nbe,
  termToVal, termToValWithBook,
  nbeTerm, nbeTermWithBook,
  
  -- * Semantic Operations (from Core.Val)
  vApp,
  
  -- * Command Execution (from Core.Eval)
  exec,
  
  -- * Utilities (from Core.Val)
  weakenVal, weakenNe,
  
  -- * Type Checking (from Core.Check)
  check, infer, checkProof,
  
  -- * Surface Conversion (integrated in type checker)
  -- surfaceToIntrinsic, intrinsicToSurface  -- REMOVED: unsafe Bridge functions
) where

-- Foundation types
import Core.Sort (Term(..), Cmd(..), Idx(..), Expr, Book, SomeTerm(..))

-- Unified evaluation system
import Core.Eval (Val(..), Ne(..), quote, vApp, weakenVal, weakenNe, termToVal, termToValWithBook, nbeTerm, nbeTermWithBook, exec)

-- Type checking
import Core.Check (check, infer, checkProof)

-- Surface conversion (removed - was unsafe Bridge module)

-- Convenient aliases for main operations
eval :: Term '[] ty -> Val '[] ty
eval = termToVal

nbe :: Term '[] ty -> Term '[] ty  
nbe = nbeTerm