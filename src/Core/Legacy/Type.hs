-- Bend2's Core.Sort
-- =================
-- This is the starting point of this repository. All other modules are files
-- from/to the core Expr type (surface expressions). The intrinsic Term type
-- is now the primary representation. Includes Books, Errors and other helper types.
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Core.Sort where

import Core.Sort
import Data.Kind (Type)
import Data.Map qualified as M
