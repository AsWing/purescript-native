-----------------------------------------------------------------------------
--
-- Module      :  Language.PureScript.CodeGen.Lisp.Optimizer.Unused
-- Copyright   :  (c) Phil Freeman 2013-14
-- License     :  MIT
--
-- Maintainer  :  Phil Freeman <paf31@cantab.net>
-- Stability   :  experimental
-- Portability :
--
-- |
-- Removes unused variables
--
-----------------------------------------------------------------------------

module Language.PureScript.CodeGen.Lisp.Optimizer.Unused
  ( removeCodeAfterReturnStatements
  , removeUnusedArg
  , removeUndefinedApp
  ) where

import Language.PureScript.CodeGen.Lisp.AST
import Language.PureScript.CodeGen.Lisp.Optimizer.Common

import qualified Language.PureScript.Constants as C

removeCodeAfterReturnStatements :: Lisp -> Lisp
removeCodeAfterReturnStatements = everywhereOnLisp (removeFromBlock go)
  where
  go :: [Lisp] -> [Lisp]
  go lisps | not (any isLispReturn lisps) = lisps
         | otherwise = let (body, ret : _) = break isLispReturn lisps in body ++ [ret]
  isLispReturn (LispReturn _) = True
  isLispReturn _ = False

removeUnusedArg :: Lisp -> Lisp
removeUnusedArg = everywhereOnLisp convert
  where
  convert (LispFunction name [arg] body) | arg == C.__unused = LispFunction name [] body
  convert lisp = lisp

removeUndefinedApp :: Lisp -> Lisp
removeUndefinedApp = everywhereOnLisp convert
  where
  convert (LispApp fn [LispVar arg]) | arg == C.undefined = LispApp fn []
  convert lisp = lisp
