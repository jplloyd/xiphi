module Elaboration where

import Core

import Control.Monad.State

import Internal(Xi(..), Gamma(..), Term)

import qualified Internal as I




type ElabM = State Xi


type Type = Term

elaborate :: Expr -> Term -> Term
elaborate e t = evalState (check (Gamma []) e t) Empty

check :: Gamma -> Expr -> Type -> ElabM Term
check g e t = do
  (typ,term) <- infer g e
  genEq g typ term t

infer :: Gamma -> Expr -> ElabM (Type, Term)
infer = undefined

genEq :: Gamma -> Term -> Type -> Type -> ElabM Term
genEq = undefined
