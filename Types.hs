module Types where

import DList

import Control.Monad.Except
import Control.Monad.Trans.Writer

type Error = String
type Log = DList Char

-- Error handling
type ErrT = ExceptT Error

-- Scope checking logging
type LogT = WriterT Log

