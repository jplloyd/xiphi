-- | Tying scope checking and type checking together by using checking problems
module CheckHub where

import Surface
import Core
import ScopeChecking
import Elaboration
import Internal
import Types
import DList

import Control.Applicative
import Prelude hiding (log)

-- Wrapping a type checking problem
-- the expressions of the tuple list are turned into
-- constants (in order) and have to be fully type checked
data ChkProb = ChkProb {constants :: [(N,SExpr)], term ::  SExpr, typ :: SExpr}

-- would be easier to work with...
data ChkProb' = ChkProb' [(N,Type)] SExpr Type

-- Don't look at it right now
process :: ChkProb -> IO ()
process prob = do
    let result = processProb prob
    either (\err -> putStrLn "A scope checking error occured" >> putStrLn err) (handle) result
  where handle (log,xi,expr,result) = do
          putStrLn (fromDList log)
          either (\err -> putStrLn "An elaboration error occured" >> putStrLn err) (handle' expr) result
          putStrLn " == Meta Context =="
          print xi
        handle' expr (posts,typ',trm) = do
          printSurface (constants prob) (typ prob) (term prob)
          printCore expr
          putStrLn " == Postulates == "
          putStrLn $ concatMap printPost posts
          putStrLn " == Elab type == "
          print typ'
          putStrLn " == Elab term == "
          print trm
        printPost (n,typ') = n ++ " : " ++ show typ' ++ "\n"
        printSurface psts typ' trm = do
          putStrLn "-- surface postulates"
          putStrLn $ concatMap printPost psts
          putStrLn "-- surface type"
          print typ'
          putStrLn "-- surface term"
          print trm
        printCore (psts,typ',trm) = do
          putStrLn "-- core postulates"
          putStrLn $ concatMap printPost psts
          putStrLn "-- core type"
          print typ'
          putStrLn "-- core term"
          print trm

-- remaining-- - correctness of subst comp implementation
-- - options for printing different logs - store all logs up until possible errors (tedious)

processProb :: ChkProb -> Either Error (Log, Xi, ([(Name,CExpr)], CExpr,CExpr), Either Error ([(Name,Type)],Type,Term))
processProb prob = go (unzip (constants prob)) (typ prob) (term prob)
  where go (ns,pstS) typS trmS = ccurr ns elabProblem <$> snd (scopecheckProb pstS typS trmS)
        ccurr ns f (a,b,c) = f (zip ns a) b c
