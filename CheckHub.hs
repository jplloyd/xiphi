-- | Tying scope checking and type checking together by using checking problems
module CheckHub where

import Surface
import ScopeChecking
import Elaboration
import Internal
import Types


import Control.Applicative
import Prelude hiding (log)

-- Wrapping a type checking problem
-- the expressions of the tuple list are turned into
-- constants (in order) and have to be fully type checked
data ChkProb = ChkProb {constants :: [(N,SExpr)], term ::  SExpr, typ :: SExpr}

-- would be easier to work with...
data ChkProb' = ChkProb' [(N,Type)] SExpr Type

process :: ChkProb -> IO ()
process prob = do
    let result = processProb prob
    either (\err -> putStrLn "A scope checking error occured" >> putStrLn err) (handle) result
  where handle (log,xi,result) = do
          either (\err -> putStrLn "An elaboration error occured" >> putStrLn err) (handle') result
          putStrLn " == Meta Context =="
          print xi
        handle' (posts,typ',trm) = do
          putStrLn " == Postulates == "
          putStrLn $ concatMap printPost posts
          putStrLn " == Elab type == "
          print typ'
          putStrLn " == Elab term == "
          print trm
        printPost (n,typ') = n ++ " : " ++ show typ' ++ "\n"

-- remaining-- - correctness of subst comp implementation
-- - options for printing different logs - store all logs up until possible errors (tedious)

processProb :: ChkProb -> Either Error (Log, Xi, Either Error ([(Name,Type)],Type,Term))
processProb prob = go (unzip (constants prob)) (typ prob) (term prob)
  where go (ns,pstS) typS trmS =  elabProblem <$> zip ns <$> mapM ssnd pstS <*> ssnd typS <*> ssnd trmS
        ssnd = snd . scopecheck -- we don't care about the scope checking logs
