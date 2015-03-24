-- | Tying scope checking and type checking together by using checking problems
module CheckHub where

import Surface
import Core
import ScopeChecking
import Derivation
import ElabSpec
import Internal
import Types
import LatexPrint

import Data.List
import Control.Applicative
import Prelude hiding (log)

-- Wrapping a type checking problem
-- the expressions of the tuple list are turned into
-- constants (in order) and have to be fully type checked
data ChkProb = ChkProb {constants :: [(Name,SExpr)], term ::  SExpr, typ :: SExpr}

-- So this is what we want to have: a set of postulates, an expression and a type in Surface,
-- and a set of optional postulate-replacements in Internal, providing the ability to instantiate things manually
-- the type in Surface should also be replaceable eventually
data OptChkProb = OCP {posts :: [((Name,SExpr), Maybe Type)],
                       termS :: SExpr, 
                       typeS :: (SExpr,Maybe Type)}

printDerivation :: [Rule] -> IO ()
printDerivation rs = do
  let log = unlines (intersperse "\\\\" $ map (show . lP) (aggregate . compact $ rs))
  writeFile "/home/jesper/dev/masterthesisproject/report/problems/derivlog.tex" log


-- Don't look at it right now
process :: ChkProb -> IO ()
process prob = do
    let result = processProb prob
    either (\err -> putStrLn "A scope checking error occured" >> putStrLn err) handle result
  where handle (log,xi,expr,result) = do
          printDerivation log
          either (\err -> putStrLn "An elaboration error occured" >> putStrLn err) (handle' expr) result
          putStrLn " == Meta Context =="
          print xi
        handle' expr (posts',typ',trm) = do
          printSurface (constants prob) (typ prob) (term prob)
          printCore expr
          putStrLn " == Postulates == "
          putStrLn $ concatMap printPost' posts'
          putStrLn " == Elab type == "
          putStrLn . showTerm $ typ'
          putStrLn " == Elab term == "
          putStrLn . showTerm $ trm

printPost (n,typ') = n ++ " : " ++ show typ' ++ "\n"

printPost' (n,typ') = n ++ " : " ++ showTerm typ' ++ "\n" ++ n ++ " : " ++ show typ' ++ "\n"

printLPost (n,typ') = n ++ " : " ++ latexTerm typ' ++ "\n"

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

processProb :: ChkProb -> Either Error ([Rule], Xi, ([(Name,CExpr)], CExpr,CExpr), Either Error ([(Name,Type)],Type,Term))
processProb prob = go (unzip (constants prob)) (typ prob) (term prob)
  where go (ns,pstS) typS trmS = ccurr ns elabProblem <$> snd (scopecheckProb pstS typS trmS)
        ccurr ns f (a,b,c) = f (zip ns a) b c
