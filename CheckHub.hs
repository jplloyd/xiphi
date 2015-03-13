-- | Tying scope checking and type checking together by using checking problems
module CheckHub where

import Surface
import Core
import ScopeChecking
import Elaboration
import Internal
import Types
import DList

import Control.Arrow
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


-- Don't look at it right now
process :: ChkProb -> IO ()
process prob = do
    let result = processProb prob
    either (\err -> putStrLn "A scope checking error occured" >> putStrLn err) handle result
  where handle (log,xi,expr,result) = do
          putStrLn (fromDList log)
          either (\err -> putStrLn "An elaboration error occured" >> putStrLn err) (handle' expr) result
          putStrLn " == Meta Context =="
          print xi
        handle' expr (posts,typ',trm) = do
          printSurface (constants prob) (typ prob) (term prob)
          printCore expr
          putStrLn " == Postulates == "
          putStrLn $ concatMap printPost' posts
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

-- (Log, Xi, ([(Name,CExpr)], CExpr,CExpr), Either Error ([(Name,Type)],Type,Term))
-- Temporary, allegedly
processOpt :: OptChkProb -> IO ()
processOpt prob = do
    let result = processOptProb prob
    either (\err -> putStrLn "A scope checking error occured" >> putStrLn err) handle result
  where handle (log,xi,expr,result) = do
          putStrLn (fromDList log)
          printSurface (map fst (posts prob)) (typeS prob) (termS prob)
          printCore expr
          either (\err -> putStrLn "An elaboration error occured" >> putStrLn err) (handle' expr) result
          putStrLn " == Meta Context =="
          print xi
          putStrLn " == Latex constraints =="
          putStrLn $ unlines . map (latexConstraint . constraint) $ constraints xi
        handle' :: ([(Name,CExpr)], CExpr,CExpr) -> ([(Name,Type)],Type,Term) -> IO ()
        handle' expr (posts,typ',trm) = do
          putStrLn " == Postulates == "
          putStrLn $ concatMap printPost' posts
          putStrLn " == Latex Posts == "
          putStrLn $ concatMap printLPost posts
          putStrLn " == Elab type == "
          putStrLn . showTerm $ typ'
          putStrLn " == Elab term == "
          putStrLn . showTerm $ trm


processProb :: ChkProb -> Either Error (Log, Xi, ([(Name,CExpr)], CExpr,CExpr), Either Error ([(Name,Type)],Type,Term))
processProb prob = go (unzip (constants prob)) (typ prob) (term prob)
  where go (ns,pstS) typS trmS = ccurr ns elabProblem <$> snd (scopecheckProb pstS typS trmS)
        ccurr ns f (a,b,c) = f (zip ns a) b c


processOptProb :: OptChkProb -> Either Error (Log, Xi, ([(Name,CExpr)], CExpr,CExpr), Either Error ([(Name,Type)],Type,Term))
processOptProb prob = go (first unzip $ unzip (posts prob)) (typeS prob) (termS prob)
   where go ((ns,exps),alts) (typS,typI) trmS = elabProb ns alts typI <$> snd (scopecheckProb exps typS trmS)
         elabProb ns alts typI (exprs,typC,trmC) = elabOptProblem (zip (zip ns exprs) alts) trmC (typC,typI)
