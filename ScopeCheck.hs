module ScopeCheck where

import Surface as S
import qualified Core as C

data CBind = CB (C.Expr,N)

data Context = Context {fCounter::Int, constants :: [(C.N,C.Expr)], binds :: [CBind]}

emptyC :: Context 
emptyC = Context 0 [] []

inc :: Context -> Context
inc c = c{fCounter=fCounter c + 1}

addBind :: CBind -> Context -> Context
addBind b c = c{binds=b : binds c}

addBinds  :: [CBind] -> Context -> Context
addBinds bs c = c{binds=bs ++ binds c}


scopecheck :: Context -> Expr -> Maybe C.Expr
scopecheck c _e = case _e of
  Var n -> substitute c n
  Cns n -> return $ C.Cns n
  Set -> return C.Set
  Fun impl (Bind (n,e')) e -> do
    sig <- makesig c impl
    let bs = bindsOf impl
    let r = "r" ++ (show . fCounter $ c)
    let c' = addBinds (map (\f -> CB (C.Proj (C.Var r) f, f)) bs) (inc c)
    e'' <- scopecheck c' e'  
    e2 <- scopecheck (addBind (CB (e'',n)) c' ) e
    return $ C.Fun (C.Bind r sig) (C.Fun (C.Bind n e'') e2)
  App e impl e' -> do
    e1 <- scopecheck c e
    e2 <- scopecheck c e'
    estr <- makestruct c impl
    return $ C.App (C.App e1 estr) e2
  Lam impls expl e -> do -- It doesn't make any sense to allow the explicit binding to shadow.
    lsig <- makelsig impls
    let r = "r" ++ show (fCounter c)
    let c' = addBinds ((CB (C.Var expl, expl)) : map (\f -> CB (C.Proj (C.Var r) f, f)) impls) (inc c)
    e1 <- scopecheck c' e
    return $ C.Lam (C.Bind "r" lsig) (C.Lam (C.Bind expl C.WCrd) e1)
  Wld -> return C.WCrd


substitute :: Context -> N -> Maybe C.Expr
substitute c n = repl (binds c)
  where repl [] = Nothing
        repl (CB (e,n'):bs) = if n' == n then Just e else repl bs

makelsig :: [N] -> Maybe C.Expr
makelsig ns = if unique ns then return (C.LSig ns) else Nothing

unique :: Eq a => [a] -> Bool
unique [] = True
unique (a : as) = a `notElem` as && unique as

makesig :: Context -> [Bind] -> Maybe C.Expr
makesig c bs | unique . bindsOf $ bs = C.Sig `fmap` go c bs
             | otherwise = Nothing
  where go c' [] = Just []
        go c' (Bind (n,e):bs) = do
          e' <- scopecheck c' e
          let c'' = (addBind (CB (C.Var n,n)) c')
          bs' <- go c'' bs
          return $ C.Bind n e' : bs'

makestruct :: Context -> [Assign] -> Maybe C.Expr
makestruct c as = C.EStr `fmap` go [] as
  where go _     []  = Just []
        go taken ass = case ass of
          (Named n e) : as' -> if n `elem` taken then Nothing else do
            e' <- scopecheck c e
            as'' <- go (n:taken) as'
            return (C.Named n e' : as'')
          (Pos e) : as' -> do
            e' <- scopecheck c e
            as'' <- go taken as'
            return (C.Pos e' : as'')
            
bindsOf :: [Bind] -> [N] 
bindsOf = map (\(Bind (n,_)) -> n)
