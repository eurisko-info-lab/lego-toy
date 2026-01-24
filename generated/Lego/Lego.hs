{-
  Generated from Rosetta IR
  Module: Lego
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Lego where

data term where

  deriving (Show, Eq)

data env where

  deriving (Show, Eq)

data binding where

  deriving (Show, Eq)

data rule where

  deriving (Show, Eq)

data iso where

  deriving (Show, Eq)

data symbol where

  deriving (Show, Eq)

data production where

  deriving (Show, Eq)

data grammar where

  deriving (Show, Eq)

atomExpand :: Expr -> Maybe Expr
atomExpand (Atom name) = Just ((Con name))
atomExpand _ = Nothing

matchVar :: Expr -> Maybe Expr
matchVar (Match (Var name) t) = Just ((If (StartsWith name (Lit (String "$"))) (Env (Con ( (Var $ name) (Var $ t) ))) (If (Eq (Var name) t) Env Fail)))
matchVar _ = Nothing

matchLit :: Expr -> Maybe Expr
matchLit (Match (Lit a) (Lit b)) = Just ((If (Eq a b) Env Fail))
matchLit _ = Nothing

matchCon :: Expr -> Maybe Expr
matchCon (Match (Con n1 args1) (Con n2 args2)) = Just ((If (Eq n1 n2) (MatchList args1 args2) Fail))
matchCon _ = Nothing

matchFail :: Expr -> Maybe Expr
matchFail (Match p t) = Just (Fail)
matchFail _ = Nothing

matchListNil :: Expr -> Maybe Expr
matchListNil (MatchList (Unit ( )) (Unit ( ))) = Just (Env)
matchListNil _ = Nothing

matchListCons :: Expr -> Maybe Expr
matchListCons (MatchList (Con ( (Var $ p) (Var $ ps) )) (Con ( (Var $ t) (Var $ ts) ))) = Just ((Merge (Match p t) (MatchList ps ts)))
matchListCons _ = Nothing

mergeEnvs :: Expr -> Maybe Expr
mergeEnvs (Merge (Env bs1) (Env bs2)) = Just ((Env bs1 bs2))
mergeEnvs _ = Nothing

mergeFail :: Expr -> Maybe Expr
mergeFail (Merge Fail e) = Just (Fail)
mergeFail _ = Nothing

substVar :: Expr -> Maybe Expr
substVar (Subst (Var name) (Env bindings)) = Just ((Lookup name bindings))
substVar _ = Nothing

substLit :: Expr -> Maybe Expr
substLit (Subst (Lit s) env) = Just ((Lit s))
substLit _ = Nothing

substCon :: Expr -> Maybe Expr
substCon (Subst (Con name args) env) = Just ((Con name (MapSubst args env)))
substCon _ = Nothing

mapSubstNil :: Expr -> Maybe Expr
mapSubstNil (MapSubst (Unit ( )) env) = Just ((Unit ( )))
mapSubstNil _ = Nothing

mapSubstCons :: Expr -> Maybe Expr
mapSubstCons (MapSubst (Con ( (Var $ t) (Var $ ts) )) env) = Just ((Con ( (App ( (Con subst) (Var $ t) (Var $ env) )) (Con ( mapSubst (Var $ ts) (Var $ env) )) )))
mapSubstCons _ = Nothing

lookupHit :: Expr -> Maybe Expr
lookupHit (Lookup name (App ( ( name val ) rest ))) = Just (val)
lookupHit _ = Nothing

lookupMiss :: Expr -> Maybe Expr
lookupMiss (Lookup name (App ( ( other val ) rest ))) = Just ((Lookup name rest))
lookupMiss _ = Nothing

lookupFail :: Expr -> Maybe Expr
lookupFail (Lookup name (Unit ( ))) = Just ((Var name))
lookupFail _ = Nothing

applyRule :: Expr -> Maybe Expr
applyRule (Apply (Rule name pat tmpl) t) = Just ((Case (Match pat t) (Env bs) (Subst tmpl (Env bs)) Fail Fail))
applyRule _ = Nothing

tryFirst :: Expr -> Maybe Expr
tryFirst (TryRules (App ( ( rule n p t ) rest )) term) = Just ((Case (Apply (Rule n p t) term) Fail (TryRules rest term) result result))
tryFirst _ = Nothing

tryEmpty :: Expr -> Maybe Expr
tryEmpty (TryRules (Unit ( )) term) = Just (Fail)
tryEmpty _ = Nothing

normalizeStep :: Expr -> Maybe Expr
normalizeStep (Normalize rules t) = Just ((LetIn ( let $ t' = (NormalizeOnce rules t) in (If (Eq t t') t (Normalize rules t')) )))
normalizeStep _ = Nothing

normalizeOnce :: Expr -> Maybe Expr
normalizeOnce (NormalizeOnce rules t) = Just ((Case (TryRules rules t) Fail (NormalizeChildren rules t) result result))
normalizeOnce _ = Nothing

normalizeChildrenVar :: Expr -> Maybe Expr
normalizeChildrenVar (NormalizeChildren rules (Var x)) = Just ((Var x))
normalizeChildrenVar _ = Nothing

normalizeChildrenLit :: Expr -> Maybe Expr
normalizeChildrenLit (NormalizeChildren rules (Lit s)) = Just ((Lit s))
normalizeChildrenLit _ = Nothing

normalizeChildrenCon :: Expr -> Maybe Expr
normalizeChildrenCon (NormalizeChildren rules (Con name args)) = Just ((Con name (MapNormalize rules args)))
normalizeChildrenCon _ = Nothing

mapNormalizeNil :: Expr -> Maybe Expr
mapNormalizeNil (MapNormalize rules (Unit ( ))) = Just ((Unit ( )))
mapNormalizeNil _ = Nothing

mapNormalizeCons :: Expr -> Maybe Expr
mapNormalizeCons (MapNormalize rules (Con ( (Var $ t) (Var $ ts) ))) = Just ((Con ( (App ( (Con normalizeOnce) (Var $ rules) (Var $ t) )) (Con ( mapNormalize (Var $ rules) (Var $ ts) )) )))
mapNormalizeCons _ = Nothing

isoId :: Expr -> Maybe Expr
isoId (IsoId) = Just ((Iso (Con ( (Var $ x) (Con ( some (Var $ x) )) )) (Con ( (Var $ x) (Con ( some (Var $ x) )) ))))
isoId _ = Nothing

isoComp :: Expr -> Maybe Expr
isoComp (IsoComp (Iso fwd1 bwd1) (Iso fwd2 bwd2)) = Just ((Iso (Con ( (Var $ a) (Con ( bind (Con ( apply (Var $ fwd1) (Var $ a) )) (Var $ b) (Con ( apply (Var $ fwd2) (Var $ b) )) )) )) (Con ( (Var $ c) (Con ( bind (Con ( apply (Var $ bwd2) (Var $ c) )) (Var $ b) (Con ( apply (Var $ bwd1) (Var $ b) )) )) ))))
isoComp _ = Nothing

isoSym :: Expr -> Maybe Expr
isoSym (IsoSym (Iso fwd bwd)) = Just ((Iso bwd fwd))
isoSym _ = Nothing

stringEq :: Expr -> Maybe Expr
stringEq (Eq (Lit a) (Lit b)) = Just ((EqStrings a b))
stringEq _ = Nothing

startsWith :: Expr -> Maybe Expr
startsWith (StartsWith s prefix) = Just ((StartsWithBuiltin s prefix))
startsWith _ = Nothing

ifTrue :: Expr -> Maybe Expr
ifTrue (If True then_ else_) = Just (then_)
ifTrue _ = Nothing

ifFalse :: Expr -> Maybe Expr
ifFalse (If False then_ else_) = Just (else_)
ifFalse _ = Nothing

bindSome :: Expr -> Maybe Expr
bindSome (Bind (Some x) var body) = Just ((Subst body (Env (Con ( (Var $ var) (Var $ x) )))))
bindSome _ = Nothing

bindNone :: Expr -> Maybe Expr
bindNone (Bind None var body) = Just (None)
bindNone _ = Nothing

caseMatch :: Expr -> Maybe Expr
caseMatch (Case scrutinee pat1 body1 rest) = Just ((Case (Match pat1 scrutinee) (Env bs) (Subst body1 (Env bs)) Fail (Case scrutinee rest)))
caseMatch _ = Nothing

caseEmpty :: Expr -> Maybe Expr
caseEmpty (Case scrutinee) = Just ((Stuck scrutinee))
caseEmpty _ = Nothing

mapNil :: Expr -> Maybe Expr
mapNil (Map f (Unit ( ))) = Just ((Unit ( )))
mapNil _ = Nothing

mapCons :: Expr -> Maybe Expr
mapCons (Map f (Con ( (Var $ x) (Var $ xs) ))) = Just ((Con ( (App ( (Con apply) (Var $ f) (Var $ x) )) (Con ( map (Var $ f) (Var $ xs) )) )))
mapCons _ = Nothing

foldNil :: Expr -> Maybe Expr
foldNil (Fold f acc (Unit ( ))) = Just (acc)
foldNil _ = Nothing

foldCons :: Expr -> Maybe Expr
foldCons (Fold f acc (Con ( (Var $ x) (Var $ xs) ))) = Just ((Fold f (Apply f acc x) xs))
foldCons _ = Nothing

appendNil :: Expr -> Maybe Expr
appendNil (Append (Unit ( )) ys) = Just (ys)
appendNil _ = Nothing

appendCons :: Expr -> Maybe Expr
appendCons (Append (Con ( (Var $ x) (Var $ xs) )) ys) = Just ((Con ( (Var $ x) (Con ( append (Var $ xs) (Var $ ys) )) )))
appendCons _ = Nothing

lengthNil :: Expr -> Maybe Expr
lengthNil (Length (Unit ( ))) = Just (Zero)
lengthNil _ = Nothing

lengthCons :: Expr -> Maybe Expr
lengthCons (Length (Con ( (Var $ x) (Var $ xs) ))) = Just ((Succ (Length xs)))
lengthCons _ = Nothing
