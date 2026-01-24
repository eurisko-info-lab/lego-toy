/-
  Generated from Rosetta IR
  Module: Lego
-/

inductive term where

  deriving Repr, BEq

inductive env where

  deriving Repr, BEq

inductive binding where

  deriving Repr, BEq

inductive rule where

  deriving Repr, BEq

inductive iso where

  deriving Repr, BEq

inductive symbol where

  deriving Repr, BEq

inductive production where

  deriving Repr, BEq

inductive grammar where

  deriving Repr, BEq

def atomExpand : Expr → Option Expr
  | (.atom name) => some (.con name)
  | _ => none

def matchVar : Expr → Option Expr
  | (.match (.var name) t) => some (.if (.startsWith name (.lit (.string "$"))) (.env (.con ( (.var $ name) (.var $ t) ))) (.if (.eq (.var name) t) .env .fail))
  | _ => none

def matchLit : Expr → Option Expr
  | (.match (.lit a) (.lit b)) => some (.if (.eq a b) .env .fail)
  | _ => none

def matchCon : Expr → Option Expr
  | (.match (.con n1 args1) (.con n2 args2)) => some (.if (.eq n1 n2) (.matchList args1 args2) .fail)
  | _ => none

def matchFail : Expr → Option Expr
  | (.match p t) => some .fail
  | _ => none

def matchListNil : Expr → Option Expr
  | (.matchList (.unit ( )) (.unit ( ))) => some .env
  | _ => none

def matchListCons : Expr → Option Expr
  | (.matchList (.con ( (.var $ p) (.var $ ps) )) (.con ( (.var $ t) (.var $ ts) ))) => some (.merge (.match p t) (.matchList ps ts))
  | _ => none

def mergeEnvs : Expr → Option Expr
  | (.merge (.env bs1) (.env bs2)) => some (.env bs1 bs2)
  | _ => none

def mergeFail : Expr → Option Expr
  | (.merge .fail e) => some .fail
  | _ => none

def substVar : Expr → Option Expr
  | (.subst (.var name) (.env bindings)) => some (.lookup name bindings)
  | _ => none

def substLit : Expr → Option Expr
  | (.subst (.lit s) env) => some (.lit s)
  | _ => none

def substCon : Expr → Option Expr
  | (.subst (.con name args) env) => some (.con name (.mapSubst args env))
  | _ => none

def mapSubstNil : Expr → Option Expr
  | (.mapSubst (.unit ( )) env) => some (.unit ( ))
  | _ => none

def mapSubstCons : Expr → Option Expr
  | (.mapSubst (.con ( (.var $ t) (.var $ ts) )) env) => some (.con ( (.app ( (.con subst) (.var $ t) (.var $ env) )) (.con ( mapSubst (.var $ ts) (.var $ env) )) ))
  | _ => none

def lookupHit : Expr → Option Expr
  | (.lookup name (.app ( ( name val ) rest ))) => some val
  | _ => none

def lookupMiss : Expr → Option Expr
  | (.lookup name (.app ( ( other val ) rest ))) => some (.lookup name rest)
  | _ => none

def lookupFail : Expr → Option Expr
  | (.lookup name (.unit ( ))) => some (.var name)
  | _ => none

def applyRule : Expr → Option Expr
  | (.apply (.rule name pat tmpl) t) => some (.case (.match pat t) (.env bs) (.subst tmpl (.env bs)) .fail .fail)
  | _ => none

def tryFirst : Expr → Option Expr
  | (.tryRules (.app ( ( rule n p t ) rest )) term) => some (.case (.apply (.rule n p t) term) .fail (.tryRules rest term) result result)
  | _ => none

def tryEmpty : Expr → Option Expr
  | (.tryRules (.unit ( )) term) => some .fail
  | _ => none

def normalizeStep : Expr → Option Expr
  | (.normalize rules t) => some (.letIn ( let $ t' = (.normalizeOnce rules t) in (.if (.eq t t') t (.normalize rules t')) ))
  | _ => none

def normalizeOnce : Expr → Option Expr
  | (.normalizeOnce rules t) => some (.case (.tryRules rules t) .fail (.normalizeChildren rules t) result result)
  | _ => none

def normalizeChildrenVar : Expr → Option Expr
  | (.normalizeChildren rules (.var x)) => some (.var x)
  | _ => none

def normalizeChildrenLit : Expr → Option Expr
  | (.normalizeChildren rules (.lit s)) => some (.lit s)
  | _ => none

def normalizeChildrenCon : Expr → Option Expr
  | (.normalizeChildren rules (.con name args)) => some (.con name (.mapNormalize rules args))
  | _ => none

def mapNormalizeNil : Expr → Option Expr
  | (.mapNormalize rules (.unit ( ))) => some (.unit ( ))
  | _ => none

def mapNormalizeCons : Expr → Option Expr
  | (.mapNormalize rules (.con ( (.var $ t) (.var $ ts) ))) => some (.con ( (.app ( (.con normalizeOnce) (.var $ rules) (.var $ t) )) (.con ( mapNormalize (.var $ rules) (.var $ ts) )) ))
  | _ => none

def isoId : Expr → Option Expr
  | .isoId => some (.iso (.con ( (.var $ x) (.con ( some (.var $ x) )) )) (.con ( (.var $ x) (.con ( some (.var $ x) )) )))
  | _ => none

def isoComp : Expr → Option Expr
  | (.isoComp (.iso fwd1 bwd1) (.iso fwd2 bwd2)) => some (.iso (.con ( (.var $ a) (.con ( bind (.con ( apply (.var $ fwd1) (.var $ a) )) (.var $ b) (.con ( apply (.var $ fwd2) (.var $ b) )) )) )) (.con ( (.var $ c) (.con ( bind (.con ( apply (.var $ bwd2) (.var $ c) )) (.var $ b) (.con ( apply (.var $ bwd1) (.var $ b) )) )) )))
  | _ => none

def isoSym : Expr → Option Expr
  | (.isoSym (.iso fwd bwd)) => some (.iso bwd fwd)
  | _ => none

def stringEq : Expr → Option Expr
  | (.eq (.lit a) (.lit b)) => some (.eqStrings a b)
  | _ => none

def startsWith : Expr → Option Expr
  | (.startsWith s prefix) => some (.startsWithBuiltin s prefix)
  | _ => none

def ifTrue : Expr → Option Expr
  | (.if .true then_ else_) => some then_
  | _ => none

def ifFalse : Expr → Option Expr
  | (.if .false then_ else_) => some else_
  | _ => none

def bindSome : Expr → Option Expr
  | (.bind (.some x) var body) => some (.subst body (.env (.con ( (.var $ var) (.var $ x) ))))
  | _ => none

def bindNone : Expr → Option Expr
  | (.bind .none var body) => some .none
  | _ => none

def caseMatch : Expr → Option Expr
  | (.case scrutinee pat1 body1 rest) => some (.case (.match pat1 scrutinee) (.env bs) (.subst body1 (.env bs)) .fail (.case scrutinee rest))
  | _ => none

def caseEmpty : Expr → Option Expr
  | (.case scrutinee) => some (.stuck scrutinee)
  | _ => none

def mapNil : Expr → Option Expr
  | (.map f (.unit ( ))) => some (.unit ( ))
  | _ => none

def mapCons : Expr → Option Expr
  | (.map f (.con ( (.var $ x) (.var $ xs) ))) => some (.con ( (.app ( (.con apply) (.var $ f) (.var $ x) )) (.con ( map (.var $ f) (.var $ xs) )) ))
  | _ => none

def foldNil : Expr → Option Expr
  | (.fold f acc (.unit ( ))) => some acc
  | _ => none

def foldCons : Expr → Option Expr
  | (.fold f acc (.con ( (.var $ x) (.var $ xs) ))) => some (.fold f (.apply f acc x) xs)
  | _ => none

def appendNil : Expr → Option Expr
  | (.append (.unit ( )) ys) => some ys
  | _ => none

def appendCons : Expr → Option Expr
  | (.append (.con ( (.var $ x) (.var $ xs) )) ys) => some (.con ( (.var $ x) (.con ( append (.var $ xs) (.var $ ys) )) ))
  | _ => none

def lengthNil : Expr → Option Expr
  | (.length (.unit ( ))) => some .zero
  | _ => none

def lengthCons : Expr → Option Expr
  | (.length (.con ( (.var $ x) (.var $ xs) ))) => some (.succ (.length xs))
  | _ => none
