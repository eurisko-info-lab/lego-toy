inductive Iso  (a : Type) (b : Type) where
  | MkIso : ( a → ( Option b ) ) → ( b → ( Option a ) ) → Iso a b
  

inductive Term where
  | Var : String → Term
  | Lit : String → Term
  | Con : String → ( List Term ) → Term
  deriving BEq, Repr

inductive AST  (a : Type) where
  | MkAST : ( String → a ) → ( String → a ) → ( String → ( List a ) → a ) → ( AST a )
  

inductive PieceLevel where
  | TokenLevel : PieceLevel
  | SyntaxLevel : PieceLevel
  deriving BEq, Repr

inductive Rule where
  | MkRule : String → Term → Term → Rule
  deriving BEq, Repr

inductive TypeRule where
  | MkTypeRule : String → Term → Term → TypeRule
  deriving BEq, Repr

inductive GrammarExpr where
  | GEmpty : GrammarExpr
  | GLit : String → GrammarExpr
  | GRef : String → GrammarExpr
  | GSeq : GrammarExpr → GrammarExpr → GrammarExpr
  | GAlt : GrammarExpr → GrammarExpr → GrammarExpr
  | GStar : GrammarExpr → GrammarExpr
  | GPlus : GrammarExpr → GrammarExpr
  | GOpt : GrammarExpr → GrammarExpr
  | GNot : GrammarExpr → GrammarExpr
  | GAnd : GrammarExpr → GrammarExpr
  | GCon : String → GrammarExpr → GrammarExpr
  deriving BEq, Repr

inductive GrammarProduction where
  | MkGrammarProduction : String → GrammarExpr → String → GrammarProduction
  deriving BEq, Repr

inductive Piece where
  | MkPiece : String → PieceLevel → ( List GrammarProduction ) → ( List Rule ) → ( List TypeRule ) → Piece
  deriving BEq, Repr

inductive Language where
  | MkLanguage : String → ( List Piece ) → Language
  deriving BEq, Repr

inductive SourceLoc where
  | MkSourceLoc : String → Int → Int → Int → SourceLoc
  | UnknownLoc : SourceLoc
  deriving BEq, Repr

inductive Severity where
  | SevError : Severity
  | SevWarning : Severity
  | SevInfo : Severity
  deriving BEq, Repr

inductive Binding where
  | MkBinding : String → Term → ( Option Term ) → SourceLoc → Binding
  deriving BEq, Repr

inductive TypeError where
  | MkTypeError : String → SourceLoc → Severity → ( Option Term ) → ( Option Term ) → ( List Binding ) → TypeError
  deriving BEq, Repr

inductive EvalResult where
  | EvalOk : Term → ( List TypeError ) → EvalResult
  | EvalFailed : ( List TypeError ) → EvalResult
  deriving BEq, Repr

inductive Context where
  | EmptyContext : Context
  | ContextCons : Binding → Context → Context
  deriving BEq, Repr

inductive VarContext where
  | EmptyVarContext : VarContext
  | VarContextCons : String → VarContext → VarContext
  deriving BEq, Repr

inductive EvalEnv where
  | MkEvalEnv : AttrEnv → Context → VarContext → ( List TypeError ) → SourceLoc → EvalEnv
  deriving BEq, Repr

inductive Mode where
  | Infer : Mode
  | Check : Mode
  deriving BEq, Repr

inductive AttrFlow where
  | Syn : AttrFlow
  | Inh : AttrFlow
  | SynInh : AttrFlow
  deriving BEq, Repr

inductive AttrPath where
  | Empty : AttrPath
  | PathCon : String → AttrPath → AttrPath
  deriving BEq, Repr

inductive AttrRef where
  | MkAttrRef : AttrPath → String → AttrRef
  deriving BEq, Repr

inductive AttrRule where
  | MkAttrRule : String → AttrPath → Term → AttrRule
  deriving BEq, Repr

inductive AttrDef where
  | MkAttrDef : String → AttrFlow → ( Option Term ) → ( List AttrRule ) → AttrDef
  deriving BEq, Repr

inductive AttrEnv where
  | EmptyAttrEnv : AttrEnv
  | AttrEnvCons : AttrPath → String → Term → AttrEnv → AttrEnv
  deriving BEq, Repr

inductive AttrLanguage where
  | MkAttrLanguage : String → ( List GrammarProduction ) → ( List AttrDef ) → AttrLanguage
  deriving BEq, Repr

inductive Token where
  | TokIdent : String → Token
  | TokString : String → Token
  | TokInt : Int → Token
  | TokSym : String → Token
  | TokEOF : Token
  deriving BEq, Repr

inductive ParseState where
  | MkState : ( List Token ) → Int → ParseState
  deriving BEq, Repr

inductive ParseResult where
  | ParseOk : Term → ParseState → ParseResult
  | ParseFail : String → ParseState → ParseResult
  deriving BEq, Repr

inductive PrintResult where
  | PrintOk : ( List Token ) → PrintResult
  | PrintFail : String → PrintResult
  deriving BEq, Repr

inductive Env where
  | EnvEmpty : Env
  | Bind : String → Term → Env → Env
  deriving BEq, Repr

inductive Symbol where
  | Terminal : String → Symbol
  | NonTerminal : String → Symbol
  | Epsilon : Symbol
  deriving BEq, Repr

inductive Production where
  | MkProd : String → ( List Symbol ) → String → Production
  deriving BEq, Repr

inductive Grammar where
  | MkGrammar : ( List Production ) → Grammar
  deriving BEq, Repr

inductive Parser where
  | MkParser : Grammar → ( String → ( Option Term ) ) → Parser
  

inductive Printer where
  | MkPrinter : Grammar → ( Term → ( Option String ) ) → Printer
  

inductive LoadedGrammar where
  | LoadedGrammarMkGrammar : ( List Production ) → ( List Production ) → ( List String ) → String → LoadedGrammar
  deriving BEq, Repr

inductive Runtime where
  | MkRuntime : LoadedGrammar → ( List Rule ) → Runtime
  deriving BEq, Repr

inductive ValidationSeverity where
  | ValError : ValidationSeverity
  | ValWarning : ValidationSeverity
  | ValInfo : ValidationSeverity
  deriving BEq, Repr

inductive ValidationError where
  | UndefinedProduction : String → String → ValidationError
  | DuplicateProduction : String → ValidationError
  | UnboundVariable : String → String → ValidationError
  | CircularImport : String → ValidationError
  | InvalidSyntax : String → String → ValidationError
  deriving BEq, Repr

inductive ValidationWarning where
  | ConflictingRules : String → String → String → ValidationWarning
  | DirectLeftRecursion : String → ValidationWarning
  | IndirectLeftRecursion : ( List String ) → ValidationWarning
  | UnusedProduction : String → ValidationWarning
  | ShadowedProduction : String → String → ValidationWarning
  | AmbiguousGrammar : String → String → ValidationWarning
  | MissingCut : String → String → ValidationWarning
  | RuleCycle : ( List String ) → ValidationWarning
  | UnreachableAlt : String → Int → ValidationWarning
  | RedundantAlt : String → Int → Int → ValidationWarning
  deriving BEq, Repr

inductive ValidationResult where
  | MkValidationResult : ( List ValidationError ) → ( List ValidationWarning ) → ValidationResult
  deriving BEq, Repr

def isoId : Term → Option Term
  | .Con "isoId" [] => some (.Con "MkIso" [.Con "Lam" [.Con "binder" [.Lit "x", .Con "Some" [.Con "x" []]]], .Con "Lam" [.Con "binder" [.Lit "x", .Con "Some" [.Con "x" []]]]])
  | _ => none

def isoComp : Term → Option Term
  | .Con "comp" [.Con "MkIso" [f1, b1], .Con "MkIso" [f2, b2]] => some (.Con "MkIso" [.Con "Lam" [.Con "binder" [.Lit "a", .Con "bind" [.Con "App" [f1, .Con "a" []], .Con "b" [], .Con "App" [f2, .Con "b" []]]]], .Con "Lam" [.Con "binder" [.Lit "c", .Con "bind" [.Con "App" [b2, .Con "c" []], .Con "b" [], .Con "App" [b1, .Con "b" []]]]]])
  | _ => none

def isoSym : Term → Option Term
  | .Con "sym" [.Con "MkIso" [fwd, bwd]] => some (.Con "MkIso" [bwd, fwd])
  | _ => none

def isoForward : Term → Option Term
  | .Con "forward" [.Con "MkIso" [fwd, bwd], x] => some (.Con "App" [fwd, x])
  | _ => none

def isoBackward : Term → Option Term
  | .Con "backward" [.Con "MkIso" [fwd, bwd], x] => some (.Con "App" [bwd, x])
  | _ => none

def isoPar : Term → Option Term
  | .Con "par" [.Con "MkIso" [f1, b1], .Con "MkIso" [f2, b2]] => some (.Con "MkIso" [.Con "Lam" [.Con "binder" [.Lit "p", .Con "bind" [.Con "App" [f1, .Con "Fst" [.Con "p" []]], .Con "x" [], .Con "bind" [.Con "App" [f2, .Con "Snd" [.Con "p" []]], .Con "y" [], .Con "Some" [.Con "Pair" [.Con "x" [], .Con "y" []]]]]]], .Con "Lam" [.Con "binder" [.Lit "p", .Con "bind" [.Con "App" [b1, .Con "Fst" [.Con "p" []]], .Con "x" [], .Con "bind" [.Con "App" [b2, .Con "Snd" [.Con "p" []]], .Con "y" [], .Con "Some" [.Con "Pair" [.Con "x" [], .Con "y" []]]]]]]])
  | _ => none

def isoOrElse : Term → Option Term
  | .Con "orElse" [.Con "MkIso" [f1, b1], .Con "MkIso" [f2, b2]] => some (.Con "MkIso" [.Con "Lam" [.Con "binder" [.Lit "a", .Con "case" [.Con "App" [f1, .Con "a" []], .Con "Some" [.Var "x"], .Con "Some" [.Var "x"], .Con "None" [], .Con "App" [f2, .Con "a" []]]]], .Con "Lam" [.Con "binder" [.Lit "b", .Con "case" [.Con "App" [b1, .Con "b" []], .Con "Some" [.Var "x"], .Con "Some" [.Var "x"], .Con "None" [], .Con "App" [b2, .Con "b" []]]]]])
  | _ => none

def termAtom : Term → Option Term
  | .Con "atom" [s] => some (.Con "Con" [s, .Con "Nil" []])
  | _ => none

def termApp : Term → Option Term
  | .Con "app" [f, args] => some (.Con "Con" [f, args])
  | _ => none

def matchMeta : Term → Option Term
  | .Con "matchPat" [.Con "Var" [name], v_t] => some (.Con "Some" [.Con "Cons" [.Con "Pair" [name, v_t], .Con "Nil" []]])
  | _ => none

def matchVarSame : Term → Option Term
  | .Con "matchPat" [.Con "Var" [name], .Con "Var" [name_0]] => if name_0 == name then some (.Con "Some" [.Con "Nil" []]) else none
  | _ => none

def matchVarDiff : Term → Option Term
  | .Con "matchPat" [.Con "Var" [a], .Con "Var" [b]] => some (.Con "None" [])
  | _ => none

def matchLitSame : Term → Option Term
  | .Con "matchPat" [.Con "Lit" [s], .Con "Lit" [s_0]] => if s_0 == s then some (.Con "Some" [.Con "Nil" []]) else none
  | _ => none

def matchLitDiff : Term → Option Term
  | .Con "matchPat" [.Con "Lit" [a], .Con "Lit" [b]] => some (.Con "None" [])
  | _ => none

def matchConSame : Term → Option Term
  | .Con "matchPat" [.Con "Con" [n, pats], .Con "Con" [n_0, args]] => if n_0 == n then some (.Con "matchArgs" [pats, args]) else none
  | _ => none

def matchConDiff : Term → Option Term
  | .Con "matchPat" [.Con "Con" [n1, pats], .Con "Con" [n2, args]] => some (.Con "None" [])
  | _ => none

def matchArgsNil : Term → Option Term
  | .Con "matchArgs" [.Con "Nil" [], .Con "Nil" []] => some (.Con "Some" [.Con "Nil" []])
  | _ => none

def matchArgsCons : Term → Option Term
  | .Con "matchArgs" [.Con "Cons" [p, ps], .Con "Cons" [a, as]] => some (.Con "merge" [.Con "matchPat" [p, a], .Con "matchArgs" [ps, as]])
  | _ => none

def matchArgsMismatch : Term → Option Term
  | .Con "matchArgs" [ps, as] => some (.Con "None" [])
  | _ => none

def mergeBindings : Term → Option Term
  | .Con "merge" [.Con "Some" [bs1], .Con "Some" [bs2]] => some (.Con "Some" [.Con "append" [bs1, bs2]])
  | _ => none

def mergeFail : Term → Option Term
  | .Con "merge" [.Con "None" [], x] => some (.Con "None" [])
  | _ => none

def substVar : Term → Option Term
  | .Con "subst" [.Con "Var" [name], bindings] => some (.Con "lookup" [name, bindings])
  | _ => none

def substLit : Term → Option Term
  | .Con "subst" [.Con "Lit" [s], bindings] => some (.Con "Lit" [s])
  | _ => none

def substCon : Term → Option Term
  | .Con "subst" [.Con "Con" [n, args], bindings] => some (.Con "Con" [n, .Con "map" [.Con "Lam" [.Con "binder" [.Lit "t", .Con "subst" [.Con "t" [], bindings]]], args]])
  | _ => none

def lookupHit : Term → Option Term
  | .Con "lookup" [name, .Con "Cons" [.Con "Pair" [name_0, val], rest]] => if name_0 == name then some (val) else none
  | _ => none

def lookupMiss : Term → Option Term
  | .Con "lookup" [name, .Con "Cons" [.Con "Pair" [other, val], rest]] => some (.Con "lookup" [name, rest])
  | _ => none

def lookupEmpty : Term → Option Term
  | .Con "lookup" [name, .Con "Nil" []] => some (.Con "Var" [name])
  | _ => none

def astVar : Term → Option Term
  | .Con "astVar" [.Con "MkAST" [var, lit, con], s] => some (.Con "App" [var, s])
  | _ => none

def astLit : Term → Option Term
  | .Con "astLit" [.Con "MkAST" [var, lit, con], s] => some (.Con "App" [lit, s])
  | _ => none

def astCon : Term → Option Term
  | .Con "astCon" [.Con "MkAST" [var, lit, con], name, args] => some (.Con "App" [.Con "App" [con, name], args])
  | _ => none

def defaultAST : Term → Option Term
  | .Con "defaultAST" [] => some (.Con "MkAST" [.Con "Var" [], .Con "Lit" [], .Con "Con" []])
  | _ => none

def languageName : Term → Option Term
  | .Con "languageName" [.Con "MkLanguage" [name, pieces]] => some (name)
  | _ => none

def languagePieces : Term → Option Term
  | .Con "languagePieces" [.Con "MkLanguage" [name, pieces]] => some (pieces)
  | _ => none

def languageAllGrammar : Term → Option Term
  | .Con "languageAllGrammar" [.Con "MkLanguage" [name, pieces]] => some (.Con "flatMap" [.Con "pieceGrammar" [], pieces])
  | _ => none

def languageAllRules : Term → Option Term
  | .Con "languageAllRules" [.Con "MkLanguage" [name, pieces]] => some (.Con "flatMap" [.Con "pieceRules" [], pieces])
  | _ => none

def pieceName : Term → Option Term
  | .Con "pieceName" [.Con "MkPiece" [name, level, grammar, rules, typeRules]] => some (name)
  | _ => none

def pieceLevel : Term → Option Term
  | .Con "pieceLevel" [.Con "MkPiece" [name, level, grammar, rules, typeRules]] => some (level)
  | _ => none

def pieceGrammar : Term → Option Term
  | .Con "pieceGrammar" [.Con "MkPiece" [name, level, grammar, rules, typeRules]] => some (grammar)
  | _ => none

def pieceRules : Term → Option Term
  | .Con "pieceRules" [.Con "MkPiece" [name, level, grammar, rules, typeRules]] => some (rules)
  | _ => none

def pieceTypeRules : Term → Option Term
  | .Con "pieceTypeRules" [.Con "MkPiece" [name, level, grammar, rules, typeRules]] => some (typeRules)
  | _ => none

def ruleName : Term → Option Term
  | .Con "ruleName" [.Con "MkRule" [name, pattern, template]] => some (name)
  | _ => none

def rulePattern : Term → Option Term
  | .Con "rulePattern" [.Con "MkRule" [name, pattern, template]] => some (pattern)
  | _ => none

def ruleTemplate : Term → Option Term
  | .Con "ruleTemplate" [.Con "MkRule" [name, pattern, template]] => some (template)
  | _ => none

def sourceLocToString : Term → Option Term
  | .Con "sourceLocToString" [.Con "MkSourceLoc" [file, line, col, span]] => some (.Con "concat" [.Con "concat" [.Con "concat" [.Con "concat" [file, .Lit "\":\""], .Con "toString" [line]], .Lit "\":\""], .Con "toString" [col]])
  | _ => none

def sourceLocToStringUnknown : Term → Option Term
  | .Con "sourceLocToString" [.Con "UnknownLoc" []] => some (.Lit "\"<unknown>:0:0\"")
  | _ => none

def typeErrorSimple : Term → Option Term
  | .Con "typeErrorSimple" [msg, loc] => some (.Con "MkTypeError" [msg, loc, .Con "SevError" [], .Con "None" [], .Con "None" [], .Con "Nil" []])
  | _ => none

def typeErrorMismatch : Term → Option Term
  | .Con "typeErrorMismatch" [expected, actual, loc] => some (.Con "MkTypeError" [.Lit "\"type mismatch\"", loc, .Con "SevError" [], .Con "Some" [expected], .Con "Some" [actual], .Con "Nil" []])
  | _ => none

def typeErrorUndefined : Term → Option Term
  | .Con "typeErrorUndefined" [name, loc] => some (.Con "MkTypeError" [.Con "concat" [.Lit "\"undefined: \"", name], loc, .Con "SevError" [], .Con "None" [], .Con "None" [], .Con "Nil" []])
  | _ => none

def typeErrorToString : Term → Option Term
  | .Con "typeErrorToString" [.Con "MkTypeError" [msg, loc, sev, exp, act, ctx]] => some (.Con "let" [.Var "sevStr", .Con "match" [sev, .Con "SevError" [], .Lit "\"error\"", .Con "SevWarning" [], .Lit "\"warning\"", .Con "SevInfo" [], .Lit "\"info\""], .Con "let" [.Var "locStr", .Con "sourceLocToString" [loc], .Con "let" [.Var "base", .Con "concat" [.Con "concat" [.Con "concat" [.Var "locStr", .Lit "\": \""], .Var "sevStr"], .Con "concat" [.Lit "\": \"", msg]], .Con "match" [exp, .Con "Some" [.Var "e"], .Con "match" [act, .Con "Some" [.Var "a"], .Con "concat" [.Con "concat" [.Con "concat" [.Var "base", .Lit "\"\\n  expected: \""], .Con "termToString" [.Var "e"]], .Con "concat" [.Lit "\"\\n  actual: \"", .Con "termToString" [.Var "a"]]], .Con "None" [], .Var "base"], .Con "None" [], .Var "base"]]]])
  | _ => none

def evalResultPure : Term → Option Term
  | .Con "evalResultPure" [a] => some (.Con "EvalOk" [a, .Con "Nil" []])
  | _ => none

def evalResultMapOk : Term → Option Term
  | .Con "evalResultMap" [f, .Con "EvalOk" [a, errs]] => some (.Con "EvalOk" [.Con "app" [a], errs])
  | _ => none

def evalResultMapFailed : Term → Option Term
  | .Con "evalResultMap" [f, .Con "EvalFailed" [errs]] => some (.Con "EvalFailed" [errs])
  | _ => none

def evalResultBindOk : Term → Option Term
  | .Con "evalResultBind" [.Con "EvalOk" [a, errs], f] => some (.Con "match" [.Con "app" [a], .Con "EvalOk" [.Var "b", .Var "errs2"], .Con "EvalOk" [.Var "b", .Con "append" [errs, .Var "errs2"]], .Con "EvalFailed" [.Var "errs2"], .Con "EvalFailed" [.Con "append" [errs, .Var "errs2"]]])
  | _ => none

def evalResultBindFailed : Term → Option Term
  | .Con "evalResultBind" [.Con "EvalFailed" [errs], f] => some (.Con "EvalFailed" [errs])
  | _ => none

def evalResultAddError : Term → Option Term
  | .Con "evalResultAddError" [e, .Con "EvalOk" [a, errs]] => some (.Con "EvalOk" [a, .Con "Cons" [e, errs]])
  | _ => none

def evalResultAddErrorFailed : Term → Option Term
  | .Con "evalResultAddError" [e, .Con "EvalFailed" [errs]] => some (.Con "EvalFailed" [.Con "Cons" [e, errs]])
  | _ => none

def evalResultIsOk : Term → Option Term
  | .Con "evalResultIsOk" [.Con "EvalOk" [a, errs]] => some (.Con "True" [])
  | _ => none

def evalResultIsOkFailed : Term → Option Term
  | .Con "evalResultIsOk" [.Con "EvalFailed" [errs]] => some (.Con "False" [])
  | _ => none

def evalResultGetErrors : Term → Option Term
  | .Con "evalResultGetErrors" [.Con "EvalOk" [a, errs]] => some (errs)
  | _ => none

def evalResultGetErrorsFailed : Term → Option Term
  | .Con "evalResultGetErrors" [.Con "EvalFailed" [errs]] => some (errs)
  | _ => none

def contextExtend : Term → Option Term
  | .Con "contextExtend" [ctx, name, ty, loc] => some (.Con "ContextCons" [.Con "MkBinding" [name, ty, .Con "None" [], loc], ctx])
  | _ => none

def contextExtendLet : Term → Option Term
  | .Con "contextExtendLet" [ctx, name, ty, val, loc] => some (.Con "ContextCons" [.Con "MkBinding" [name, ty, .Con "Some" [val], loc], ctx])
  | _ => none

def contextLookupEmpty : Term → Option Term
  | .Con "contextLookup" [.Con "EmptyContext" [], name] => some (.Con "None" [])
  | _ => none

def contextLookupFound : Term → Option Term
  | .Con "contextLookup" [.Con "ContextCons" [.Con "MkBinding" [name, ty, val, loc], rest], name_0] => if name_0 == name then some (.Con "Some" [.Con "MkBinding" [name, ty, val, loc]]) else none
  | _ => none

def contextLookupMiss : Term → Option Term
  | .Con "contextLookup" [.Con "ContextCons" [.Con "MkBinding" [n1, ty, val, loc], rest], n2] => some (.Con "contextLookup" [rest, n2])
  | _ => none

def contextLookupType : Term → Option Term
  | .Con "contextLookupType" [ctx, name] => some (.Con "match" [.Con "contextLookup" [ctx, name], .Con "Some" [.Con "MkBinding" [.Var "n", .Var "ty", .Var "v", .Var "l"]], .Con "Some" [.Var "ty"], .Con "None" [], .Con "None" []])
  | _ => none

def contextNames : Term → Option Term
  | .Con "contextNames" [.Con "EmptyContext" []] => some (.Con "Nil" [])
  | _ => none

def contextNamesCons : Term → Option Term
  | .Con "contextNames" [.Con "ContextCons" [.Con "MkBinding" [name, ty, val, loc], rest]] => some (.Con "Cons" [name, .Con "contextNames" [rest]])
  | _ => none

def varContextExtend : Term → Option Term
  | .Con "varContextExtend" [ctx, name] => some (.Con "VarContextCons" [name, ctx])
  | _ => none

def varContextContainsEmpty : Term → Option Term
  | .Con "varContextContains" [.Con "EmptyVarContext" [], name] => some (.Con "False" [])
  | _ => none

def varContextContainsFound : Term → Option Term
  | .Con "varContextContains" [.Con "VarContextCons" [name, rest], name_0] => if name_0 == name then some (.Con "True" []) else none
  | _ => none

def varContextContainsMiss : Term → Option Term
  | .Con "varContextContains" [.Con "VarContextCons" [n1, rest], n2] => some (.Con "varContextContains" [rest, n2])
  | _ => none

def evalEnvEmpty : Term → Option Term
  | .Con "evalEnvEmpty" [] => some (.Con "MkEvalEnv" [.Con "EmptyAttrEnv" [], .Con "EmptyContext" [], .Con "EmptyVarContext" [], .Con "Nil" [], .Con "UnknownLoc" []])
  | _ => none

def evalEnvWithCtx : Term → Option Term
  | .Con "evalEnvWithCtx" [.Con "MkEvalEnv" [attrs, oldCtx, vars, errs, loc], ctx] => some (.Con "MkEvalEnv" [attrs, ctx, vars, errs, loc])
  | _ => none

def evalEnvWithLoc : Term → Option Term
  | .Con "evalEnvWithLoc" [.Con "MkEvalEnv" [attrs, ctx, vars, errs, oldLoc], loc] => some (.Con "MkEvalEnv" [attrs, ctx, vars, errs, loc])
  | _ => none

def evalEnvAddBinding : Term → Option Term
  | .Con "evalEnvAddBinding" [.Con "MkEvalEnv" [attrs, ctx, vars, errs, loc], name, ty] => some (.Con "MkEvalEnv" [attrs, .Con "contextExtend" [ctx, name, ty, loc], vars, errs, loc])
  | _ => none

def evalEnvAddVar : Term → Option Term
  | .Con "evalEnvAddVar" [.Con "MkEvalEnv" [attrs, ctx, vars, errs, loc], name] => some (.Con "MkEvalEnv" [attrs, ctx, .Con "varContextExtend" [vars, name], errs, loc])
  | _ => none

def evalEnvAddError : Term → Option Term
  | .Con "evalEnvAddError" [.Con "MkEvalEnv" [attrs, ctx, vars, errs, loc], e] => some (.Con "MkEvalEnv" [attrs, ctx, vars, .Con "Cons" [e, errs], loc])
  | _ => none

def evalEnvAddTypeError : Term → Option Term
  | .Con "evalEnvAddTypeError" [.Con "MkEvalEnv" [attrs, ctx, vars, errs, loc], msg] => some (.Con "MkEvalEnv" [attrs, ctx, vars, .Con "Cons" [.Con "typeErrorSimple" [msg, loc], errs], loc])
  | _ => none

def evalEnvAddMismatch : Term → Option Term
  | .Con "evalEnvAddMismatch" [.Con "MkEvalEnv" [attrs, ctx, vars, errs, loc], expected, actual] => some (.Con "MkEvalEnv" [attrs, ctx, vars, .Con "Cons" [.Con "typeErrorMismatch" [expected, actual, loc], errs], loc])
  | _ => none

def evalEnvSetAttr : Term → Option Term
  | .Con "evalEnvSetAttr" [.Con "MkEvalEnv" [attrs, ctx, vars, errs, loc], path, name, val] => some (.Con "MkEvalEnv" [.Con "attrEnvInsert" [attrs, path, name, val], ctx, vars, errs, loc])
  | _ => none

def evalEnvGetAttr : Term → Option Term
  | .Con "evalEnvGetAttr" [.Con "MkEvalEnv" [attrs, ctx, vars, errs, loc], path, name] => some (.Con "attrEnvLookup" [attrs, path, name])
  | _ => none

def evalEnvHasErrors : Term → Option Term
  | .Con "evalEnvHasErrors" [.Con "MkEvalEnv" [attrs, ctx, vars, errs, loc]] => some (.Con "not" [.Con "null" [errs]])
  | _ => none

def freeVarsVar : Term → Option Term
  | .Con "freeVars" [.Con "Var" [n]] => some (.Con "Cons" [n, .Con "Nil" []])
  | _ => none

def freeVarsLit : Term → Option Term
  | .Con "freeVars" [.Con "Lit" [s]] => some (.Con "Nil" [])
  | _ => none

def freeVarsLam : Term → Option Term
  | .Con "freeVars" [.Con "Con" [.Lit "\"lam\"", .Con "Cons" [.Con "Var" [x], .Con "Cons" [ty, .Con "Cons" [body, .Con "Nil" []]]]]] => some (.Con "append" [.Con "freeVars" [ty], .Con "filter" [.Con "binder" [.Lit "v", .Con "not" [.Con "eq" [.Var "v", x]]], .Con "freeVars" [body]]])
  | _ => none

def freeVarsPi : Term → Option Term
  | .Con "freeVars" [.Con "Con" [.Lit "\"Pi\"", .Con "Cons" [.Con "Var" [x], .Con "Cons" [dom, .Con "Cons" [cod, .Con "Nil" []]]]]] => some (.Con "append" [.Con "freeVars" [dom], .Con "filter" [.Con "binder" [.Lit "v", .Con "not" [.Con "eq" [.Var "v", x]]], .Con "freeVars" [cod]]])
  | _ => none

def freeVarsCon : Term → Option Term
  | .Con "freeVars" [.Con "Con" [c, args]] => some (.Con "flatMap" [.Con "freeVars" [], args])
  | _ => none

def freshName : Term → Option Term
  | .Con "freshName" [base, avoid] => some (.Con "freshNameHelper" [base, avoid, .Lit "0"])
  | _ => none

def freshNameHelper : Term → Option Term
  | .Con "freshNameHelper" [base, avoid, i] => some (.Con "let" [.Var "candidate", .Con "if" [.Con "eq" [i, .Lit "0"], base, .Con "concat" [base, .Con "toString" [i]]], .Con "if" [.Con "contains" [avoid, .Var "candidate"], .Con "freshNameHelper" [base, avoid, .Con "add" [i, .Lit "1"]], .Var "candidate"]])
  | _ => none

def substAvoidVar : Term → Option Term
  | .Con "substAvoid" [name, repl, fv, .Con "Var" [n]] => some (.Con "if" [.Con "eq" [n, name], repl, .Con "Var" [n]])
  | _ => none

def substAvoidLit : Term → Option Term
  | .Con "substAvoid" [name, repl, fv, .Con "Lit" [s]] => some (.Con "Lit" [s])
  | _ => none

def substAvoidLam : Term → Option Term
  | .Con "substAvoid" [name, repl, fv, .Con "Con" [.Lit "\"lam\"", .Con "Cons" [.Con "Var" [x], .Con "Cons" [ty, .Con "Cons" [body, .Con "Nil" []]]]]] => some (.Con "if" [.Con "eq" [x, name], .Con "Con" [.Lit "\"lam\"", .Con "Cons" [.Con "Var" [x], .Con "Cons" [.Con "substAvoid" [name, repl, fv, ty], .Con "Cons" [body, .Con "Nil" []]]]], .Con "if" [.Con "contains" [fv, x], .Con "let" [.Var "x2", .Con "freshName" [x, fv], .Con "let" [.Var "body2", .Con "subst" [x, .Con "Var" [.Var "x2"], body], .Con "Con" [.Lit "\"lam\"", .Con "Cons" [.Con "Var" [.Var "x2"], .Con "Cons" [.Con "substAvoid" [name, repl, fv, ty], .Con "Cons" [.Con "substAvoid" [name, repl, .Con "Cons" [.Var "x2", fv], .Var "body2"], .Con "Nil" []]]]]]], .Con "Con" [.Lit "\"lam\"", .Con "Cons" [.Con "Var" [x], .Con "Cons" [.Con "substAvoid" [name, repl, fv, ty], .Con "Cons" [.Con "substAvoid" [name, repl, fv, body], .Con "Nil" []]]]]]])
  | _ => none

def substAvoidPi : Term → Option Term
  | .Con "substAvoid" [name, repl, fv, .Con "Con" [.Lit "\"Pi\"", .Con "Cons" [.Con "Var" [x], .Con "Cons" [dom, .Con "Cons" [cod, .Con "Nil" []]]]]] => some (.Con "if" [.Con "eq" [x, name], .Con "Con" [.Lit "\"Pi\"", .Con "Cons" [.Con "Var" [x], .Con "Cons" [.Con "substAvoid" [name, repl, fv, dom], .Con "Cons" [cod, .Con "Nil" []]]]], .Con "if" [.Con "contains" [fv, x], .Con "let" [.Var "x2", .Con "freshName" [x, fv], .Con "let" [.Var "cod2", .Con "subst" [x, .Con "Var" [.Var "x2"], cod], .Con "Con" [.Lit "\"Pi\"", .Con "Cons" [.Con "Var" [.Var "x2"], .Con "Cons" [.Con "substAvoid" [name, repl, fv, dom], .Con "Cons" [.Con "substAvoid" [name, repl, .Con "Cons" [.Var "x2", fv], .Var "cod2"], .Con "Nil" []]]]]]], .Con "Con" [.Lit "\"Pi\"", .Con "Cons" [.Con "Var" [x], .Con "Cons" [.Con "substAvoid" [name, repl, fv, dom], .Con "Cons" [.Con "substAvoid" [name, repl, fv, cod], .Con "Nil" []]]]]]])
  | _ => none

def substAvoidCon : Term → Option Term
  | .Con "substAvoid" [name, repl, fv, .Con "Con" [c, args]] => some (.Con "Con" [c, .Con "map" [.Con "binder" [.Lit "a", .Con "substAvoid" [name, repl, fv, .Var "a"]], args]])
  | _ => none

def attrRefSelf : Term → Option Term
  | .Con "attrRefSelf" [name] => some (.Con "MkAttrRef" [.Con "Empty" [], name])
  | _ => none

def attrRefChild : Term → Option Term
  | .Con "attrRefChild" [child, name] => some (.Con "MkAttrRef" [.Con "PathCon" [child, .Con "Empty" []], name])
  | _ => none

def emptyAttrDef : Term → Option Term
  | .Con "emptyAttrDef" [name, flow] => some (.Con "MkAttrDef" [name, flow, .Con "None" [], .Con "Nil" []])
  | _ => none

def addAttrRule : Term → Option Term
  | .Con "addAttrRule" [.Con "MkAttrDef" [name, flow, ty, rules], rule] => some (.Con "MkAttrDef" [name, flow, ty, .Con "append" [rules, .Con "Cons" [rule, .Con "Nil" []]]])
  | _ => none

def attrEnvLookupEmpty : Term → Option Term
  | .Con "attrEnvLookup" [.Con "Empty" [], path, name] => some (.Con "None" [])
  | _ => none

def attrEnvLookupFound : Term → Option Term
  | .Con "attrEnvLookup" [.Con "AttrEnvCons" [path, name, val, rest], path_0, name_1] => if name_1 == name && path_0 == path then some (.Con "Some" [val]) else none
  | _ => none

def attrEnvLookupMiss : Term → Option Term
  | .Con "attrEnvLookup" [.Con "AttrEnvCons" [p1, n1, val, rest], p2, n2] => some (.Con "attrEnvLookup" [rest, p2, n2])
  | _ => none

def attrEnvInsert : Term → Option Term
  | .Con "attrEnvInsert" [env, path, name, val] => some (.Con "AttrEnvCons" [path, name, val, env])
  | _ => none

def attrEnvGetLocal : Term → Option Term
  | .Con "attrEnvGetLocal" [env, name] => some (.Con "attrEnvLookup" [env, .Con "Empty" [], name])
  | _ => none

def attrEnvGetChild : Term → Option Term
  | .Con "attrEnvGetChild" [env, child, name] => some (.Con "attrEnvLookup" [env, .Con "PathCon" [child, .Con "Empty" []], name])
  | _ => none

def attrEnvMergeEmpty : Term → Option Term
  | .Con "attrEnvMerge" [env1, .Con "EmptyAttrEnv" []] => some (env1)
  | _ => none

def attrEnvMergeCons : Term → Option Term
  | .Con "attrEnvMerge" [env1, .Con "AttrEnvCons" [path, name, val, rest]] => some (.Con "attrEnvMerge" [.Con "AttrEnvCons" [path, name, val, env1], rest])
  | _ => none

def evalAttrExprVar : Term → Option Term
  | .Con "evalAttrExpr" [.Con "Var" [name], env] => some (.Con "if" [.Con "startsWith" [name, .Lit "\"$\""], .Con "match" [.Con "attrEnvLookup" [env, .Con "Empty" [], .Con "drop" [.Lit "1", name]], .Con "Some" [.Var "v"], .Var "v", .Con "None" [], .Con "Con" [.Lit "\"error\"", .Con "Cons" [.Con "Lit" [.Con "concat" [.Lit "\"undefined: \"", name]], .Con "Nil" []]]], .Con "Var" [name]])
  | _ => none

def evalAttrExprCon : Term → Option Term
  | .Con "evalAttrExpr" [.Con "Con" [c, args], env] => some (.Con "Con" [c, .Con "map" [.Con "binder" [.Lit "x", .Con "evalAttrExpr" [.Var "x", env]], args]])
  | _ => none

def evalAttrExprLit : Term → Option Term
  | .Con "evalAttrExpr" [.Con "Lit" [s], env] => some (.Con "Lit" [s])
  | _ => none

def findRuleEmpty : Term → Option Term
  | .Con "findRule" [prod, target, .Con "Nil" []] => some (.Con "None" [])
  | _ => none

def findRuleFound : Term → Option Term
  | .Con "findRule" [prod, target, .Con "Cons" [.Con "MkAttrRule" [prod_0, target_1, expr], rest]] => if target_1 == target && prod_0 == prod then some (.Con "Some" [.Con "MkAttrRule" [prod, target, expr]]) else none
  | _ => none

def findRuleMiss : Term → Option Term
  | .Con "findRule" [prod, target, .Con "Cons" [.Con "MkAttrRule" [p2, t2, e], rest]] => some (.Con "findRule" [prod, target, rest])
  | _ => none

def evalSynVar : Term → Option Term
  | .Con "evalSyn" [v_def, .Con "Var" [x]] => some (.Con "EmptyAttrEnv" [])
  | _ => none

def evalSynLit : Term → Option Term
  | .Con "evalSyn" [v_def, .Con "Lit" [s]] => some (.Con "EmptyAttrEnv" [])
  | _ => none

def evalSynCon : Term → Option Term
  | .Con "evalSyn" [.Con "MkAttrDef" [attrName, flow, ty, rules], .Con "Con" [prod, children]] => some (.Con "evalSynConHelper" [attrName, flow, ty, rules, prod, children, .Lit "0"])
  | _ => none

def evalSynConHelper : Term → Option Term
  | .Con "evalSynConHelper" [attrName, flow, ty, rules, prod, children, idx] => some (.Con "let" [.Var "childEnvs", .Con "mapWithIndex" [.Con "i" [.Con "binder" [.Lit "child", .Con "prefixEnv" [.Con "concat" [.Lit "\"child\"", .Con "toString" [.Var "i"]], .Con "evalSyn" [.Con "MkAttrDef" [attrName, flow, ty, rules], .Var "child"]]]], children], .Con "let" [.Var "env", .Con "foldl" [.Con "attrEnvMerge" [], .Con "EmptyAttrEnv" [], .Var "childEnvs"], .Con "match" [.Con "findRule" [prod, .Con "Empty" [], rules], .Con "Some" [.Con "MkAttrRule" [.Var "p", .Var "t", .Var "expr"]], .Con "attrEnvInsert" [.Var "env", .Con "Empty" [], attrName, .Con "evalAttrExpr" [.Var "expr", .Var "env"]], .Con "None" [], .Var "env"]]])
  | _ => none

def evalInhVar : Term → Option Term
  | .Con "evalInh" [v_def, .Con "Var" [x], parentEnv] => some (parentEnv)
  | _ => none

def evalInhLit : Term → Option Term
  | .Con "evalInh" [v_def, .Con "Lit" [s], parentEnv] => some (parentEnv)
  | _ => none

def evalInhCon : Term → Option Term
  | .Con "evalInh" [.Con "MkAttrDef" [attrName, flow, ty, rules], .Con "Con" [prod, children], parentEnv] => some (.Con "evalInhConHelper" [attrName, flow, ty, rules, prod, children, parentEnv, .Lit "0"])
  | _ => none

def evalAttrs : Term → Option Term
  | .Con "evalAttrs" [defs, term] => some (.Con "let" [.Var "synDefs", .Con "filter" [.Con "binder" [.Lit "d", .Con "eq" [.Con "attrDefFlow" [.Var "d"], .Con "Syn" []]], defs], .Con "let" [.Var "inhDefs", .Con "filter" [.Con "binder" [.Lit "d", .Con "eq" [.Con "attrDefFlow" [.Var "d"], .Con "Inh" []]], defs], .Con "let" [.Var "inhEnv", .Con "foldl" [.Con "env" [.Con "binder" [.Lit "def", .Con "evalInh" [.Var "def", term, .Var "env"]]], .Con "EmptyAttrEnv" [], .Var "inhDefs"], .Con "foldl" [.Con "env" [.Con "binder" [.Lit "def", .Con "attrEnvMerge" [.Var "env", .Con "evalSyn" [.Var "def", term]]]], .Var "inhEnv", .Var "synDefs"]]]])
  | _ => none

def cataTermVar : Term → Option Term
  | .Con "cataTerm" [alg, .Con "Var" [x]] => some (.Con "app" [x, .Con "Nil" []])
  | _ => none

def cataTermLit : Term → Option Term
  | .Con "cataTerm" [alg, .Con "Lit" [s]] => some (.Con "app" [s, .Con "Nil" []])
  | _ => none

def cataTermCon : Term → Option Term
  | .Con "cataTerm" [alg, .Con "Con" [c, args]] => some (.Con "app" [c, .Con "map" [.Con "binder" [.Lit "a", .Con "cataTerm" [alg, .Var "a"]], args]])
  | _ => none

def paraTermVar : Term → Option Term
  | .Con "paraTerm" [coalg, .Con "Var" [x]] => some (.Con "app" [x, .Con "Nil" []])
  | _ => none

def paraTermLit : Term → Option Term
  | .Con "paraTerm" [coalg, .Con "Lit" [s]] => some (.Con "app" [s, .Con "Nil" []])
  | _ => none

def paraTermCon : Term → Option Term
  | .Con "paraTerm" [coalg, .Con "Con" [c, args]] => some (.Con "app" [c, .Con "map" [.Con "binder" [.Lit "a", .Con "Pair" [.Var "a", .Con "paraTerm" [coalg, .Var "a"]]], args]])
  | _ => none

def attrLangSynAttrs : Term → Option Term
  | .Con "attrLangSynAttrs" [.Con "MkAttrLanguage" [name, pieces, attrs]] => some (.Con "filter" [.Con "binder" [.Lit "d", .Con "eq" [.Con "attrDefFlow" [.Var "d"], .Con "Syn" []]], attrs])
  | _ => none

def attrLangInhAttrs : Term → Option Term
  | .Con "attrLangInhAttrs" [.Con "MkAttrLanguage" [name, pieces, attrs]] => some (.Con "filter" [.Con "binder" [.Lit "d", .Con "eq" [.Con "attrDefFlow" [.Var "d"], .Con "Inh" []]], attrs])
  | _ => none

def attrLangEval : Term → Option Term
  | .Con "attrLangEval" [.Con "MkAttrLanguage" [name, pieces, attrs], term] => some (.Con "evalAttrs" [attrs, term])
  | _ => none

def attrLangPushout : Term → Option Term
  | .Con "attrLangPushout" [.Con "MkAttrLanguage" [n1, p1, a1], .Con "MkAttrLanguage" [n2, p2, a2]] => some (.Con "MkAttrLanguage" [.Con "concat" [.Con "concat" [n1, .Lit "\"_\""], n2], .Con "append" [p1, p2], .Con "append" [a1, a2]])
  | _ => none

def tokEq : Term → Option Term
  | .Con "tokEq" [.Con "TokIdent" [a], .Con "TokIdent" [b]] => some (.Con "strEq" [a, b])
  | _ => none

def tokEqString : Term → Option Term
  | .Con "tokEq" [.Con "TokString" [a], .Con "TokString" [b]] => some (.Con "strEq" [a, b])
  | _ => none

def tokEqSym : Term → Option Term
  | .Con "tokEq" [.Con "TokSym" [a], .Con "TokSym" [b]] => some (.Con "strEq" [a, b])
  | _ => none

def tokEqMismatch : Term → Option Term
  | .Con "tokEq" [a, b] => some (.Con "false" [])
  | _ => none

def stateTokens : Term → Option Term
  | .Con "stateTokens" [.Con "MkState" [toks, pos]] => some (toks)
  | _ => none

def statePos : Term → Option Term
  | .Con "statePos" [.Con "MkState" [toks, pos]] => some (pos)
  | _ => none

def stateAdvance : Term → Option Term
  | .Con "stateAdvance" [.Con "MkState" [.Con "Cons" [v_t, ts], pos]] => some (.Con "MkState" [ts, .Con "add" [pos, .Lit "1"]])
  | _ => none

def parseLit : Term → Option Term
  | .Con "parseLit" [s, .Con "MkState" [.Con "Cons" [.Con "TokSym" [s_0], rest], pos]] => if s_0 == s then some (.Con "ParseOk" [.Con "Lit" [s], .Con "MkState" [rest, .Con "add" [pos, .Lit "1"]]]) else none
  | _ => none

def parseLitFail : Term → Option Term
  | .Con "parseLit" [s, .Con "MkState" [.Con "Cons" [v_t, rest], pos]] => some (.Con "ParseFail" [.Con "concat" [.Lit "\"expected \"", s], .Con "MkState" [.Con "Cons" [v_t, rest], pos]])
  | _ => none

def parseIdent : Term → Option Term
  | .Con "parseIdent" [.Con "MkState" [.Con "Cons" [.Con "TokIdent" [name], rest], pos]] => some (.Con "ParseOk" [.Con "Var" [name], .Con "MkState" [rest, .Con "add" [pos, .Lit "1"]]])
  | _ => none

def parseIdentFail : Term → Option Term
  | .Con "parseIdent" [.Con "MkState" [.Con "Cons" [v_t, rest], pos]] => some (.Con "ParseFail" [.Lit "\"expected identifier\"", .Con "MkState" [.Con "Cons" [v_t, rest], pos]])
  | _ => none

def parseSeq : Term → Option Term
  | .Con "parseSeq" [p1, p2, state] => some (.Con "case" [.Con "parse" [p1, state], .Con "ParseOk" [.Var "t1", .Var "s1"], .Con "case" [.Con "parse" [p2, .Var "s1"], .Con "ParseOk" [.Var "t2", .Var "s2"], .Con "ParseOk" [.Con "Con" [.Lit "\"seq\"", .Con "Cons" [.Var "t1", .Con "Cons" [.Var "t2", .Con "Nil" []]]], .Var "s2"], .Con "ParseFail" [.Var "msg", .Var "s"], .Con "ParseFail" [.Var "msg", .Var "s"]], .Con "ParseFail" [.Var "msg", .Var "s"], .Con "ParseFail" [.Var "msg", .Var "s"]])
  | _ => none

def parseAlt : Term → Option Term
  | .Con "parseAlt" [p1, p2, state] => some (.Con "case" [.Con "parse" [p1, state], .Con "ParseOk" [.Var "t", .Var "s"], .Con "ParseOk" [.Var "t", .Var "s"], .Con "ParseFail" [.Var "msg1", .Var "s1"], .Con "case" [.Con "parse" [p2, state], .Con "ParseOk" [.Var "t", .Var "s"], .Con "ParseOk" [.Var "t", .Var "s"], .Con "ParseFail" [.Var "msg2", .Var "s2"], .Con "ParseFail" [.Con "concat" [.Var "msg1", .Con "concat" [.Lit "\" or \"", .Var "msg2"]], state]]])
  | _ => none

def parseStar : Term → Option Term
  | .Con "parseStar" [p, state] => some (.Con "case" [.Con "parse" [p, state], .Con "ParseOk" [.Var "t", .Var "s"], .Con "case" [.Con "parseStar" [p, .Var "s"], .Con "ParseOk" [.Con "Con" [.Lit "\"list\"", .Var "ts"], .Var "s2"], .Con "ParseOk" [.Con "Con" [.Lit "\"list\"", .Con "Cons" [.Var "t", .Var "ts"]], .Var "s2"], .Con "ParseFail" [.Var "msg", .Var "s2"], .Con "ParseOk" [.Con "Con" [.Lit "\"list\"", .Con "Cons" [.Var "t", .Con "Nil" []]], .Var "s"]], .Con "ParseFail" [.Var "msg", .Var "s"], .Con "ParseOk" [.Con "Con" [.Lit "\"list\"", .Con "Nil" []], state]])
  | _ => none

def parseOpt : Term → Option Term
  | .Con "parseOpt" [p, state] => some (.Con "case" [.Con "parse" [p, state], .Con "ParseOk" [.Var "t", .Var "s"], .Con "ParseOk" [.Con "Con" [.Lit "\"some\"", .Con "Cons" [.Var "t", .Con "Nil" []]], .Var "s"], .Con "ParseFail" [.Var "msg", .Var "s"], .Con "ParseOk" [.Con "Con" [.Lit "\"none\"", .Con "Nil" []], state]])
  | _ => none

def parseCon : Term → Option Term
  | .Con "parseCon" [name, p, state] => some (.Con "case" [.Con "parse" [p, state], .Con "ParseOk" [.Var "t", .Var "s"], .Con "ParseOk" [.Con "Con" [name, .Con "Cons" [.Var "t", .Con "Nil" []]], .Var "s"], .Con "ParseFail" [.Var "msg", .Var "s"], .Con "ParseFail" [.Var "msg", .Var "s"]])
  | _ => none

def parseGEmpty : Term → Option Term
  | .Con "parse" [.Con "GEmpty" [], state] => some (.Con "ParseOk" [.Con "Con" [.Lit "\"unit\"", .Con "Nil" []], state])
  | _ => none

def parseGLit : Term → Option Term
  | .Con "parse" [.Con "GLit" [s], state] => some (.Con "parseLit" [s, state])
  | _ => none

def parseGRef : Term → Option Term
  | .Con "parse" [.Con "GRef" [.Lit "\"ident\""], state] => some (.Con "parseIdent" [state])
  | _ => none

def parseGSeq : Term → Option Term
  | .Con "parse" [.Con "GSeq" [g1, g2], state] => some (.Con "parseSeq" [g1, g2, state])
  | _ => none

def parseGAlt : Term → Option Term
  | .Con "parse" [.Con "GAlt" [g1, g2], state] => some (.Con "parseAlt" [g1, g2, state])
  | _ => none

def parseGStar : Term → Option Term
  | .Con "parse" [.Con "GStar" [g], state] => some (.Con "parseStar" [g, state])
  | _ => none

def parseGOpt : Term → Option Term
  | .Con "parse" [.Con "GOpt" [g], state] => some (.Con "parseOpt" [g, state])
  | _ => none

def parseGCon : Term → Option Term
  | .Con "parse" [.Con "GCon" [name, g], state] => some (.Con "parseCon" [name, g, state])
  | _ => none

def printLit : Term → Option Term
  | .Con "print" [.Con "GLit" [s], .Con "Lit" [s_0]] => if s_0 == s then some (.Con "PrintOk" [.Con "Cons" [.Con "TokSym" [s], .Con "Nil" []]]) else none
  | _ => none

def printIdent : Term → Option Term
  | .Con "print" [.Con "GRef" [.Lit "\"ident\""], .Con "Var" [name]] => some (.Con "PrintOk" [.Con "Cons" [.Con "TokIdent" [name], .Con "Nil" []]])
  | _ => none

def printSeq : Term → Option Term
  | .Con "print" [.Con "GSeq" [g1, g2], .Con "Con" [.Lit "\"seq\"", .Con "Cons" [t1, .Con "Cons" [t2, .Con "Nil" []]]]] => some (.Con "case" [.Con "print" [g1, t1], .Con "PrintOk" [.Var "toks1"], .Con "case" [.Con "print" [g2, t2], .Con "PrintOk" [.Var "toks2"], .Con "PrintOk" [.Con "append" [.Var "toks1", .Var "toks2"]], .Con "PrintFail" [.Var "msg"], .Con "PrintFail" [.Var "msg"]], .Con "PrintFail" [.Var "msg"], .Con "PrintFail" [.Var "msg"]])
  | _ => none

def printCon : Term → Option Term
  | .Con "print" [.Con "GCon" [name, g], .Con "Con" [name_0, .Con "Cons" [v_t, .Con "Nil" []]]] => if name_0 == name then some (.Con "print" [g, v_t]) else none
  | _ => none

def grammarIso : Term → Option Term
  | .Con "grammarIso" [g] => some (.Con "MkIso" [.Con "Lam" [.Con "binder" [.Lit "input", .Con "case" [.Con "parse" [g, .Con "tokenize" [.Con "input" []]], .Con "ParseOk" [.Var "t", .Var "s"], .Con "Some" [.Var "t"], .Con "ParseFail" [.Var "msg", .Var "s"], .Con "None" []]]], .Con "Lam" [.Con "binder" [.Lit "term", .Con "case" [.Con "print" [g, .Var "term"], .Con "PrintOk" [.Var "toks"], .Con "Some" [.Con "detokenize" [.Var "toks"]], .Con "PrintFail" [.Var "msg"], .Con "None" []]]]])
  | _ => none

def matchVarMeta : Term → Option Term
  | .Con "match" [.Con "Var" [name], v_t] => some (.Con "Some" [.Con "Bind" [name, v_t, .Con "Empty" []]])
  | _ => none

def matchListNil : Term → Option Term
  | .Con "matchList" [.Con "Nil" [], .Con "Nil" []] => some (.Con "Some" [.Con "Empty" []])
  | _ => none

def matchListCons : Term → Option Term
  | .Con "matchList" [.Con "Cons" [p, ps], .Con "Cons" [v_t, ts]] => some (.Con "merge" [.Con "match" [p, v_t], .Con "matchList" [ps, ts]])
  | _ => none

def mergeEnvs : Term → Option Term
  | .Con "merge" [.Con "Some" [e1], .Con "Some" [e2]] => some (.Con "Some" [.Con "append" [e1, e2]])
  | _ => none

def substVarHit : Term → Option Term
  | .Con "subst" [.Con "Var" [name], .Con "Bind" [name_0, val, rest]] => if name_0 == name then some (val) else none
  | _ => none

def substVarMiss : Term → Option Term
  | .Con "subst" [.Con "Var" [name], .Con "Bind" [other, val, rest]] => some (.Con "subst" [.Con "Var" [name], rest])
  | _ => none

def substVarEmpty : Term → Option Term
  | .Con "subst" [.Con "Var" [name], .Con "Empty" []] => some (.Con "Var" [name])
  | _ => none

def applyRule : Term → Option Term
  | .Con "apply" [.Con "MkRule" [name, pat, tmpl], v_t] => some (.Con "case" [.Con "match" [pat, v_t], .Con "Some" [.Var "env"], .Con "subst" [tmpl, .Var "env"], .Con "None" [], .Con "None" []])
  | _ => none

def tryRulesFirst : Term → Option Term
  | .Con "tryRules" [.Con "Cons" [r, rs], v_t] => some (.Con "case" [.Con "apply" [r, v_t], .Con "Some" [.Var "result"], .Con "Some" [.Var "result"], .Con "None" [], .Con "tryRules" [rs, v_t]])
  | _ => none

def tryRulesEmpty : Term → Option Term
  | .Con "tryRules" [.Con "Nil" [], v_t] => some (.Con "None" [])
  | _ => none

def normalizeStep : Term → Option Term
  | .Con "normalize" [rules, v_t] => some (.Con "let" [.Var "t'", .Con "normalizeOnce" [rules, v_t], .Con "if" [.Con "eq" [v_t, .Var "t'"], v_t, .Con "normalize" [rules, .Var "t'"]]])
  | _ => none

def normalizeOnceTop : Term → Option Term
  | .Con "normalizeOnce" [rules, v_t] => some (.Con "case" [.Con "tryRules" [rules, v_t], .Con "Some" [.Var "result"], .Var "result", .Con "None" [], .Con "normalizeChildren" [rules, v_t]])
  | _ => none

def normalizeChildrenVar : Term → Option Term
  | .Con "normalizeChildren" [rules, .Con "Var" [x]] => some (.Con "Var" [x])
  | _ => none

def normalizeChildrenLit : Term → Option Term
  | .Con "normalizeChildren" [rules, .Con "Lit" [s]] => some (.Con "Lit" [s])
  | _ => none

def normalizeChildrenCon : Term → Option Term
  | .Con "normalizeChildren" [rules, .Con "Con" [name, args]] => some (.Con "Con" [name, .Con "map" [.Con "normalizeOnce" [rules], args]])
  | _ => none

def rosettaTranslate : Term → Option Term
  | .Con "translate" [.Con "MkLang" [n1, g1, iso1], .Con "MkLang" [n2, g2, iso2], src] => some (.Con "forward" [iso2, .Con "backward" [iso1, src]])
  | _ => none

def roundTrip : Term → Option Term
  | .Con "roundtrip" [.Con "MkLang" [n, g, .Con "MkIso" [parse, print]], src] => some (.Con "bind" [.Con "App" [parse, src], .Var "ast", .Con "App" [print, .Var "ast"]])
  | _ => none

def mapNil : Term → Option Term
  | .Con "map" [f, .Con "Nil" []] => some (.Con "Nil" [])
  | _ => none

def mapCons : Term → Option Term
  | .Con "map" [f, .Con "Cons" [x, xs]] => some (.Con "Cons" [.Con "App" [f, x], .Con "map" [f, xs]])
  | _ => none

def foldNil : Term → Option Term
  | .Con "fold" [f, acc, .Con "Nil" []] => some (acc)
  | _ => none

def foldCons : Term → Option Term
  | .Con "fold" [f, acc, .Con "Cons" [x, xs]] => some (.Con "fold" [f, .Con "App" [f, acc, x], xs])
  | _ => none

def appendNil : Term → Option Term
  | .Con "append" [.Con "Nil" [], ys] => some (ys)
  | _ => none

def appendCons : Term → Option Term
  | .Con "append" [.Con "Cons" [x, xs], ys] => some (.Con "Cons" [x, .Con "append" [xs, ys]])
  | _ => none

def ifTrue : Term → Option Term
  | .Con "if" [.Con "true" [], v_then, v_else] => some (v_then)
  | _ => none

def ifFalse : Term → Option Term
  | .Con "if" [.Con "false" [], v_then, v_else] => some (v_else)
  | _ => none

def eqSame : Term → Option Term
  | .Con "eq" [x, x_0] => if x_0 == x then some (.Con "true" []) else none
  | _ => none

def bindSome : Term → Option Term
  | .Con "bind" [.Con "Some" [x], var, body] => some (.Con "subst" [body, .Con "Bind" [var, x, .Con "Empty" []]])
  | _ => none

def bindNone : Term → Option Term
  | .Con "bind" [.Con "None" [], var, body] => some (.Con "None" [])
  | _ => none

def prodName : Term → Option Term
  | .Con "prodName" [.Con "MkProd" [name, expr, con]] => some (name)
  | _ => none

def prodGrammar : Term → Option Term
  | .Con "prodGrammar" [.Con "MkProd" [name, expr, con]] => some (expr)
  | _ => none

def prodCon : Term → Option Term
  | .Con "prodCon" [.Con "MkProd" [name, expr, con]] => some (con)
  | _ => none

def astToGrammarLit : Term → Option Term
  | .Con "astToGrammar" [.Con "Con" [.Lit "\"lit\"", .Con "Cons" [.Con "Con" [.Lit "\"string\"", .Con "Cons" [.Con "Lit" [s], .Con "Nil" []]], .Con "Nil" []]]] => some (.Con "GLit" [.Con "stripQuotes" [s]])
  | _ => none

def astToGrammarRef : Term → Option Term
  | .Con "astToGrammar" [.Con "Con" [.Lit "\"ref\"", .Con "Cons" [.Con "Con" [.Lit "\"ident\"", .Con "Cons" [.Con "Var" [name], .Con "Nil" []]], .Con "Nil" []]]] => some (.Con "GRef" [name])
  | _ => none

def astToGrammarSpecial : Term → Option Term
  | .Con "astToGrammar" [.Con "Con" [.Lit "\"special\"", .Con "Cons" [.Con "Var" [s], .Con "Nil" []]]] => some (.Con "GRef" [.Con "concat" [.Lit "\"TOKEN.\"", .Con "stripAngleBrackets" [s]]])
  | _ => none

def astToGrammarSeq : Term → Option Term
  | .Con "astToGrammar" [.Con "Con" [.Lit "\"seq\"", args]] => some (.Con "foldr" [.Con "GSeq" [], .Con "GEmpty" [], .Con "map" [.Con "astToGrammar" [], args]])
  | _ => none

def astToGrammarAlt : Term → Option Term
  | .Con "astToGrammar" [.Con "Con" [.Lit "\"alt\"", args]] => some (.Con "let" [.Var "parts", .Con "splitByPipe" [args], .Con "foldr1" [.Con "GAlt" [], .Con "map" [.Con "astToGrammar" [], .Var "parts"]]])
  | _ => none

def astToGrammarStar : Term → Option Term
  | .Con "astToGrammar" [.Con "Con" [.Lit "\"star\"", .Con "Cons" [g, .Con "Nil" []]]] => some (.Con "GStar" [.Con "astToGrammar" [g]])
  | _ => none

def astToGrammarPlus : Term → Option Term
  | .Con "astToGrammar" [.Con "Con" [.Lit "\"plus\"", .Con "Cons" [g, .Con "Nil" []]]] => some (.Con "GPlus" [.Con "astToGrammar" [g]])
  | _ => none

def astToGrammarOpt : Term → Option Term
  | .Con "astToGrammar" [.Con "Con" [.Lit "\"opt\"", .Con "Cons" [g, .Con "Nil" []]]] => some (.Con "GOpt" [.Con "astToGrammar" [g]])
  | _ => none

def astToGrammarNot : Term → Option Term
  | .Con "astToGrammar" [.Con "Con" [.Lit "\"not\"", .Con "Cons" [g, .Con "Nil" []]]] => some (.Con "GNot" [.Con "astToGrammar" [g]])
  | _ => none

def astToGrammarAnd : Term → Option Term
  | .Con "astToGrammar" [.Con "Con" [.Lit "\"and\"", .Con "Cons" [g, .Con "Nil" []]]] => some (.Con "GAnd" [.Con "astToGrammar" [g]])
  | _ => none

def extractParentNames : Term → Option Term
  | .Con "extractParentNames" [.Con "Con" [.Lit "\"DLang\"", args]] => some (.Con "filterMap" [.Con "extractParentFromArg" [], args])
  | _ => none

def extractParentNamesOther : Term → Option Term
  | .Con "extractParentNames" [other] => some (.Con "Nil" [])
  | _ => none

def extractParentFromArg : Term → Option Term
  | .Con "extractParentFromArg" [.Con "Con" [.Lit "\"DImports\"", imports]] => some (.Con "Some" [.Con "filterMap" [.Con "extractIdentName" [], imports]])
  | _ => none

def extractParentFromArgOther : Term → Option Term
  | .Con "extractParentFromArg" [other] => some (.Con "None" [])
  | _ => none

def extractIdentName : Term → Option Term
  | .Con "extractIdentName" [.Con "Con" [.Lit "\"ident\"", .Con "Cons" [.Con "Var" [name], .Con "Nil" []]]] => some (.Con "Some" [name])
  | _ => none

def extractIdentNameOther : Term → Option Term
  | .Con "extractIdentName" [other] => some (.Con "None" [])
  | _ => none

def extractProductions : Term → Option Term
  | .Con "extractProductions" [.Con "Con" [.Lit "\"DGrammar\"", .Con "Cons" [.Con "Con" [.Lit "\"ident\"", .Con "Cons" [.Con "Var" [lang], .Con "Nil" []]], .Con "Cons" [pieces, .Con "Nil" []]]]] => some (.Con "concatMap" [.Con "extractPieceProductions" [], .Con "getList" [pieces]])
  | _ => none

def extractPieceProductions : Term → Option Term
  | .Con "extractPieceProductions" [.Con "Con" [.Lit "\"DPiece\"", .Con "Cons" [.Con "Con" [.Lit "\"ident\"", .Con "Cons" [.Con "Var" [pieceName], .Con "Nil" []]], .Con "Cons" [members, .Con "Nil" []]]]] => some (.Con "concatMap" [.Con "extractMemberProd" [pieceName], .Con "getList" [members]])
  | _ => none

def extractMemberProdSyntax : Term → Option Term
  | .Con "extractMemberProd" [piece, .Con "Con" [.Lit "\"DSyntax\"", .Con "Cons" [.Con "Con" [.Lit "\"ident\"", .Con "Cons" [.Con "Var" [cat], .Con "Nil" []]], .Con "Cons" [alts, .Con "Nil" []]]]] => some (.Con "map" [.Con "mkProduction" [piece, cat], .Con "splitByPipe" [.Con "getList" [alts]]])
  | _ => none

def mkProduction : Term → Option Term
  | .Con "mkProduction" [piece, cat, alt] => some (.Con "let" [.Var "conName", .Con "extractConName" [alt], .Con "MkProd" [.Con "concat" [piece, .Con "concat" [.Lit "\".\"", cat]], .Con "astToGrammar" [alt], .Var "conName"]])
  | _ => none

def extractConName : Term → Option Term
  | .Con "extractConName" [alt] => some (.Con "case" [.Con "findArrow" [alt], .Con "Some" [.Var "name"], .Var "name", .Con "None" [], .Lit "\"node\""])
  | _ => none

def extractRules : Term → Option Term
  | .Con "extractRules" [.Con "Con" [.Lit "\"DGrammar\"", .Con "Cons" [lang, .Con "Cons" [pieces, .Con "Nil" []]]]] => some (.Con "concatMap" [.Con "extractPieceRules" [], .Con "getList" [pieces]])
  | _ => none

def extractPieceRules : Term → Option Term
  | .Con "extractPieceRules" [.Con "Con" [.Lit "\"DPiece\"", .Con "Cons" [name, .Con "Cons" [members, .Con "Nil" []]]]] => some (.Con "filterMap" [.Con "extractRule" [], .Con "getList" [members]])
  | _ => none

def extractRule : Term → Option Term
  | .Con "extractRule" [.Con "Con" [.Lit "\"DRule\"", .Con "Cons" [.Con "Con" [.Lit "\"ident\"", .Con "Cons" [.Con "Var" [name], .Con "Nil" []]], .Con "Cons" [pat, .Con "Cons" [template, .Con "Nil" []]]]]] => some (.Con "Some" [.Con "MkRule" [name, pat, template]])
  | _ => none

def extractRuleNone : Term → Option Term
  | .Con "extractRule" [other] => some (.Con "None" [])
  | _ => none

def parseWithGrammar : Term → Option Term
  | .Con "parseWithGrammar" [.Con "MkGrammar" [prods, tokProds, syms, start], input] => some (.Con "let" [.Var "tokens", .Con "tokenize" [input], .Con "let" [.Var "state", .Con "MkState" [.Var "tokens", .Lit "0"], .Con "parseProduction" [start, prods, .Var "state"]]])
  | _ => none

def parseProduction : Term → Option Term
  | .Con "parseProduction" [name, prods, state] => some (.Con "case" [.Con "findProd" [name, prods], .Con "Some" [.Con "MkProd" [.Var "n", .Var "g", .Var "c"]], .Con "parse" [.Var "g", state], .Con "None" [], .Con "ParseFail" [.Con "concat" [.Lit "\"unknown production: \"", name], state]])
  | _ => none

def findProdHit : Term → Option Term
  | .Con "findProd" [name, .Con "Cons" [.Con "MkProd" [name_0, g, c], rest]] => if name_0 == name then some (.Con "Some" [.Con "MkProd" [name, g, c]]) else none
  | _ => none

def findProdMiss : Term → Option Term
  | .Con "findProd" [name, .Con "Cons" [.Con "MkProd" [other, g, c], rest]] => some (.Con "findProd" [name, rest])
  | _ => none

def findProdEmpty : Term → Option Term
  | .Con "findProd" [name, .Con "Nil" []] => some (.Con "None" [])
  | _ => none

def printWithGrammar : Term → Option Term
  | .Con "printWithGrammar" [.Con "MkGrammar" [prods, tokProds, syms, start], prodName, term] => some (.Con "case" [.Con "findProd" [prodName, prods], .Con "Some" [.Con "MkProd" [.Var "n", .Var "g", .Var "c"]], .Con "print" [.Var "g", term], .Con "None" [], .Con "PrintFail" [.Con "concat" [.Lit "\"unknown production: \"", prodName]]])
  | _ => none

def stripQuotes : Term → Option Term
  | .Con "stripQuotes" [s] => some (.Con "if" [.Con "and" [.Con "startsWith" [s, .Lit "\"\\\"\""], .Con "endsWith" [s, .Lit "\"\\\"\""]], .Con "drop" [.Lit "1", .Con "dropRight" [.Lit "1", s]], s])
  | _ => none

def stripAngleBrackets : Term → Option Term
  | .Con "stripAngleBrackets" [s] => some (.Con "if" [.Con "and" [.Con "startsWith" [s, .Lit "\"<\""], .Con "endsWith" [s, .Lit "\">\""]], .Con "drop" [.Lit "1", .Con "dropRight" [.Lit "1", s]], s])
  | _ => none

def splitByPipe : Term → Option Term
  | .Con "splitByPipe" [ts] => some (.Con "splitBy" [.Con "Lit" [.Lit "\"|\""], ts])
  | _ => none

def getList : Term → Option Term
  | .Con "getList" [.Con "Con" [.Lit "\"list\"", xs]] => some (xs)
  | _ => none

def getListOther : Term → Option Term
  | .Con "getList" [v_t] => some (.Con "Cons" [v_t, .Con "Nil" []])
  | _ => none

def rtGrammar : Term → Option Term
  | .Con "rtGrammar" [.Con "MkRuntime" [grammar, rules]] => some (grammar)
  | _ => none

def rtRules : Term → Option Term
  | .Con "rtRules" [.Con "MkRuntime" [grammar, rules]] => some (rules)
  | _ => none

def loadBootstrap : Term → Option Term
  | .Con "loadBootstrap" [content] => some (.Con "case" [.Con "parseBootstrap" [content], .Con "Some" [.Var "ast"], .Con "let" [.Var "prods", .Con "extractProductions" [.Var "ast"], .Con "let" [.Var "rules", .Con "extractRules" [.Var "ast"], .Con "Some" [.Con "MkRuntime" [.Con "MkGrammar" [.Var "prods", .Con "Nil" [], .Con "Nil" [], .Lit "\"File.legoFile\""], .Var "rules"]]]], .Con "None" [], .Con "None" []])
  | _ => none

def parseBootstrap : Term → Option Term
  | .Con "parseBootstrap" [content] => some (.Con "hardcodedParse" [content])
  | _ => none

def loadLego : Term → Option Term
  | .Con "loadLego" [bootstrapRt, content] => some (.Con "case" [.Con "parseLegoFile" [bootstrapRt, content], .Con "Some" [.Var "ast"], .Con "let" [.Var "prods", .Con "extractProductions" [.Var "ast"], .Con "let" [.Var "rules", .Con "extractRules" [.Var "ast"], .Con "let" [.Var "bootstrapProds", .Con "rtGrammar" [bootstrapRt], .Con "Some" [.Con "MkRuntime" [.Con "MkGrammar" [.Con "append" [.Var "prods", .Con "grammarProds" [.Var "bootstrapProds"]], .Con "Nil" [], .Con "Nil" [], .Lit "\"File.legoFile\""], .Con "append" [.Var "rules", .Con "rtRules" [bootstrapRt]]]]]]], .Con "None" [], .Con "None" []])
  | _ => none

def parseLegoFile : Term → Option Term
  | .Con "parseLegoFile" [rt, content] => some (.Con "parseWithGrammar" [.Con "rtGrammar" [rt], content])
  | _ => none

def parseLegoFileE : Term → Option Term
  | .Con "parseLegoFileE" [rt, content] => some (.Con "case" [.Con "parseWithGrammar" [.Con "rtGrammar" [rt], content], .Con "ParseOk" [.Var "t", .Var "s"], .Con "Ok" [.Var "t"], .Con "ParseFail" [.Var "msg", .Var "s"], .Con "Err" [.Var "msg"]])
  | _ => none

def loadLanguage : Term → Option Term
  | .Con "loadLanguage" [rt, path] => some (.Con "loadLanguageWithParents" [rt, path, .Con "Nil" []])
  | _ => none

def loadLanguageWithParents : Term → Option Term
  | .Con "loadLanguageWithParents" [rt, path, visited] => some (.Con "if" [.Con "elem" [path, visited], .Con "Err" [.Con "concat" [.Lit "\"Circular language inheritance: \"", path]], .Con "case" [.Con "readFile" [path], .Con "Some" [.Var "content"], .Con "loadLanguageContent" [rt, path, .Var "content", .Con "Cons" [path, visited]], .Con "None" [], .Con "Err" [.Con "concat" [.Lit "\"Cannot read file: \"", path]]]])
  | _ => none

def loadLanguageContent : Term → Option Term
  | .Con "loadLanguageContent" [rt, path, content, visited] => some (.Con "case" [.Con "parseLegoFile" [rt, content], .Con "Some" [.Var "ast"], .Con "let" [.Var "parentNames", .Con "extractParentNames" [.Var "ast"], .Con "loadWithParents" [rt, path, .Var "ast", .Var "parentNames", visited]], .Con "None" [], .Con "Err" [.Lit "\"parse failed\""]])
  | _ => none

def loadWithParents : Term → Option Term
  | .Con "loadWithParents" [rt, path, ast, parentNames, visited] => some (.Con "case" [.Con "loadParentGrammars" [rt, path, parentNames, visited], .Con "Ok" [.Var "inheritedProds", .Var "inheritedTokProds"], .Con "let" [.Var "childProds", .Con "extractProductions" [ast], .Con "let" [.Var "childTokProds", .Con "extractTokenProductions" [ast], .Con "let" [.Var "mergedProds", .Con "append" [.Var "inheritedProds", .Var "childProds"], .Con "let" [.Var "mergedTokProds", .Con "append" [.Var "inheritedTokProds", .Var "childTokProds"], .Con "let" [.Var "syms", .Con "extractSymbols" [.Var "mergedProds"], .Con "let" [.Var "start", .Con "findStartProd" [.Var "childProds"], .Con "Ok" [.Con "MkGrammar" [.Var "mergedProds", .Var "mergedTokProds", .Var "syms", .Var "start"]]]]]]]], .Con "Err" [.Var "e"], .Con "Err" [.Var "e"]])
  | _ => none

def loadParentGrammars : Term → Option Term
  | .Con "loadParentGrammars" [rt, childPath, .Con "Nil" [], visited] => some (.Con "Ok" [.Con "Nil" [], .Con "Nil" []])
  | _ => none

def loadParentGrammarsNonEmpty : Term → Option Term
  | .Con "loadParentGrammars" [rt, childPath, .Con "Cons" [parent, rest], visited] => some (.Con "case" [.Con "resolveParentPath" [parent, childPath], .Con "Some" [.Var "parentPath"], .Con "case" [.Con "loadLanguageWithParents" [rt, .Var "parentPath", visited], .Con "Ok" [.Var "parentGrammar"], .Con "case" [.Con "loadParentGrammars" [rt, childPath, rest, visited], .Con "Ok" [.Var "restProds", .Var "restTokProds"], .Con "Ok" [.Con "append" [.Con "grammarProds" [.Var "parentGrammar"], .Var "restProds"], .Con "append" [.Con "grammarTokProds" [.Var "parentGrammar"], .Var "restTokProds"]], .Con "Err" [.Var "e"], .Con "Err" [.Var "e"]], .Con "Err" [.Var "e"], .Con "Err" [.Con "concat" [.Lit "\"Failed to load parent \"", .Con "concat" [parent, .Con "concat" [.Lit "\": \"", .Var "e"]]]]], .Con "None" [], .Con "if" [.Con "eq" [parent, .Lit "\"Bootstrap\""], .Con "case" [.Con "loadParentGrammars" [rt, childPath, rest, visited], .Con "Ok" [.Var "restProds", .Var "restTokProds"], .Con "Ok" [.Con "append" [.Con "grammarProds" [.Con "rtGrammar" [rt]], .Var "restProds"], .Con "append" [.Con "grammarTokProds" [.Con "rtGrammar" [rt]], .Var "restTokProds"]], .Con "Err" [.Var "e"], .Con "Err" [.Var "e"]], .Con "Err" [.Con "concat" [.Lit "\"Cannot find parent language: \"", parent]]]])
  | _ => none

def resolveParentPath : Term → Option Term
  | .Con "resolveParentPath" [parentName, childPath] => some (.Con "findFirst" [.Con "fileExists" [], .Con "Cons" [.Con "concat" [.Con "dirname" [childPath], .Con "concat" [.Lit "\"/\"", .Con "concat" [parentName, .Lit "\".lego\""]]], .Con "Cons" [.Con "concat" [.Lit "\"test/\"", .Con "concat" [parentName, .Lit "\".lego\""]], .Con "Cons" [.Con "concat" [.Lit "\"src/Lego/\"", .Con "concat" [parentName, .Lit "\".lego\""]], .Con "Cons" [.Con "concat" [.Lit "\"src/Rosetta/\"", .Con "concat" [parentName, .Lit "\".lego\""]], .Con "Nil" []]]]]])
  | _ => none

def grammarProds : Term → Option Term
  | .Con "grammarProds" [.Con "MkGrammar" [prods, tokProds, syms, start]] => some (prods)
  | _ => none

def grammarTokProds : Term → Option Term
  | .Con "grammarTokProds" [.Con "MkGrammar" [prods, tokProds, syms, start]] => some (tokProds)
  | _ => none

def extractTokenProductions : Term → Option Term
  | .Con "extractTokenProductions" [ast] => some (.Con "filter" [.Con "isTokenProd" [], .Con "extractProductions" [ast]])
  | _ => none

def isTokenProd : Term → Option Term
  | .Con "isTokenProd" [.Con "MkProd" [name, g, c]] => some (.Con "startsWith" [name, .Lit "\"TOKEN.\""])
  | _ => none

def extractSymbols : Term → Option Term
  | .Con "extractSymbols" [prods] => some (.Con "nub" [.Con "concatMap" [.Con "prodSymbols" [], prods]])
  | _ => none

def prodSymbols : Term → Option Term
  | .Con "prodSymbols" [.Con "MkProd" [name, g, c]] => some (.Con "grammarSymbols" [g])
  | _ => none

def grammarSymbolsRef : Term → Option Term
  | .Con "grammarSymbols" [.Con "GRef" [name]] => some (.Con "Cons" [name, .Con "Nil" []])
  | _ => none

def grammarSymbolsSeq : Term → Option Term
  | .Con "grammarSymbols" [.Con "GSeq" [g1, g2]] => some (.Con "append" [.Con "grammarSymbols" [g1], .Con "grammarSymbols" [g2]])
  | _ => none

def grammarSymbolsAlt : Term → Option Term
  | .Con "grammarSymbols" [.Con "GAlt" [g1, g2]] => some (.Con "append" [.Con "grammarSymbols" [g1], .Con "grammarSymbols" [g2]])
  | _ => none

def grammarSymbolsStar : Term → Option Term
  | .Con "grammarSymbols" [.Con "GStar" [g]] => some (.Con "grammarSymbols" [g])
  | _ => none

def grammarSymbolsOther : Term → Option Term
  | .Con "grammarSymbols" [g] => some (.Con "Nil" [])
  | _ => none

def findStartProd : Term → Option Term
  | .Con "findStartProd" [.Con "Cons" [.Con "MkProd" [name, g, c], rest]] => some (name)
  | _ => none

def findStartProdEmpty : Term → Option Term
  | .Con "findStartProd" [.Con "Nil" []] => some (.Lit "\"File.legoFile\"")
  | _ => none

def normalize : Term → Option Term
  | .Con "normalize" [rt, term] => some (.Con "normalizeWith" [.Lit "1000", .Con "rtRules" [rt], term])
  | _ => none

def normalizeWith : Term → Option Term
  | .Con "normalizeWith" [.Lit "0", rules, v_t] => some (v_t)
  | _ => none

def normalizeWithFuel : Term → Option Term
  | .Con "normalizeWith" [n, rules, v_t] => some (.Con "case" [.Con "tryApplyRules" [rules, v_t], .Con "Some" [.Var "t'"], .Con "normalizeWith" [.Con "sub" [n, .Lit "1"], rules, .Var "t'"], .Con "None" [], .Con "normalizeChildren" [n, rules, v_t]])
  | _ => none

def tryApplyRules : Term → Option Term
  | .Con "tryApplyRules" [.Con "Cons" [.Con "MkRule" [name, pat, tmpl], rest], v_t] => some (.Con "case" [.Con "matchPat" [pat, v_t], .Con "Some" [.Var "bindings"], .Con "Some" [.Con "subst" [tmpl, .Var "bindings"]], .Con "None" [], .Con "tryApplyRules" [rest, v_t]])
  | _ => none

def tryApplyRulesEmpty : Term → Option Term
  | .Con "tryApplyRules" [.Con "Nil" [], v_t] => some (.Con "None" [])
  | _ => none

def normalizeChildren : Term → Option Term
  | .Con "normalizeChildren" [n, rules, .Con "Var" [x]] => some (.Con "Var" [x])
  | _ => none

def printTerm : Term → Option Term
  | .Con "printTerm" [rt, term, prodName] => some (.Con "case" [.Con "printWithGrammar" [.Con "rtGrammar" [rt], prodName, term], .Con "PrintOk" [.Var "tokens"], .Con "Some" [.Con "joinTokens" [.Var "tokens"]], .Con "PrintFail" [.Var "msg"], .Con "None" []])
  | _ => none

def joinTokens : Term → Option Term
  | .Con "joinTokens" [tokens] => some (.Con "intercalate" [.Lit "\" \"", .Con "map" [.Con "tokenToString" [], tokens]])
  | _ => none

def tokenToString : Term → Option Term
  | .Con "tokenToString" [.Con "TokIdent" [s]] => some (s)
  | _ => none

def tokenToStringStr : Term → Option Term
  | .Con "tokenToString" [.Con "TokString" [s]] => some (.Con "concat" [.Lit "\"\\\"\"", .Con "concat" [s, .Lit "\"\\\"\""]])
  | _ => none

def tokenToStringSym : Term → Option Term
  | .Con "tokenToString" [.Con "TokSym" [s]] => some (s)
  | _ => none

def initRuntime : Term → Option Term
  | .Con "initRuntime" [bootstrapContent, legoContent] => some (.Con "case" [.Con "loadBootstrap" [bootstrapContent], .Con "Some" [.Var "bootstrapRt"], .Con "case" [.Con "loadLego" [.Var "bootstrapRt", legoContent], .Con "Some" [.Var "legoRt"], .Con "Ok" [.Var "legoRt"], .Con "None" [], .Con "Err" [.Lit "\"failed to load Lego.lego\""]], .Con "None" [], .Con "Err" [.Lit "\"failed to load Bootstrap.lego\""]])
  | _ => none

def valErrorFormat : Term → Option Term
  | .Con "valErrorFormat" [.Con "UndefinedProduction" [ref, source]] => some (.Con "concat" [.Con "concat" [.Con "concat" [.Lit "\"ERROR: Undefined production '\"", ref], .Lit "\"' referenced from '\""], .Con "concat" [source, .Lit "\"'\""]])
  | _ => none

def valErrorFormatDup : Term → Option Term
  | .Con "valErrorFormat" [.Con "DuplicateProduction" [name]] => some (.Con "concat" [.Con "concat" [.Lit "\"ERROR: Duplicate production '\"", name], .Lit "\"'\""])
  | _ => none

def valErrorFormatUnbound : Term → Option Term
  | .Con "valErrorFormat" [.Con "UnboundVariable" [var, rule]] => some (.Con "concat" [.Con "concat" [.Con "concat" [.Con "concat" [.Lit "\"ERROR: Unbound variable '\"", var], .Lit "\"' in rule '\""], rule], .Lit "\"'\""])
  | _ => none

def valErrorFormatCircular : Term → Option Term
  | .Con "valErrorFormat" [.Con "CircularImport" [mod]] => some (.Con "concat" [.Con "concat" [.Lit "\"ERROR: Circular import of '\"", mod], .Lit "\"'\""])
  | _ => none

def valErrorFormatInvalid : Term → Option Term
  | .Con "valErrorFormat" [.Con "InvalidSyntax" [ctx, msg]] => some (.Con "concat" [.Con "concat" [.Con "concat" [.Lit "\"ERROR: Invalid syntax in \"", ctx], .Lit "\": \""], msg])
  | _ => none

def valWarnFormatConflict : Term → Option Term
  | .Con "valWarnFormat" [.Con "ConflictingRules" [r1, r2, reason]] => some (.Con "concat" [.Con "concat" [.Con "concat" [.Con "concat" [.Con "concat" [.Lit "\"WARNING: Conflicting rules '\"", r1], .Lit "\"' and '\""], r2], .Lit "\"': \""], reason])
  | _ => none

def valWarnFormatDirectLR : Term → Option Term
  | .Con "valWarnFormat" [.Con "DirectLeftRecursion" [name]] => some (.Con "concat" [.Con "concat" [.Lit "\"WARNING: Direct left recursion in production '\"", name], .Lit "\"'\""])
  | _ => none

def valWarnFormatIndirectLR : Term → Option Term
  | .Con "valWarnFormat" [.Con "IndirectLeftRecursion" [path]] => some (.Con "concat" [.Lit "\"WARNING: Indirect left recursion: \"", .Con "intercalate" [.Lit "\" -> \"", path]])
  | _ => none

def valWarnFormatUnused : Term → Option Term
  | .Con "valWarnFormat" [.Con "UnusedProduction" [name]] => some (.Con "concat" [.Con "concat" [.Lit "\"WARNING: Unused production '\"", name], .Lit "\"'\""])
  | _ => none

def valWarnFormatShadow : Term → Option Term
  | .Con "valWarnFormat" [.Con "ShadowedProduction" [name, by]] => some (.Con "concat" [.Con "concat" [.Con "concat" [.Con "concat" [.Lit "\"WARNING: Production '\"", name], .Lit "\"' shadowed by '\""], by], .Lit "\"'\""])
  | _ => none

def valWarnFormatAmbig : Term → Option Term
  | .Con "valWarnFormat" [.Con "AmbiguousGrammar" [name, reason]] => some (.Con "concat" [.Con "concat" [.Con "concat" [.Con "concat" [.Lit "\"WARNING: Ambiguous grammar for '\"", name], .Lit "\"': \""], reason], .Lit "\"\""])
  | _ => none

def valWarnFormatMissingCut : Term → Option Term
  | .Con "valWarnFormat" [.Con "MissingCut" [prod, kw]] => some (.Con "concat" [.Con "concat" [.Con "concat" [.Con "concat" [.Lit "\"OPTIMIZE: Production '\"", prod], .Lit "\"' could add cut after '\""], kw], .Lit "\"' for better errors\""])
  | _ => none

def valWarnFormatCycle : Term → Option Term
  | .Con "valWarnFormat" [.Con "RuleCycle" [cycle]] => some (.Con "concat" [.Lit "\"WARNING: Potential non-terminating rule cycle: \"", .Con "intercalate" [.Lit "\" -> \"", cycle]])
  | _ => none

def valWarnFormatUnreachable : Term → Option Term
  | .Con "valWarnFormat" [.Con "UnreachableAlt" [prod, idx]] => some (.Con "concat" [.Con "concat" [.Con "concat" [.Lit "\"WARNING: Alternative \"", .Con "toString" [idx]], .Lit "\" in '\""], .Con "concat" [prod, .Lit "\"' is unreachable\""]])
  | _ => none

def valWarnFormatRedundant : Term → Option Term
  | .Con "valWarnFormat" [.Con "RedundantAlt" [prod, i, j]] => some (.Con "concat" [.Con "concat" [.Con "concat" [.Con "concat" [.Con "concat" [.Lit "\"WARNING: Alternatives \"", .Con "toString" [i]], .Lit "\" and \""], .Con "toString" [j]], .Lit "\" in '\""], .Con "concat" [prod, .Lit "\"' are redundant\""]])
  | _ => none

def valResultEmpty : Term → Option Term
  | .Con "valResultEmpty" [] => some (.Con "MkValidationResult" [.Con "Nil" [], .Con "Nil" []])
  | _ => none

def valResultAppend : Term → Option Term
  | .Con "valResultAppend" [.Con "MkValidationResult" [e1, w1], .Con "MkValidationResult" [e2, w2]] => some (.Con "MkValidationResult" [.Con "append" [e1, e2], .Con "append" [w1, w2]])
  | _ => none

def valResultAddError : Term → Option Term
  | .Con "valResultAddError" [.Con "MkValidationResult" [errs, warns], e] => some (.Con "MkValidationResult" [.Con "Cons" [e, errs], warns])
  | _ => none

def valResultAddWarning : Term → Option Term
  | .Con "valResultAddWarning" [.Con "MkValidationResult" [errs, warns], w] => some (.Con "MkValidationResult" [errs, .Con "Cons" [w, warns]])
  | _ => none

def valResultHasErrors : Term → Option Term
  | .Con "valResultHasErrors" [.Con "MkValidationResult" [errs, warns]] => some (.Con "not" [.Con "null" [errs]])
  | _ => none

def valResultFormat : Term → Option Term
  | .Con "valResultFormat" [.Con "MkValidationResult" [errs, warns]] => some (.Con "append" [.Con "map" [.Con "valErrorFormat" [], errs], .Con "map" [.Con "valWarnFormat" [], warns]])
  | _ => none

def builtinProductions : Term → Option Term
  | .Con "builtinProductions" [] => some (.Con "Cons" [.Lit "\"nat\"", .Con "Cons" [.Lit "\"int\"", .Con "Cons" [.Lit "\"str\"", .Con "Cons" [.Lit "\"string\"", .Con "Cons" [.Lit "\"ident\"", .Con "Cons" [.Lit "\"char\"", .Con "Cons" [.Lit "\"float\"", .Con "Cons" [.Lit "\"bool\"", .Con "Nil" []]]]]]]]])
  | _ => none

def extractRefsEmpty : Term → Option Term
  | .Con "extractRefs" [.Con "GEmpty" []] => some (.Con "Nil" [])
  | _ => none

def extractRefsLit : Term → Option Term
  | .Con "extractRefs" [.Con "GLit" [s]] => some (.Con "Nil" [])
  | _ => none

def extractRefsRef : Term → Option Term
  | .Con "extractRefs" [.Con "GRef" [name]] => some (.Con "Cons" [name, .Con "Nil" []])
  | _ => none

def extractRefsSeq : Term → Option Term
  | .Con "extractRefs" [.Con "GSeq" [g1, g2]] => some (.Con "append" [.Con "extractRefs" [g1], .Con "extractRefs" [g2]])
  | _ => none

def extractRefsAlt : Term → Option Term
  | .Con "extractRefs" [.Con "GAlt" [g1, g2]] => some (.Con "append" [.Con "extractRefs" [g1], .Con "extractRefs" [g2]])
  | _ => none

def extractRefsStar : Term → Option Term
  | .Con "extractRefs" [.Con "GStar" [g]] => some (.Con "extractRefs" [g])
  | _ => none

def extractRefsPlus : Term → Option Term
  | .Con "extractRefs" [.Con "GPlus" [g]] => some (.Con "extractRefs" [g])
  | _ => none

def extractRefsOpt : Term → Option Term
  | .Con "extractRefs" [.Con "GOpt" [g]] => some (.Con "extractRefs" [g])
  | _ => none

def extractRefsNot : Term → Option Term
  | .Con "extractRefs" [.Con "GNot" [g]] => some (.Con "extractRefs" [g])
  | _ => none

def extractRefsAnd : Term → Option Term
  | .Con "extractRefs" [.Con "GAnd" [g]] => some (.Con "extractRefs" [g])
  | _ => none

def extractRefsCon : Term → Option Term
  | .Con "extractRefs" [.Con "GCon" [name, g]] => some (.Con "extractRefs" [g])
  | _ => none

def checkUndefinedRefs : Term → Option Term
  | .Con "checkUndefinedRefs" [grammar] => some (.Con "let" [.Var "defined", .Con "grammarDefinedNames" [grammar], .Con "let" [.Var "builtins", .Con "builtinProductions" [], .Con "foldl" [.Con "acc" [.Con "binder" [.Lit "prod", .Con "let" [.Var "refs", .Con "extractRefs" [.Con "grammarLookup" [grammar, .Var "prod"]], .Con "foldl" [.Con "acc2" [.Con "binder" [.Lit "ref", .Con "if" [.Con "or" [.Con "contains" [.Var "defined", .Var "ref"], .Con "contains" [.Var "builtins", .Con "baseName" [.Var "ref"]]], .Var "acc2", .Con "valResultAddError" [.Var "acc2", .Con "UndefinedProduction" [.Var "ref", .Var "prod"]]]]], .Var "acc", .Var "refs"]]]], .Con "valResultEmpty" [], .Con "grammarProductions" [grammar]]]])
  | _ => none

def isDirectLeftRecEmpty : Term → Option Term
  | .Con "isDirectLeftRec" [name, .Con "GEmpty" []] => some (.Con "False" [])
  | _ => none

def isDirectLeftRecLit : Term → Option Term
  | .Con "isDirectLeftRec" [name, .Con "GLit" [s]] => some (.Con "False" [])
  | _ => none

def isDirectLeftRecRef : Term → Option Term
  | .Con "isDirectLeftRec" [name, .Con "GRef" [ref]] => some (.Con "eq" [ref, name])
  | _ => none

def isDirectLeftRecSeq : Term → Option Term
  | .Con "isDirectLeftRec" [name, .Con "GSeq" [g1, g2]] => some (.Con "isDirectLeftRec" [name, g1])
  | _ => none

def isDirectLeftRecAlt : Term → Option Term
  | .Con "isDirectLeftRec" [name, .Con "GAlt" [g1, g2]] => some (.Con "or" [.Con "isDirectLeftRec" [name, g1], .Con "isDirectLeftRec" [name, g2]])
  | _ => none

def isDirectLeftRecStar : Term → Option Term
  | .Con "isDirectLeftRec" [name, .Con "GStar" [g]] => some (.Con "isDirectLeftRec" [name, g])
  | _ => none

def isDirectLeftRecPlus : Term → Option Term
  | .Con "isDirectLeftRec" [name, .Con "GPlus" [g]] => some (.Con "isDirectLeftRec" [name, g])
  | _ => none

def isDirectLeftRecOpt : Term → Option Term
  | .Con "isDirectLeftRec" [name, .Con "GOpt" [g]] => some (.Con "isDirectLeftRec" [name, g])
  | _ => none

def isDirectLeftRecCon : Term → Option Term
  | .Con "isDirectLeftRec" [name, .Con "GCon" [c, g]] => some (.Con "isDirectLeftRec" [name, g])
  | _ => none

def checkLeftRecursion : Term → Option Term
  | .Con "checkLeftRecursion" [grammar] => some (.Con "foldl" [.Con "acc" [.Con "binder" [.Lit "prod", .Con "if" [.Con "isDirectLeftRec" [.Var "prod", .Con "grammarLookup" [grammar, .Var "prod"]], .Con "valResultAddWarning" [.Var "acc", .Con "DirectLeftRecursion" [.Var "prod"]], .Var "acc"]]], .Con "valResultEmpty" [], .Con "grammarProductions" [grammar]])
  | _ => none

def varsInVar : Term → Option Term
  | .Con "varsIn" [.Con "Var" [v]] => some (.Con "Cons" [v, .Con "Nil" []])
  | _ => none

def varsInLit : Term → Option Term
  | .Con "varsIn" [.Con "Lit" [s]] => some (.Con "Nil" [])
  | _ => none

def varsInCon : Term → Option Term
  | .Con "varsIn" [.Con "Con" [c, args]] => some (.Con "flatMap" [.Con "varsIn" [], args])
  | _ => none

def patternVarsVar : Term → Option Term
  | .Con "patternVars" [.Con "Var" [v]] => some (.Con "if" [.Con "startsWith" [v, .Lit "\"$\""], .Con "Cons" [v, .Con "Nil" []], .Con "Nil" []])
  | _ => none

def patternVarsLit : Term → Option Term
  | .Con "patternVars" [.Con "Lit" [s]] => some (.Con "Nil" [])
  | _ => none

def patternVarsCon : Term → Option Term
  | .Con "patternVars" [.Con "Con" [c, args]] => some (.Con "flatMap" [.Con "patternVars" [], args])
  | _ => none

def checkUnboundVars : Term → Option Term
  | .Con "checkUnboundVars" [rules] => some (.Con "foldl" [.Con "acc" [.Con "binder" [.Lit "rule", .Con "let" [.Var "patVars", .Con "patternVars" [.Con "rulePattern" [.Var "rule"]], .Con "let" [.Var "tplVars", .Con "filter" [.Con "binder" [.Lit "v", .Con "startsWith" [.Var "v", .Lit "\"$\""]], .Con "varsIn" [.Con "ruleTemplate" [.Var "rule"]]], .Con "let" [.Var "unbound", .Con "filter" [.Con "binder" [.Lit "v", .Con "not" [.Con "contains" [.Var "patVars", .Var "v"]]], .Var "tplVars"], .Con "foldl" [.Con "acc2" [.Con "binder" [.Lit "v", .Con "valResultAddError" [.Var "acc2", .Con "UnboundVariable" [.Var "v", .Con "ruleName" [.Var "rule"]]]]], .Var "acc", .Var "unbound"]]]]]], .Con "valResultEmpty" [], rules])
  | _ => none

def patternKeyVar : Term → Option Term
  | .Con "patternKey" [.Con "Var" [v]] => some (.Lit "\"_\"")
  | _ => none

def patternKeyLit : Term → Option Term
  | .Con "patternKey" [.Con "Lit" [s]] => some (.Con "concat" [.Con "concat" [.Lit "\"\\\"\"", s], .Lit "\"\\\"\""])
  | _ => none

def patternKeyCon : Term → Option Term
  | .Con "patternKey" [.Con "Con" [name, args]] => some (.Con "concat" [.Con "concat" [.Con "concat" [.Lit "\"(\"", name], .Con "concat" [.Lit "\" \"", .Con "intercalate" [.Lit "\" \"", .Con "map" [.Con "patternKey" [], args]]]], .Lit "\")\""])
  | _ => none

def checkConflictingRules : Term → Option Term
  | .Con "checkConflictingRules" [rules] => some (.Con "let" [.Var "grouped", .Con "groupBy" [.Con "binder" [.Lit "r", .Con "patternKey" [.Con "rulePattern" [.Var "r"]]], rules], .Con "foldl" [.Con "acc" [.Con "binder" [.Lit "group", .Con "if" [.Con "gt" [.Con "length" [.Var "group"], .Lit "1"], .Con "let" [.Var "names", .Con "map" [.Con "ruleName" [], .Var "group"], .Con "valResultAddWarning" [.Var "acc", .Con "ConflictingRules" [.Con "head" [.Var "names"], .Con "head" [.Con "tail" [.Var "names"]], .Lit "\"same pattern structure\""]]], .Var "acc"]]], .Con "valResultEmpty" [], .Con "mapValues" [.Var "grouped"]]])
  | _ => none

def validateGrammar : Term → Option Term
  | .Con "validateGrammar" [grammar, rules] => some (.Con "valResultAppend" [.Con "valResultAppend" [.Con "checkUndefinedRefs" [grammar], .Con "checkLeftRecursion" [grammar]], .Con "valResultAppend" [.Con "checkUnboundVars" [rules], .Con "checkConflictingRules" [rules]]])
  | _ => none

def formatValidationResult : Term → Option Term
  | .Con "formatValidationResult" [result] => some (.Con "let" [.Var "lines", .Con "valResultFormat" [result], .Con "intercalate" [.Lit "\"\\n\"", .Var "lines"]])
  | _ => none

