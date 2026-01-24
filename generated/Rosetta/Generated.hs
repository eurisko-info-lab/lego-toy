module Generated where

data Iso  a b
  = MkIso ( (a -> (Maybe b)) ) ( (b -> (Maybe a)) )
  

data Term
  = Var String
  | Lit String
  | Con String [Term]
  
  deriving (Show, Eq)

data AST  a
  = MkAST ( (String -> a) ) ( (String -> a) ) ( (String -> ([a] -> a)) )
  

data PieceLevel
  = TokenLevel
  | SyntaxLevel
  
  deriving (Show, Eq)

data Rule
  = MkRule String Term Term
  
  deriving (Show, Eq)

data TypeRule
  = MkTypeRule String Term Term
  
  deriving (Show, Eq)

data GrammarExpr
  = GEmpty
  | GLit String
  | GRef String
  | GSeq GrammarExpr GrammarExpr
  | GAlt GrammarExpr GrammarExpr
  | GStar GrammarExpr
  | GPlus GrammarExpr
  | GOpt GrammarExpr
  | GNot GrammarExpr
  | GAnd GrammarExpr
  | GCon String GrammarExpr
  
  deriving (Show, Eq)

data GrammarProduction
  = MkGrammarProduction String GrammarExpr String
  
  deriving (Show, Eq)

data Piece
  = MkPiece String PieceLevel [GrammarProduction] [Rule] [TypeRule]
  
  deriving (Show, Eq)

data Language
  = MkLanguage String [Piece]
  
  deriving (Show, Eq)

data SourceLoc
  = MkSourceLoc String Int Int Int
  | UnknownLoc
  
  deriving (Show, Eq)

data Severity
  = SevError
  | SevWarning
  | SevInfo
  
  deriving (Show, Eq)

data Binding
  = MkBinding String Term (Maybe Term) SourceLoc
  
  deriving (Show, Eq)

data TypeError
  = MkTypeError String SourceLoc Severity (Maybe Term) (Maybe Term) [Binding]
  
  deriving (Show, Eq)

data EvalResult
  = EvalOk Term [TypeError]
  | EvalFailed [TypeError]
  
  deriving (Show, Eq)

data Context
  = EmptyContext
  | ContextCons Binding Context
  
  deriving (Show, Eq)

data VarContext
  = EmptyVarContext
  | VarContextCons String VarContext
  
  deriving (Show, Eq)

data EvalEnv
  = MkEvalEnv AttrEnv Context VarContext [TypeError] SourceLoc
  
  deriving (Show, Eq)

data Mode
  = Infer
  | Check
  
  deriving (Show, Eq)

data AttrFlow
  = Syn
  | Inh
  | SynInh
  
  deriving (Show, Eq)

data AttrPath
  = Empty
  | PathCon String AttrPath
  
  deriving (Show, Eq)

data AttrRef
  = MkAttrRef AttrPath String
  
  deriving (Show, Eq)

data AttrRule
  = MkAttrRule String AttrPath Term
  
  deriving (Show, Eq)

data AttrDef
  = MkAttrDef String AttrFlow (Maybe Term) [AttrRule]
  
  deriving (Show, Eq)

data AttrEnv
  = EmptyAttrEnv
  | AttrEnvCons AttrPath String Term AttrEnv
  
  deriving (Show, Eq)

data AttrLanguage
  = MkAttrLanguage String [GrammarProduction] [AttrDef]
  
  deriving (Show, Eq)

data Token
  = TokIdent String
  | TokString String
  | TokInt Int
  | TokSym String
  | TokEOF
  
  deriving (Show, Eq)

data ParseState
  = MkState [Token] Int
  
  deriving (Show, Eq)

data ParseResult
  = ParseOk Term ParseState
  | ParseFail String ParseState
  
  deriving (Show, Eq)

data PrintResult
  = PrintOk [Token]
  | PrintFail String
  
  deriving (Show, Eq)

data Env
  = EnvEmpty
  | Bind String Term Env
  
  deriving (Show, Eq)

data Symbol
  = Terminal String
  | NonTerminal String
  | Epsilon
  
  deriving (Show, Eq)

data Production
  = MkProd String [Symbol] String
  
  deriving (Show, Eq)

data Grammar
  = MkGrammar [Production]
  
  deriving (Show, Eq)

data Parser
  = MkParser Grammar ( (String -> (Maybe Term)) )
  

data Printer
  = MkPrinter Grammar ( (Term -> (Maybe String)) )
  

data LoadedGrammar
  = LoadedGrammarMkGrammar [Production] [Production] [String] String
  
  deriving (Show, Eq)

data Runtime
  = MkRuntime LoadedGrammar [Rule]
  
  deriving (Show, Eq)

data ValidationSeverity
  = ValError
  | ValWarning
  | ValInfo
  
  deriving (Show, Eq)

data ValidationError
  = UndefinedProduction String String
  | DuplicateProduction String
  | UnboundVariable String String
  | CircularImport String
  | InvalidSyntax String String
  
  deriving (Show, Eq)

data ValidationWarning
  = ConflictingRules String String String
  | DirectLeftRecursion String
  | IndirectLeftRecursion [String]
  | UnusedProduction String
  | ShadowedProduction String String
  | AmbiguousGrammar String String
  | MissingCut String String
  | RuleCycle [String]
  | UnreachableAlt String Int
  | RedundantAlt String Int Int
  
  deriving (Show, Eq)

data ValidationResult
  = MkValidationResult [ValidationError] [ValidationWarning]
  
  deriving (Show, Eq)

isoId :: Term -> Maybe Term
isoId (Con "isoId" []) = Just (Con "MkIso" [Con "Lam" [Con "binder" [Lit "x", Con "Some" [Con "x" []]]], Con "Lam" [Con "binder" [Lit "x", Con "Some" [Con "x" []]]]])
isoId _ = Nothing

isoComp :: Term -> Maybe Term
isoComp (Con "comp" [(Con "MkIso" [f1, b1]), (Con "MkIso" [f2, b2])]) = Just (Con "MkIso" [Con "Lam" [Con "binder" [Lit "a", Con "bind" [Con "App" [f1, Con "a" []], Con "b" [], Con "App" [f2, Con "b" []]]]], Con "Lam" [Con "binder" [Lit "c", Con "bind" [Con "App" [b2, Con "c" []], Con "b" [], Con "App" [b1, Con "b" []]]]]])
isoComp _ = Nothing

isoSym :: Term -> Maybe Term
isoSym (Con "sym" [(Con "MkIso" [fwd, bwd])]) = Just (Con "MkIso" [bwd, fwd])
isoSym _ = Nothing

isoForward :: Term -> Maybe Term
isoForward (Con "forward" [(Con "MkIso" [fwd, bwd]), x]) = Just (Con "App" [fwd, x])
isoForward _ = Nothing

isoBackward :: Term -> Maybe Term
isoBackward (Con "backward" [(Con "MkIso" [fwd, bwd]), x]) = Just (Con "App" [bwd, x])
isoBackward _ = Nothing

isoPar :: Term -> Maybe Term
isoPar (Con "par" [(Con "MkIso" [f1, b1]), (Con "MkIso" [f2, b2])]) = Just (Con "MkIso" [Con "Lam" [Con "binder" [Lit "p", Con "bind" [Con "App" [f1, Con "Fst" [Con "p" []]], Con "x" [], Con "bind" [Con "App" [f2, Con "Snd" [Con "p" []]], Con "y" [], Con "Some" [Con "Pair" [Con "x" [], Con "y" []]]]]]], Con "Lam" [Con "binder" [Lit "p", Con "bind" [Con "App" [b1, Con "Fst" [Con "p" []]], Con "x" [], Con "bind" [Con "App" [b2, Con "Snd" [Con "p" []]], Con "y" [], Con "Some" [Con "Pair" [Con "x" [], Con "y" []]]]]]]])
isoPar _ = Nothing

isoOrElse :: Term -> Maybe Term
isoOrElse (Con "orElse" [(Con "MkIso" [f1, b1]), (Con "MkIso" [f2, b2])]) = Just (Con "MkIso" [Con "Lam" [Con "binder" [Lit "a", Con "case" [Con "App" [f1, Con "a" []], Con "Some" [Var "x"], Con "Some" [Var "x"], Con "None" [], Con "App" [f2, Con "a" []]]]], Con "Lam" [Con "binder" [Lit "b", Con "case" [Con "App" [b1, Con "b" []], Con "Some" [Var "x"], Con "Some" [Var "x"], Con "None" [], Con "App" [b2, Con "b" []]]]]])
isoOrElse _ = Nothing

termAtom :: Term -> Maybe Term
termAtom (Con "atom" [s]) = Just (Con "Con" [s, Con "Nil" []])
termAtom _ = Nothing

termApp :: Term -> Maybe Term
termApp (Con "app" [f, args]) = Just (Con "Con" [f, args])
termApp _ = Nothing

matchMeta :: Term -> Maybe Term
matchMeta (Con "matchPat" [(Con "Var" [name]), v_t]) = Just (Con "Some" [Con "Cons" [Con "Pair" [name, v_t], Con "Nil" []]])
matchMeta _ = Nothing

matchVarSame :: Term -> Maybe Term
matchVarSame (Con "matchPat" [(Con "Var" [name]), (Con "Var" [name0])]) | name0 == name = Just (Con "Some" [Con "Nil" []])
matchVarSame _ = Nothing

matchVarDiff :: Term -> Maybe Term
matchVarDiff (Con "matchPat" [(Con "Var" [a]), (Con "Var" [b])]) = Just (Con "None" [])
matchVarDiff _ = Nothing

matchLitSame :: Term -> Maybe Term
matchLitSame (Con "matchPat" [(Con "Lit" [s]), (Con "Lit" [s0])]) | s0 == s = Just (Con "Some" [Con "Nil" []])
matchLitSame _ = Nothing

matchLitDiff :: Term -> Maybe Term
matchLitDiff (Con "matchPat" [(Con "Lit" [a]), (Con "Lit" [b])]) = Just (Con "None" [])
matchLitDiff _ = Nothing

matchConSame :: Term -> Maybe Term
matchConSame (Con "matchPat" [(Con "Con" [n, pats]), (Con "Con" [n0, args])]) | n0 == n = Just (Con "matchArgs" [pats, args])
matchConSame _ = Nothing

matchConDiff :: Term -> Maybe Term
matchConDiff (Con "matchPat" [(Con "Con" [n1, pats]), (Con "Con" [n2, args])]) = Just (Con "None" [])
matchConDiff _ = Nothing

matchArgsNil :: Term -> Maybe Term
matchArgsNil (Con "matchArgs" [(Con "Nil" []), (Con "Nil" [])]) = Just (Con "Some" [Con "Nil" []])
matchArgsNil _ = Nothing

matchArgsCons :: Term -> Maybe Term
matchArgsCons (Con "matchArgs" [(Con "Cons" [p, ps]), (Con "Cons" [a, as])]) = Just (Con "merge" [Con "matchPat" [p, a], Con "matchArgs" [ps, as]])
matchArgsCons _ = Nothing

matchArgsMismatch :: Term -> Maybe Term
matchArgsMismatch (Con "matchArgs" [ps, as]) = Just (Con "None" [])
matchArgsMismatch _ = Nothing

mergeBindings :: Term -> Maybe Term
mergeBindings (Con "merge" [(Con "Some" [bs1]), (Con "Some" [bs2])]) = Just (Con "Some" [Con "append" [bs1, bs2]])
mergeBindings _ = Nothing

mergeFail :: Term -> Maybe Term
mergeFail (Con "merge" [(Con "None" []), x]) = Just (Con "None" [])
mergeFail _ = Nothing

substVar :: Term -> Maybe Term
substVar (Con "subst" [(Con "Var" [name]), bindings]) = Just (Con "lookup" [name, bindings])
substVar _ = Nothing

substLit :: Term -> Maybe Term
substLit (Con "subst" [(Con "Lit" [s]), bindings]) = Just (Con "Lit" [s])
substLit _ = Nothing

substCon :: Term -> Maybe Term
substCon (Con "subst" [(Con "Con" [n, args]), bindings]) = Just (Con "Con" [n, Con "map" [Con "Lam" [Con "binder" [Lit "t", Con "subst" [Con "t" [], bindings]]], args]])
substCon _ = Nothing

lookupHit :: Term -> Maybe Term
lookupHit (Con "lookup" [name, (Con "Cons" [(Con "Pair" [name0, val]), rest])]) | name0 == name = Just (val)
lookupHit _ = Nothing

lookupMiss :: Term -> Maybe Term
lookupMiss (Con "lookup" [name, (Con "Cons" [(Con "Pair" [other, val]), rest])]) = Just (Con "lookup" [name, rest])
lookupMiss _ = Nothing

lookupEmpty :: Term -> Maybe Term
lookupEmpty (Con "lookup" [name, (Con "Nil" [])]) = Just (Con "Var" [name])
lookupEmpty _ = Nothing

astVar :: Term -> Maybe Term
astVar (Con "astVar" [(Con "MkAST" [var, lit, con]), s]) = Just (Con "App" [var, s])
astVar _ = Nothing

astLit :: Term -> Maybe Term
astLit (Con "astLit" [(Con "MkAST" [var, lit, con]), s]) = Just (Con "App" [lit, s])
astLit _ = Nothing

astCon :: Term -> Maybe Term
astCon (Con "astCon" [(Con "MkAST" [var, lit, con]), name, args]) = Just (Con "App" [Con "App" [con, name], args])
astCon _ = Nothing

defaultAST :: Term -> Maybe Term
defaultAST (Con "defaultAST" []) = Just (Con "MkAST" [Con "Var" [], Con "Lit" [], Con "Con" []])
defaultAST _ = Nothing

languageName :: Term -> Maybe Term
languageName (Con "languageName" [(Con "MkLanguage" [name, pieces])]) = Just (name)
languageName _ = Nothing

languagePieces :: Term -> Maybe Term
languagePieces (Con "languagePieces" [(Con "MkLanguage" [name, pieces])]) = Just (pieces)
languagePieces _ = Nothing

languageAllGrammar :: Term -> Maybe Term
languageAllGrammar (Con "languageAllGrammar" [(Con "MkLanguage" [name, pieces])]) = Just (Con "flatMap" [Con "pieceGrammar" [], pieces])
languageAllGrammar _ = Nothing

languageAllRules :: Term -> Maybe Term
languageAllRules (Con "languageAllRules" [(Con "MkLanguage" [name, pieces])]) = Just (Con "flatMap" [Con "pieceRules" [], pieces])
languageAllRules _ = Nothing

pieceName :: Term -> Maybe Term
pieceName (Con "pieceName" [(Con "MkPiece" [name, level, grammar, rules, typeRules])]) = Just (name)
pieceName _ = Nothing

pieceLevel :: Term -> Maybe Term
pieceLevel (Con "pieceLevel" [(Con "MkPiece" [name, level, grammar, rules, typeRules])]) = Just (level)
pieceLevel _ = Nothing

pieceGrammar :: Term -> Maybe Term
pieceGrammar (Con "pieceGrammar" [(Con "MkPiece" [name, level, grammar, rules, typeRules])]) = Just (grammar)
pieceGrammar _ = Nothing

pieceRules :: Term -> Maybe Term
pieceRules (Con "pieceRules" [(Con "MkPiece" [name, level, grammar, rules, typeRules])]) = Just (rules)
pieceRules _ = Nothing

pieceTypeRules :: Term -> Maybe Term
pieceTypeRules (Con "pieceTypeRules" [(Con "MkPiece" [name, level, grammar, rules, typeRules])]) = Just (typeRules)
pieceTypeRules _ = Nothing

ruleName :: Term -> Maybe Term
ruleName (Con "ruleName" [(Con "MkRule" [name, pattern, template])]) = Just (name)
ruleName _ = Nothing

rulePattern :: Term -> Maybe Term
rulePattern (Con "rulePattern" [(Con "MkRule" [name, pattern, template])]) = Just (pattern)
rulePattern _ = Nothing

ruleTemplate :: Term -> Maybe Term
ruleTemplate (Con "ruleTemplate" [(Con "MkRule" [name, pattern, template])]) = Just (template)
ruleTemplate _ = Nothing

sourceLocToString :: Term -> Maybe Term
sourceLocToString (Con "sourceLocToString" [(Con "MkSourceLoc" [file, line, col, span])]) = Just (Con "concat" [Con "concat" [Con "concat" [Con "concat" [file, Lit "\":\""], Con "toString" [line]], Lit "\":\""], Con "toString" [col]])
sourceLocToString _ = Nothing

sourceLocToStringUnknown :: Term -> Maybe Term
sourceLocToStringUnknown (Con "sourceLocToString" [(Con "UnknownLoc" [])]) = Just (Lit "\"<unknown>:0:0\"")
sourceLocToStringUnknown _ = Nothing

typeErrorSimple :: Term -> Maybe Term
typeErrorSimple (Con "typeErrorSimple" [msg, loc]) = Just (Con "MkTypeError" [msg, loc, Con "SevError" [], Con "None" [], Con "None" [], Con "Nil" []])
typeErrorSimple _ = Nothing

typeErrorMismatch :: Term -> Maybe Term
typeErrorMismatch (Con "typeErrorMismatch" [expected, actual, loc]) = Just (Con "MkTypeError" [Lit "\"type mismatch\"", loc, Con "SevError" [], Con "Some" [expected], Con "Some" [actual], Con "Nil" []])
typeErrorMismatch _ = Nothing

typeErrorUndefined :: Term -> Maybe Term
typeErrorUndefined (Con "typeErrorUndefined" [name, loc]) = Just (Con "MkTypeError" [Con "concat" [Lit "\"undefined: \"", name], loc, Con "SevError" [], Con "None" [], Con "None" [], Con "Nil" []])
typeErrorUndefined _ = Nothing

typeErrorToString :: Term -> Maybe Term
typeErrorToString (Con "typeErrorToString" [(Con "MkTypeError" [msg, loc, sev, exp, act, ctx])]) = Just (Con "let" [Var "sevStr", Con "match" [sev, Con "SevError" [], Lit "\"error\"", Con "SevWarning" [], Lit "\"warning\"", Con "SevInfo" [], Lit "\"info\""], Con "let" [Var "locStr", Con "sourceLocToString" [loc], Con "let" [Var "base", Con "concat" [Con "concat" [Con "concat" [Var "locStr", Lit "\": \""], Var "sevStr"], Con "concat" [Lit "\": \"", msg]], Con "match" [exp, Con "Some" [Var "e"], Con "match" [act, Con "Some" [Var "a"], Con "concat" [Con "concat" [Con "concat" [Var "base", Lit "\"\\n  expected: \""], Con "termToString" [Var "e"]], Con "concat" [Lit "\"\\n  actual: \"", Con "termToString" [Var "a"]]], Con "None" [], Var "base"], Con "None" [], Var "base"]]]])
typeErrorToString _ = Nothing

evalResultPure :: Term -> Maybe Term
evalResultPure (Con "evalResultPure" [a]) = Just (Con "EvalOk" [a, Con "Nil" []])
evalResultPure _ = Nothing

evalResultMapOk :: Term -> Maybe Term
evalResultMapOk (Con "evalResultMap" [f, (Con "EvalOk" [a, errs])]) = Just (Con "EvalOk" [Con "app" [a], errs])
evalResultMapOk _ = Nothing

evalResultMapFailed :: Term -> Maybe Term
evalResultMapFailed (Con "evalResultMap" [f, (Con "EvalFailed" [errs])]) = Just (Con "EvalFailed" [errs])
evalResultMapFailed _ = Nothing

evalResultBindOk :: Term -> Maybe Term
evalResultBindOk (Con "evalResultBind" [(Con "EvalOk" [a, errs]), f]) = Just (Con "match" [Con "app" [a], Con "EvalOk" [Var "b", Var "errs2"], Con "EvalOk" [Var "b", Con "append" [errs, Var "errs2"]], Con "EvalFailed" [Var "errs2"], Con "EvalFailed" [Con "append" [errs, Var "errs2"]]])
evalResultBindOk _ = Nothing

evalResultBindFailed :: Term -> Maybe Term
evalResultBindFailed (Con "evalResultBind" [(Con "EvalFailed" [errs]), f]) = Just (Con "EvalFailed" [errs])
evalResultBindFailed _ = Nothing

evalResultAddError :: Term -> Maybe Term
evalResultAddError (Con "evalResultAddError" [e, (Con "EvalOk" [a, errs])]) = Just (Con "EvalOk" [a, Con "Cons" [e, errs]])
evalResultAddError _ = Nothing

evalResultAddErrorFailed :: Term -> Maybe Term
evalResultAddErrorFailed (Con "evalResultAddError" [e, (Con "EvalFailed" [errs])]) = Just (Con "EvalFailed" [Con "Cons" [e, errs]])
evalResultAddErrorFailed _ = Nothing

evalResultIsOk :: Term -> Maybe Term
evalResultIsOk (Con "evalResultIsOk" [(Con "EvalOk" [a, errs])]) = Just (Con "True" [])
evalResultIsOk _ = Nothing

evalResultIsOkFailed :: Term -> Maybe Term
evalResultIsOkFailed (Con "evalResultIsOk" [(Con "EvalFailed" [errs])]) = Just (Con "False" [])
evalResultIsOkFailed _ = Nothing

evalResultGetErrors :: Term -> Maybe Term
evalResultGetErrors (Con "evalResultGetErrors" [(Con "EvalOk" [a, errs])]) = Just (errs)
evalResultGetErrors _ = Nothing

evalResultGetErrorsFailed :: Term -> Maybe Term
evalResultGetErrorsFailed (Con "evalResultGetErrors" [(Con "EvalFailed" [errs])]) = Just (errs)
evalResultGetErrorsFailed _ = Nothing

contextExtend :: Term -> Maybe Term
contextExtend (Con "contextExtend" [ctx, name, ty, loc]) = Just (Con "ContextCons" [Con "MkBinding" [name, ty, Con "None" [], loc], ctx])
contextExtend _ = Nothing

contextExtendLet :: Term -> Maybe Term
contextExtendLet (Con "contextExtendLet" [ctx, name, ty, val, loc]) = Just (Con "ContextCons" [Con "MkBinding" [name, ty, Con "Some" [val], loc], ctx])
contextExtendLet _ = Nothing

contextLookupEmpty :: Term -> Maybe Term
contextLookupEmpty (Con "contextLookup" [(Con "EmptyContext" []), name]) = Just (Con "None" [])
contextLookupEmpty _ = Nothing

contextLookupFound :: Term -> Maybe Term
contextLookupFound (Con "contextLookup" [(Con "ContextCons" [(Con "MkBinding" [name, ty, val, loc]), rest]), name0]) | name0 == name = Just (Con "Some" [Con "MkBinding" [name, ty, val, loc]])
contextLookupFound _ = Nothing

contextLookupMiss :: Term -> Maybe Term
contextLookupMiss (Con "contextLookup" [(Con "ContextCons" [(Con "MkBinding" [n1, ty, val, loc]), rest]), n2]) = Just (Con "contextLookup" [rest, n2])
contextLookupMiss _ = Nothing

contextLookupType :: Term -> Maybe Term
contextLookupType (Con "contextLookupType" [ctx, name]) = Just (Con "match" [Con "contextLookup" [ctx, name], Con "Some" [Con "MkBinding" [Var "n", Var "ty", Var "v", Var "l"]], Con "Some" [Var "ty"], Con "None" [], Con "None" []])
contextLookupType _ = Nothing

contextNames :: Term -> Maybe Term
contextNames (Con "contextNames" [(Con "EmptyContext" [])]) = Just (Con "Nil" [])
contextNames _ = Nothing

contextNamesCons :: Term -> Maybe Term
contextNamesCons (Con "contextNames" [(Con "ContextCons" [(Con "MkBinding" [name, ty, val, loc]), rest])]) = Just (Con "Cons" [name, Con "contextNames" [rest]])
contextNamesCons _ = Nothing

varContextExtend :: Term -> Maybe Term
varContextExtend (Con "varContextExtend" [ctx, name]) = Just (Con "VarContextCons" [name, ctx])
varContextExtend _ = Nothing

varContextContainsEmpty :: Term -> Maybe Term
varContextContainsEmpty (Con "varContextContains" [(Con "EmptyVarContext" []), name]) = Just (Con "False" [])
varContextContainsEmpty _ = Nothing

varContextContainsFound :: Term -> Maybe Term
varContextContainsFound (Con "varContextContains" [(Con "VarContextCons" [name, rest]), name0]) | name0 == name = Just (Con "True" [])
varContextContainsFound _ = Nothing

varContextContainsMiss :: Term -> Maybe Term
varContextContainsMiss (Con "varContextContains" [(Con "VarContextCons" [n1, rest]), n2]) = Just (Con "varContextContains" [rest, n2])
varContextContainsMiss _ = Nothing

evalEnvEmpty :: Term -> Maybe Term
evalEnvEmpty (Con "evalEnvEmpty" []) = Just (Con "MkEvalEnv" [Con "EmptyAttrEnv" [], Con "EmptyContext" [], Con "EmptyVarContext" [], Con "Nil" [], Con "UnknownLoc" []])
evalEnvEmpty _ = Nothing

evalEnvWithCtx :: Term -> Maybe Term
evalEnvWithCtx (Con "evalEnvWithCtx" [(Con "MkEvalEnv" [attrs, oldCtx, vars, errs, loc]), ctx]) = Just (Con "MkEvalEnv" [attrs, ctx, vars, errs, loc])
evalEnvWithCtx _ = Nothing

evalEnvWithLoc :: Term -> Maybe Term
evalEnvWithLoc (Con "evalEnvWithLoc" [(Con "MkEvalEnv" [attrs, ctx, vars, errs, oldLoc]), loc]) = Just (Con "MkEvalEnv" [attrs, ctx, vars, errs, loc])
evalEnvWithLoc _ = Nothing

evalEnvAddBinding :: Term -> Maybe Term
evalEnvAddBinding (Con "evalEnvAddBinding" [(Con "MkEvalEnv" [attrs, ctx, vars, errs, loc]), name, ty]) = Just (Con "MkEvalEnv" [attrs, Con "contextExtend" [ctx, name, ty, loc], vars, errs, loc])
evalEnvAddBinding _ = Nothing

evalEnvAddVar :: Term -> Maybe Term
evalEnvAddVar (Con "evalEnvAddVar" [(Con "MkEvalEnv" [attrs, ctx, vars, errs, loc]), name]) = Just (Con "MkEvalEnv" [attrs, ctx, Con "varContextExtend" [vars, name], errs, loc])
evalEnvAddVar _ = Nothing

evalEnvAddError :: Term -> Maybe Term
evalEnvAddError (Con "evalEnvAddError" [(Con "MkEvalEnv" [attrs, ctx, vars, errs, loc]), e]) = Just (Con "MkEvalEnv" [attrs, ctx, vars, Con "Cons" [e, errs], loc])
evalEnvAddError _ = Nothing

evalEnvAddTypeError :: Term -> Maybe Term
evalEnvAddTypeError (Con "evalEnvAddTypeError" [(Con "MkEvalEnv" [attrs, ctx, vars, errs, loc]), msg]) = Just (Con "MkEvalEnv" [attrs, ctx, vars, Con "Cons" [Con "typeErrorSimple" [msg, loc], errs], loc])
evalEnvAddTypeError _ = Nothing

evalEnvAddMismatch :: Term -> Maybe Term
evalEnvAddMismatch (Con "evalEnvAddMismatch" [(Con "MkEvalEnv" [attrs, ctx, vars, errs, loc]), expected, actual]) = Just (Con "MkEvalEnv" [attrs, ctx, vars, Con "Cons" [Con "typeErrorMismatch" [expected, actual, loc], errs], loc])
evalEnvAddMismatch _ = Nothing

evalEnvSetAttr :: Term -> Maybe Term
evalEnvSetAttr (Con "evalEnvSetAttr" [(Con "MkEvalEnv" [attrs, ctx, vars, errs, loc]), path, name, val]) = Just (Con "MkEvalEnv" [Con "attrEnvInsert" [attrs, path, name, val], ctx, vars, errs, loc])
evalEnvSetAttr _ = Nothing

evalEnvGetAttr :: Term -> Maybe Term
evalEnvGetAttr (Con "evalEnvGetAttr" [(Con "MkEvalEnv" [attrs, ctx, vars, errs, loc]), path, name]) = Just (Con "attrEnvLookup" [attrs, path, name])
evalEnvGetAttr _ = Nothing

evalEnvHasErrors :: Term -> Maybe Term
evalEnvHasErrors (Con "evalEnvHasErrors" [(Con "MkEvalEnv" [attrs, ctx, vars, errs, loc])]) = Just (Con "not" [Con "null" [errs]])
evalEnvHasErrors _ = Nothing

freeVarsVar :: Term -> Maybe Term
freeVarsVar (Con "freeVars" [(Con "Var" [n])]) = Just (Con "Cons" [n, Con "Nil" []])
freeVarsVar _ = Nothing

freeVarsLit :: Term -> Maybe Term
freeVarsLit (Con "freeVars" [(Con "Lit" [s])]) = Just (Con "Nil" [])
freeVarsLit _ = Nothing

freeVarsLam :: Term -> Maybe Term
freeVarsLam (Con "freeVars" [(Con "Con" [(Lit "\"lam\""), (Con "Cons" [(Con "Var" [x]), (Con "Cons" [ty, (Con "Cons" [body, (Con "Nil" [])])])])])]) = Just (Con "append" [Con "freeVars" [ty], Con "filter" [Con "binder" [Lit "v", Con "not" [Con "eq" [Var "v", x]]], Con "freeVars" [body]]])
freeVarsLam _ = Nothing

freeVarsPi :: Term -> Maybe Term
freeVarsPi (Con "freeVars" [(Con "Con" [(Lit "\"Pi\""), (Con "Cons" [(Con "Var" [x]), (Con "Cons" [dom, (Con "Cons" [cod, (Con "Nil" [])])])])])]) = Just (Con "append" [Con "freeVars" [dom], Con "filter" [Con "binder" [Lit "v", Con "not" [Con "eq" [Var "v", x]]], Con "freeVars" [cod]]])
freeVarsPi _ = Nothing

freeVarsCon :: Term -> Maybe Term
freeVarsCon (Con "freeVars" [(Con "Con" [c, args])]) = Just (Con "flatMap" [Con "freeVars" [], args])
freeVarsCon _ = Nothing

freshName :: Term -> Maybe Term
freshName (Con "freshName" [base, avoid]) = Just (Con "freshNameHelper" [base, avoid, Lit "0"])
freshName _ = Nothing

freshNameHelper :: Term -> Maybe Term
freshNameHelper (Con "freshNameHelper" [base, avoid, i]) = Just (Con "let" [Var "candidate", Con "if" [Con "eq" [i, Lit "0"], base, Con "concat" [base, Con "toString" [i]]], Con "if" [Con "contains" [avoid, Var "candidate"], Con "freshNameHelper" [base, avoid, Con "add" [i, Lit "1"]], Var "candidate"]])
freshNameHelper _ = Nothing

substAvoidVar :: Term -> Maybe Term
substAvoidVar (Con "substAvoid" [name, repl, fv, (Con "Var" [n])]) = Just (Con "if" [Con "eq" [n, name], repl, Con "Var" [n]])
substAvoidVar _ = Nothing

substAvoidLit :: Term -> Maybe Term
substAvoidLit (Con "substAvoid" [name, repl, fv, (Con "Lit" [s])]) = Just (Con "Lit" [s])
substAvoidLit _ = Nothing

substAvoidLam :: Term -> Maybe Term
substAvoidLam (Con "substAvoid" [name, repl, fv, (Con "Con" [(Lit "\"lam\""), (Con "Cons" [(Con "Var" [x]), (Con "Cons" [ty, (Con "Cons" [body, (Con "Nil" [])])])])])]) = Just (Con "if" [Con "eq" [x, name], Con "Con" [Lit "\"lam\"", Con "Cons" [Con "Var" [x], Con "Cons" [Con "substAvoid" [name, repl, fv, ty], Con "Cons" [body, Con "Nil" []]]]], Con "if" [Con "contains" [fv, x], Con "let" [Var "x2", Con "freshName" [x, fv], Con "let" [Var "body2", Con "subst" [x, Con "Var" [Var "x2"], body], Con "Con" [Lit "\"lam\"", Con "Cons" [Con "Var" [Var "x2"], Con "Cons" [Con "substAvoid" [name, repl, fv, ty], Con "Cons" [Con "substAvoid" [name, repl, Con "Cons" [Var "x2", fv], Var "body2"], Con "Nil" []]]]]]], Con "Con" [Lit "\"lam\"", Con "Cons" [Con "Var" [x], Con "Cons" [Con "substAvoid" [name, repl, fv, ty], Con "Cons" [Con "substAvoid" [name, repl, fv, body], Con "Nil" []]]]]]])
substAvoidLam _ = Nothing

substAvoidPi :: Term -> Maybe Term
substAvoidPi (Con "substAvoid" [name, repl, fv, (Con "Con" [(Lit "\"Pi\""), (Con "Cons" [(Con "Var" [x]), (Con "Cons" [dom, (Con "Cons" [cod, (Con "Nil" [])])])])])]) = Just (Con "if" [Con "eq" [x, name], Con "Con" [Lit "\"Pi\"", Con "Cons" [Con "Var" [x], Con "Cons" [Con "substAvoid" [name, repl, fv, dom], Con "Cons" [cod, Con "Nil" []]]]], Con "if" [Con "contains" [fv, x], Con "let" [Var "x2", Con "freshName" [x, fv], Con "let" [Var "cod2", Con "subst" [x, Con "Var" [Var "x2"], cod], Con "Con" [Lit "\"Pi\"", Con "Cons" [Con "Var" [Var "x2"], Con "Cons" [Con "substAvoid" [name, repl, fv, dom], Con "Cons" [Con "substAvoid" [name, repl, Con "Cons" [Var "x2", fv], Var "cod2"], Con "Nil" []]]]]]], Con "Con" [Lit "\"Pi\"", Con "Cons" [Con "Var" [x], Con "Cons" [Con "substAvoid" [name, repl, fv, dom], Con "Cons" [Con "substAvoid" [name, repl, fv, cod], Con "Nil" []]]]]]])
substAvoidPi _ = Nothing

substAvoidCon :: Term -> Maybe Term
substAvoidCon (Con "substAvoid" [name, repl, fv, (Con "Con" [c, args])]) = Just (Con "Con" [c, Con "map" [Con "binder" [Lit "a", Con "substAvoid" [name, repl, fv, Var "a"]], args]])
substAvoidCon _ = Nothing

attrRefSelf :: Term -> Maybe Term
attrRefSelf (Con "attrRefSelf" [name]) = Just (Con "MkAttrRef" [Con "Empty" [], name])
attrRefSelf _ = Nothing

attrRefChild :: Term -> Maybe Term
attrRefChild (Con "attrRefChild" [child, name]) = Just (Con "MkAttrRef" [Con "PathCon" [child, Con "Empty" []], name])
attrRefChild _ = Nothing

emptyAttrDef :: Term -> Maybe Term
emptyAttrDef (Con "emptyAttrDef" [name, flow]) = Just (Con "MkAttrDef" [name, flow, Con "None" [], Con "Nil" []])
emptyAttrDef _ = Nothing

addAttrRule :: Term -> Maybe Term
addAttrRule (Con "addAttrRule" [(Con "MkAttrDef" [name, flow, ty, rules]), rule]) = Just (Con "MkAttrDef" [name, flow, ty, Con "append" [rules, Con "Cons" [rule, Con "Nil" []]]])
addAttrRule _ = Nothing

attrEnvLookupEmpty :: Term -> Maybe Term
attrEnvLookupEmpty (Con "attrEnvLookup" [(Con "Empty" []), path, name]) = Just (Con "None" [])
attrEnvLookupEmpty _ = Nothing

attrEnvLookupFound :: Term -> Maybe Term
attrEnvLookupFound (Con "attrEnvLookup" [(Con "AttrEnvCons" [path, name, val, rest]), path0, name1]) | name1 == name, path0 == path = Just (Con "Some" [val])
attrEnvLookupFound _ = Nothing

attrEnvLookupMiss :: Term -> Maybe Term
attrEnvLookupMiss (Con "attrEnvLookup" [(Con "AttrEnvCons" [p1, n1, val, rest]), p2, n2]) = Just (Con "attrEnvLookup" [rest, p2, n2])
attrEnvLookupMiss _ = Nothing

attrEnvInsert :: Term -> Maybe Term
attrEnvInsert (Con "attrEnvInsert" [env, path, name, val]) = Just (Con "AttrEnvCons" [path, name, val, env])
attrEnvInsert _ = Nothing

attrEnvGetLocal :: Term -> Maybe Term
attrEnvGetLocal (Con "attrEnvGetLocal" [env, name]) = Just (Con "attrEnvLookup" [env, Con "Empty" [], name])
attrEnvGetLocal _ = Nothing

attrEnvGetChild :: Term -> Maybe Term
attrEnvGetChild (Con "attrEnvGetChild" [env, child, name]) = Just (Con "attrEnvLookup" [env, Con "PathCon" [child, Con "Empty" []], name])
attrEnvGetChild _ = Nothing

attrEnvMergeEmpty :: Term -> Maybe Term
attrEnvMergeEmpty (Con "attrEnvMerge" [env1, (Con "EmptyAttrEnv" [])]) = Just (env1)
attrEnvMergeEmpty _ = Nothing

attrEnvMergeCons :: Term -> Maybe Term
attrEnvMergeCons (Con "attrEnvMerge" [env1, (Con "AttrEnvCons" [path, name, val, rest])]) = Just (Con "attrEnvMerge" [Con "AttrEnvCons" [path, name, val, env1], rest])
attrEnvMergeCons _ = Nothing

evalAttrExprVar :: Term -> Maybe Term
evalAttrExprVar (Con "evalAttrExpr" [(Con "Var" [name]), env]) = Just (Con "if" [Con "startsWith" [name, Lit "\"$\""], Con "match" [Con "attrEnvLookup" [env, Con "Empty" [], Con "drop" [Lit "1", name]], Con "Some" [Var "v"], Var "v", Con "None" [], Con "Con" [Lit "\"error\"", Con "Cons" [Con "Lit" [Con "concat" [Lit "\"undefined: \"", name]], Con "Nil" []]]], Con "Var" [name]])
evalAttrExprVar _ = Nothing

evalAttrExprCon :: Term -> Maybe Term
evalAttrExprCon (Con "evalAttrExpr" [(Con "Con" [c, args]), env]) = Just (Con "Con" [c, Con "map" [Con "binder" [Lit "x", Con "evalAttrExpr" [Var "x", env]], args]])
evalAttrExprCon _ = Nothing

evalAttrExprLit :: Term -> Maybe Term
evalAttrExprLit (Con "evalAttrExpr" [(Con "Lit" [s]), env]) = Just (Con "Lit" [s])
evalAttrExprLit _ = Nothing

findRuleEmpty :: Term -> Maybe Term
findRuleEmpty (Con "findRule" [prod, target, (Con "Nil" [])]) = Just (Con "None" [])
findRuleEmpty _ = Nothing

findRuleFound :: Term -> Maybe Term
findRuleFound (Con "findRule" [prod, target, (Con "Cons" [(Con "MkAttrRule" [prod0, target1, expr]), rest])]) | target1 == target, prod0 == prod = Just (Con "Some" [Con "MkAttrRule" [prod, target, expr]])
findRuleFound _ = Nothing

findRuleMiss :: Term -> Maybe Term
findRuleMiss (Con "findRule" [prod, target, (Con "Cons" [(Con "MkAttrRule" [p2, t2, e]), rest])]) = Just (Con "findRule" [prod, target, rest])
findRuleMiss _ = Nothing

evalSynVar :: Term -> Maybe Term
evalSynVar (Con "evalSyn" [def, (Con "Var" [x])]) = Just (Con "EmptyAttrEnv" [])
evalSynVar _ = Nothing

evalSynLit :: Term -> Maybe Term
evalSynLit (Con "evalSyn" [def, (Con "Lit" [s])]) = Just (Con "EmptyAttrEnv" [])
evalSynLit _ = Nothing

evalSynCon :: Term -> Maybe Term
evalSynCon (Con "evalSyn" [(Con "MkAttrDef" [attrName, flow, ty, rules]), (Con "Con" [prod, children])]) = Just (Con "evalSynConHelper" [attrName, flow, ty, rules, prod, children, Lit "0"])
evalSynCon _ = Nothing

evalSynConHelper :: Term -> Maybe Term
evalSynConHelper (Con "evalSynConHelper" [attrName, flow, ty, rules, prod, children, idx]) = Just (Con "let" [Var "childEnvs", Con "mapWithIndex" [Con "i" [Con "binder" [Lit "child", Con "prefixEnv" [Con "concat" [Lit "\"child\"", Con "toString" [Var "i"]], Con "evalSyn" [Con "MkAttrDef" [attrName, flow, ty, rules], Var "child"]]]], children], Con "let" [Var "env", Con "foldl" [Con "attrEnvMerge" [], Con "EmptyAttrEnv" [], Var "childEnvs"], Con "match" [Con "findRule" [prod, Con "Empty" [], rules], Con "Some" [Con "MkAttrRule" [Var "p", Var "t", Var "expr"]], Con "attrEnvInsert" [Var "env", Con "Empty" [], attrName, Con "evalAttrExpr" [Var "expr", Var "env"]], Con "None" [], Var "env"]]])
evalSynConHelper _ = Nothing

evalInhVar :: Term -> Maybe Term
evalInhVar (Con "evalInh" [def, (Con "Var" [x]), parentEnv]) = Just (parentEnv)
evalInhVar _ = Nothing

evalInhLit :: Term -> Maybe Term
evalInhLit (Con "evalInh" [def, (Con "Lit" [s]), parentEnv]) = Just (parentEnv)
evalInhLit _ = Nothing

evalInhCon :: Term -> Maybe Term
evalInhCon (Con "evalInh" [(Con "MkAttrDef" [attrName, flow, ty, rules]), (Con "Con" [prod, children]), parentEnv]) = Just (Con "evalInhConHelper" [attrName, flow, ty, rules, prod, children, parentEnv, Lit "0"])
evalInhCon _ = Nothing

evalAttrs :: Term -> Maybe Term
evalAttrs (Con "evalAttrs" [defs, term]) = Just (Con "let" [Var "synDefs", Con "filter" [Con "binder" [Lit "d", Con "eq" [Con "attrDefFlow" [Var "d"], Con "Syn" []]], defs], Con "let" [Var "inhDefs", Con "filter" [Con "binder" [Lit "d", Con "eq" [Con "attrDefFlow" [Var "d"], Con "Inh" []]], defs], Con "let" [Var "inhEnv", Con "foldl" [Con "env" [Con "binder" [Lit "def", Con "evalInh" [Var "def", term, Var "env"]]], Con "EmptyAttrEnv" [], Var "inhDefs"], Con "foldl" [Con "env" [Con "binder" [Lit "def", Con "attrEnvMerge" [Var "env", Con "evalSyn" [Var "def", term]]]], Var "inhEnv", Var "synDefs"]]]])
evalAttrs _ = Nothing

cataTermVar :: Term -> Maybe Term
cataTermVar (Con "cataTerm" [alg, (Con "Var" [x])]) = Just (Con "app" [x, Con "Nil" []])
cataTermVar _ = Nothing

cataTermLit :: Term -> Maybe Term
cataTermLit (Con "cataTerm" [alg, (Con "Lit" [s])]) = Just (Con "app" [s, Con "Nil" []])
cataTermLit _ = Nothing

cataTermCon :: Term -> Maybe Term
cataTermCon (Con "cataTerm" [alg, (Con "Con" [c, args])]) = Just (Con "app" [c, Con "map" [Con "binder" [Lit "a", Con "cataTerm" [alg, Var "a"]], args]])
cataTermCon _ = Nothing

paraTermVar :: Term -> Maybe Term
paraTermVar (Con "paraTerm" [coalg, (Con "Var" [x])]) = Just (Con "app" [x, Con "Nil" []])
paraTermVar _ = Nothing

paraTermLit :: Term -> Maybe Term
paraTermLit (Con "paraTerm" [coalg, (Con "Lit" [s])]) = Just (Con "app" [s, Con "Nil" []])
paraTermLit _ = Nothing

paraTermCon :: Term -> Maybe Term
paraTermCon (Con "paraTerm" [coalg, (Con "Con" [c, args])]) = Just (Con "app" [c, Con "map" [Con "binder" [Lit "a", Con "Pair" [Var "a", Con "paraTerm" [coalg, Var "a"]]], args]])
paraTermCon _ = Nothing

attrLangSynAttrs :: Term -> Maybe Term
attrLangSynAttrs (Con "attrLangSynAttrs" [(Con "MkAttrLanguage" [name, pieces, attrs])]) = Just (Con "filter" [Con "binder" [Lit "d", Con "eq" [Con "attrDefFlow" [Var "d"], Con "Syn" []]], attrs])
attrLangSynAttrs _ = Nothing

attrLangInhAttrs :: Term -> Maybe Term
attrLangInhAttrs (Con "attrLangInhAttrs" [(Con "MkAttrLanguage" [name, pieces, attrs])]) = Just (Con "filter" [Con "binder" [Lit "d", Con "eq" [Con "attrDefFlow" [Var "d"], Con "Inh" []]], attrs])
attrLangInhAttrs _ = Nothing

attrLangEval :: Term -> Maybe Term
attrLangEval (Con "attrLangEval" [(Con "MkAttrLanguage" [name, pieces, attrs]), term]) = Just (Con "evalAttrs" [attrs, term])
attrLangEval _ = Nothing

attrLangPushout :: Term -> Maybe Term
attrLangPushout (Con "attrLangPushout" [(Con "MkAttrLanguage" [n1, p1, a1]), (Con "MkAttrLanguage" [n2, p2, a2])]) = Just (Con "MkAttrLanguage" [Con "concat" [Con "concat" [n1, Lit "\"_\""], n2], Con "append" [p1, p2], Con "append" [a1, a2]])
attrLangPushout _ = Nothing

tokEq :: Term -> Maybe Term
tokEq (Con "tokEq" [(Con "TokIdent" [a]), (Con "TokIdent" [b])]) = Just (Con "strEq" [a, b])
tokEq _ = Nothing

tokEqString :: Term -> Maybe Term
tokEqString (Con "tokEq" [(Con "TokString" [a]), (Con "TokString" [b])]) = Just (Con "strEq" [a, b])
tokEqString _ = Nothing

tokEqSym :: Term -> Maybe Term
tokEqSym (Con "tokEq" [(Con "TokSym" [a]), (Con "TokSym" [b])]) = Just (Con "strEq" [a, b])
tokEqSym _ = Nothing

tokEqMismatch :: Term -> Maybe Term
tokEqMismatch (Con "tokEq" [a, b]) = Just (Con "false" [])
tokEqMismatch _ = Nothing

stateTokens :: Term -> Maybe Term
stateTokens (Con "stateTokens" [(Con "MkState" [toks, pos])]) = Just (toks)
stateTokens _ = Nothing

statePos :: Term -> Maybe Term
statePos (Con "statePos" [(Con "MkState" [toks, pos])]) = Just (pos)
statePos _ = Nothing

stateAdvance :: Term -> Maybe Term
stateAdvance (Con "stateAdvance" [(Con "MkState" [(Con "Cons" [v_t, ts]), pos])]) = Just (Con "MkState" [ts, Con "add" [pos, Lit "1"]])
stateAdvance _ = Nothing

parseLit :: Term -> Maybe Term
parseLit (Con "parseLit" [s, (Con "MkState" [(Con "Cons" [(Con "TokSym" [s0]), rest]), pos])]) | s0 == s = Just (Con "ParseOk" [Con "Lit" [s], Con "MkState" [rest, Con "add" [pos, Lit "1"]]])
parseLit _ = Nothing

parseLitFail :: Term -> Maybe Term
parseLitFail (Con "parseLit" [s, (Con "MkState" [(Con "Cons" [v_t, rest]), pos])]) = Just (Con "ParseFail" [Con "concat" [Lit "\"expected \"", s], Con "MkState" [Con "Cons" [v_t, rest], pos]])
parseLitFail _ = Nothing

parseIdent :: Term -> Maybe Term
parseIdent (Con "parseIdent" [(Con "MkState" [(Con "Cons" [(Con "TokIdent" [name]), rest]), pos])]) = Just (Con "ParseOk" [Con "Var" [name], Con "MkState" [rest, Con "add" [pos, Lit "1"]]])
parseIdent _ = Nothing

parseIdentFail :: Term -> Maybe Term
parseIdentFail (Con "parseIdent" [(Con "MkState" [(Con "Cons" [v_t, rest]), pos])]) = Just (Con "ParseFail" [Lit "\"expected identifier\"", Con "MkState" [Con "Cons" [v_t, rest], pos]])
parseIdentFail _ = Nothing

parseSeq :: Term -> Maybe Term
parseSeq (Con "parseSeq" [p1, p2, state]) = Just (Con "case" [Con "parse" [p1, state], Con "ParseOk" [Var "t1", Var "s1"], Con "case" [Con "parse" [p2, Var "s1"], Con "ParseOk" [Var "t2", Var "s2"], Con "ParseOk" [Con "Con" [Lit "\"seq\"", Con "Cons" [Var "t1", Con "Cons" [Var "t2", Con "Nil" []]]], Var "s2"], Con "ParseFail" [Var "msg", Var "s"], Con "ParseFail" [Var "msg", Var "s"]], Con "ParseFail" [Var "msg", Var "s"], Con "ParseFail" [Var "msg", Var "s"]])
parseSeq _ = Nothing

parseAlt :: Term -> Maybe Term
parseAlt (Con "parseAlt" [p1, p2, state]) = Just (Con "case" [Con "parse" [p1, state], Con "ParseOk" [Var "t", Var "s"], Con "ParseOk" [Var "t", Var "s"], Con "ParseFail" [Var "msg1", Var "s1"], Con "case" [Con "parse" [p2, state], Con "ParseOk" [Var "t", Var "s"], Con "ParseOk" [Var "t", Var "s"], Con "ParseFail" [Var "msg2", Var "s2"], Con "ParseFail" [Con "concat" [Var "msg1", Con "concat" [Lit "\" or \"", Var "msg2"]], state]]])
parseAlt _ = Nothing

parseStar :: Term -> Maybe Term
parseStar (Con "parseStar" [p, state]) = Just (Con "case" [Con "parse" [p, state], Con "ParseOk" [Var "t", Var "s"], Con "case" [Con "parseStar" [p, Var "s"], Con "ParseOk" [Con "Con" [Lit "\"list\"", Var "ts"], Var "s2"], Con "ParseOk" [Con "Con" [Lit "\"list\"", Con "Cons" [Var "t", Var "ts"]], Var "s2"], Con "ParseFail" [Var "msg", Var "s2"], Con "ParseOk" [Con "Con" [Lit "\"list\"", Con "Cons" [Var "t", Con "Nil" []]], Var "s"]], Con "ParseFail" [Var "msg", Var "s"], Con "ParseOk" [Con "Con" [Lit "\"list\"", Con "Nil" []], state]])
parseStar _ = Nothing

parseOpt :: Term -> Maybe Term
parseOpt (Con "parseOpt" [p, state]) = Just (Con "case" [Con "parse" [p, state], Con "ParseOk" [Var "t", Var "s"], Con "ParseOk" [Con "Con" [Lit "\"some\"", Con "Cons" [Var "t", Con "Nil" []]], Var "s"], Con "ParseFail" [Var "msg", Var "s"], Con "ParseOk" [Con "Con" [Lit "\"none\"", Con "Nil" []], state]])
parseOpt _ = Nothing

parseCon :: Term -> Maybe Term
parseCon (Con "parseCon" [name, p, state]) = Just (Con "case" [Con "parse" [p, state], Con "ParseOk" [Var "t", Var "s"], Con "ParseOk" [Con "Con" [name, Con "Cons" [Var "t", Con "Nil" []]], Var "s"], Con "ParseFail" [Var "msg", Var "s"], Con "ParseFail" [Var "msg", Var "s"]])
parseCon _ = Nothing

parseGEmpty :: Term -> Maybe Term
parseGEmpty (Con "parse" [(Con "GEmpty" []), state]) = Just (Con "ParseOk" [Con "Con" [Lit "\"unit\"", Con "Nil" []], state])
parseGEmpty _ = Nothing

parseGLit :: Term -> Maybe Term
parseGLit (Con "parse" [(Con "GLit" [s]), state]) = Just (Con "parseLit" [s, state])
parseGLit _ = Nothing

parseGRef :: Term -> Maybe Term
parseGRef (Con "parse" [(Con "GRef" [(Lit "\"ident\"")]), state]) = Just (Con "parseIdent" [state])
parseGRef _ = Nothing

parseGSeq :: Term -> Maybe Term
parseGSeq (Con "parse" [(Con "GSeq" [g1, g2]), state]) = Just (Con "parseSeq" [g1, g2, state])
parseGSeq _ = Nothing

parseGAlt :: Term -> Maybe Term
parseGAlt (Con "parse" [(Con "GAlt" [g1, g2]), state]) = Just (Con "parseAlt" [g1, g2, state])
parseGAlt _ = Nothing

parseGStar :: Term -> Maybe Term
parseGStar (Con "parse" [(Con "GStar" [g]), state]) = Just (Con "parseStar" [g, state])
parseGStar _ = Nothing

parseGOpt :: Term -> Maybe Term
parseGOpt (Con "parse" [(Con "GOpt" [g]), state]) = Just (Con "parseOpt" [g, state])
parseGOpt _ = Nothing

parseGCon :: Term -> Maybe Term
parseGCon (Con "parse" [(Con "GCon" [name, g]), state]) = Just (Con "parseCon" [name, g, state])
parseGCon _ = Nothing

printLit :: Term -> Maybe Term
printLit (Con "print" [(Con "GLit" [s]), (Con "Lit" [s0])]) | s0 == s = Just (Con "PrintOk" [Con "Cons" [Con "TokSym" [s], Con "Nil" []]])
printLit _ = Nothing

printIdent :: Term -> Maybe Term
printIdent (Con "print" [(Con "GRef" [(Lit "\"ident\"")]), (Con "Var" [name])]) = Just (Con "PrintOk" [Con "Cons" [Con "TokIdent" [name], Con "Nil" []]])
printIdent _ = Nothing

printSeq :: Term -> Maybe Term
printSeq (Con "print" [(Con "GSeq" [g1, g2]), (Con "Con" [(Lit "\"seq\""), (Con "Cons" [t1, (Con "Cons" [t2, (Con "Nil" [])])])])]) = Just (Con "case" [Con "print" [g1, t1], Con "PrintOk" [Var "toks1"], Con "case" [Con "print" [g2, t2], Con "PrintOk" [Var "toks2"], Con "PrintOk" [Con "append" [Var "toks1", Var "toks2"]], Con "PrintFail" [Var "msg"], Con "PrintFail" [Var "msg"]], Con "PrintFail" [Var "msg"], Con "PrintFail" [Var "msg"]])
printSeq _ = Nothing

printCon :: Term -> Maybe Term
printCon (Con "print" [(Con "GCon" [name, g]), (Con "Con" [name0, (Con "Cons" [v_t, (Con "Nil" [])])])]) | name0 == name = Just (Con "print" [g, v_t])
printCon _ = Nothing

grammarIso :: Term -> Maybe Term
grammarIso (Con "grammarIso" [g]) = Just (Con "MkIso" [Con "Lam" [Con "binder" [Lit "input", Con "case" [Con "parse" [g, Con "tokenize" [Con "input" []]], Con "ParseOk" [Var "t", Var "s"], Con "Some" [Var "t"], Con "ParseFail" [Var "msg", Var "s"], Con "None" []]]], Con "Lam" [Con "binder" [Lit "term", Con "case" [Con "print" [g, Var "term"], Con "PrintOk" [Var "toks"], Con "Some" [Con "detokenize" [Var "toks"]], Con "PrintFail" [Var "msg"], Con "None" []]]]])
grammarIso _ = Nothing

matchVarMeta :: Term -> Maybe Term
matchVarMeta (Con "match" [(Con "Var" [name]), v_t]) = Just (Con "Some" [Con "Bind" [name, v_t, Con "Empty" []]])
matchVarMeta _ = Nothing

matchListNil :: Term -> Maybe Term
matchListNil (Con "matchList" [(Con "Nil" []), (Con "Nil" [])]) = Just (Con "Some" [Con "Empty" []])
matchListNil _ = Nothing

matchListCons :: Term -> Maybe Term
matchListCons (Con "matchList" [(Con "Cons" [p, ps]), (Con "Cons" [v_t, ts])]) = Just (Con "merge" [Con "match" [p, v_t], Con "matchList" [ps, ts]])
matchListCons _ = Nothing

mergeEnvs :: Term -> Maybe Term
mergeEnvs (Con "merge" [(Con "Some" [e1]), (Con "Some" [e2])]) = Just (Con "Some" [Con "append" [e1, e2]])
mergeEnvs _ = Nothing

substVarHit :: Term -> Maybe Term
substVarHit (Con "subst" [(Con "Var" [name]), (Con "Bind" [name0, val, rest])]) | name0 == name = Just (val)
substVarHit _ = Nothing

substVarMiss :: Term -> Maybe Term
substVarMiss (Con "subst" [(Con "Var" [name]), (Con "Bind" [other, val, rest])]) = Just (Con "subst" [Con "Var" [name], rest])
substVarMiss _ = Nothing

substVarEmpty :: Term -> Maybe Term
substVarEmpty (Con "subst" [(Con "Var" [name]), (Con "Empty" [])]) = Just (Con "Var" [name])
substVarEmpty _ = Nothing

applyRule :: Term -> Maybe Term
applyRule (Con "apply" [(Con "MkRule" [name, pat, tmpl]), v_t]) = Just (Con "case" [Con "match" [pat, v_t], Con "Some" [Var "env"], Con "subst" [tmpl, Var "env"], Con "None" [], Con "None" []])
applyRule _ = Nothing

tryRulesFirst :: Term -> Maybe Term
tryRulesFirst (Con "tryRules" [(Con "Cons" [r, rs]), v_t]) = Just (Con "case" [Con "apply" [r, v_t], Con "Some" [Var "result"], Con "Some" [Var "result"], Con "None" [], Con "tryRules" [rs, v_t]])
tryRulesFirst _ = Nothing

tryRulesEmpty :: Term -> Maybe Term
tryRulesEmpty (Con "tryRules" [(Con "Nil" []), v_t]) = Just (Con "None" [])
tryRulesEmpty _ = Nothing

normalizeStep :: Term -> Maybe Term
normalizeStep (Con "normalize" [rules, v_t]) = Just (Con "let" [Var "t'", Con "normalizeOnce" [rules, v_t], Con "if" [Con "eq" [v_t, Var "t'"], v_t, Con "normalize" [rules, Var "t'"]]])
normalizeStep _ = Nothing

normalizeOnceTop :: Term -> Maybe Term
normalizeOnceTop (Con "normalizeOnce" [rules, v_t]) = Just (Con "case" [Con "tryRules" [rules, v_t], Con "Some" [Var "result"], Var "result", Con "None" [], Con "normalizeChildren" [rules, v_t]])
normalizeOnceTop _ = Nothing

normalizeChildrenVar :: Term -> Maybe Term
normalizeChildrenVar (Con "normalizeChildren" [rules, (Con "Var" [x])]) = Just (Con "Var" [x])
normalizeChildrenVar _ = Nothing

normalizeChildrenLit :: Term -> Maybe Term
normalizeChildrenLit (Con "normalizeChildren" [rules, (Con "Lit" [s])]) = Just (Con "Lit" [s])
normalizeChildrenLit _ = Nothing

normalizeChildrenCon :: Term -> Maybe Term
normalizeChildrenCon (Con "normalizeChildren" [rules, (Con "Con" [name, args])]) = Just (Con "Con" [name, Con "map" [Con "normalizeOnce" [rules], args]])
normalizeChildrenCon _ = Nothing

rosettaTranslate :: Term -> Maybe Term
rosettaTranslate (Con "translate" [(Con "MkLang" [n1, g1, iso1]), (Con "MkLang" [n2, g2, iso2]), src]) = Just (Con "forward" [iso2, Con "backward" [iso1, src]])
rosettaTranslate _ = Nothing

roundTrip :: Term -> Maybe Term
roundTrip (Con "roundtrip" [(Con "MkLang" [n, g, (Con "MkIso" [parse, print])]), src]) = Just (Con "bind" [Con "App" [parse, src], Var "ast", Con "App" [print, Var "ast"]])
roundTrip _ = Nothing

mapNil :: Term -> Maybe Term
mapNil (Con "map" [f, (Con "Nil" [])]) = Just (Con "Nil" [])
mapNil _ = Nothing

mapCons :: Term -> Maybe Term
mapCons (Con "map" [f, (Con "Cons" [x, xs])]) = Just (Con "Cons" [Con "App" [f, x], Con "map" [f, xs]])
mapCons _ = Nothing

foldNil :: Term -> Maybe Term
foldNil (Con "fold" [f, acc, (Con "Nil" [])]) = Just (acc)
foldNil _ = Nothing

foldCons :: Term -> Maybe Term
foldCons (Con "fold" [f, acc, (Con "Cons" [x, xs])]) = Just (Con "fold" [f, Con "App" [f, acc, x], xs])
foldCons _ = Nothing

appendNil :: Term -> Maybe Term
appendNil (Con "append" [(Con "Nil" []), ys]) = Just (ys)
appendNil _ = Nothing

appendCons :: Term -> Maybe Term
appendCons (Con "append" [(Con "Cons" [x, xs]), ys]) = Just (Con "Cons" [x, Con "append" [xs, ys]])
appendCons _ = Nothing

ifTrue :: Term -> Maybe Term
ifTrue (Con "if" [(Con "true" []), v_then, v_else]) = Just (v_then)
ifTrue _ = Nothing

ifFalse :: Term -> Maybe Term
ifFalse (Con "if" [(Con "false" []), v_then, v_else]) = Just (v_else)
ifFalse _ = Nothing

eqSame :: Term -> Maybe Term
eqSame (Con "eq" [x, x0]) | x0 == x = Just (Con "true" [])
eqSame _ = Nothing

bindSome :: Term -> Maybe Term
bindSome (Con "bind" [(Con "Some" [x]), var, body]) = Just (Con "subst" [body, Con "Bind" [var, x, Con "Empty" []]])
bindSome _ = Nothing

bindNone :: Term -> Maybe Term
bindNone (Con "bind" [(Con "None" []), var, body]) = Just (Con "None" [])
bindNone _ = Nothing

prodName :: Term -> Maybe Term
prodName (Con "prodName" [(Con "MkProd" [name, expr, con])]) = Just (name)
prodName _ = Nothing

prodGrammar :: Term -> Maybe Term
prodGrammar (Con "prodGrammar" [(Con "MkProd" [name, expr, con])]) = Just (expr)
prodGrammar _ = Nothing

prodCon :: Term -> Maybe Term
prodCon (Con "prodCon" [(Con "MkProd" [name, expr, con])]) = Just (con)
prodCon _ = Nothing

astToGrammarLit :: Term -> Maybe Term
astToGrammarLit (Con "astToGrammar" [(Con "Con" [(Lit "\"lit\""), (Con "Cons" [(Con "Con" [(Lit "\"string\""), (Con "Cons" [(Con "Lit" [s]), (Con "Nil" [])])]), (Con "Nil" [])])])]) = Just (Con "GLit" [Con "stripQuotes" [s]])
astToGrammarLit _ = Nothing

astToGrammarRef :: Term -> Maybe Term
astToGrammarRef (Con "astToGrammar" [(Con "Con" [(Lit "\"ref\""), (Con "Cons" [(Con "Con" [(Lit "\"ident\""), (Con "Cons" [(Con "Var" [name]), (Con "Nil" [])])]), (Con "Nil" [])])])]) = Just (Con "GRef" [name])
astToGrammarRef _ = Nothing

astToGrammarSpecial :: Term -> Maybe Term
astToGrammarSpecial (Con "astToGrammar" [(Con "Con" [(Lit "\"special\""), (Con "Cons" [(Con "Var" [s]), (Con "Nil" [])])])]) = Just (Con "GRef" [Con "concat" [Lit "\"TOKEN.\"", Con "stripAngleBrackets" [s]]])
astToGrammarSpecial _ = Nothing

astToGrammarSeq :: Term -> Maybe Term
astToGrammarSeq (Con "astToGrammar" [(Con "Con" [(Lit "\"seq\""), args])]) = Just (Con "foldr" [Con "GSeq" [], Con "GEmpty" [], Con "map" [Con "astToGrammar" [], args]])
astToGrammarSeq _ = Nothing

astToGrammarAlt :: Term -> Maybe Term
astToGrammarAlt (Con "astToGrammar" [(Con "Con" [(Lit "\"alt\""), args])]) = Just (Con "let" [Var "parts", Con "splitByPipe" [args], Con "foldr1" [Con "GAlt" [], Con "map" [Con "astToGrammar" [], Var "parts"]]])
astToGrammarAlt _ = Nothing

astToGrammarStar :: Term -> Maybe Term
astToGrammarStar (Con "astToGrammar" [(Con "Con" [(Lit "\"star\""), (Con "Cons" [g, (Con "Nil" [])])])]) = Just (Con "GStar" [Con "astToGrammar" [g]])
astToGrammarStar _ = Nothing

astToGrammarPlus :: Term -> Maybe Term
astToGrammarPlus (Con "astToGrammar" [(Con "Con" [(Lit "\"plus\""), (Con "Cons" [g, (Con "Nil" [])])])]) = Just (Con "GPlus" [Con "astToGrammar" [g]])
astToGrammarPlus _ = Nothing

astToGrammarOpt :: Term -> Maybe Term
astToGrammarOpt (Con "astToGrammar" [(Con "Con" [(Lit "\"opt\""), (Con "Cons" [g, (Con "Nil" [])])])]) = Just (Con "GOpt" [Con "astToGrammar" [g]])
astToGrammarOpt _ = Nothing

astToGrammarNot :: Term -> Maybe Term
astToGrammarNot (Con "astToGrammar" [(Con "Con" [(Lit "\"not\""), (Con "Cons" [g, (Con "Nil" [])])])]) = Just (Con "GNot" [Con "astToGrammar" [g]])
astToGrammarNot _ = Nothing

astToGrammarAnd :: Term -> Maybe Term
astToGrammarAnd (Con "astToGrammar" [(Con "Con" [(Lit "\"and\""), (Con "Cons" [g, (Con "Nil" [])])])]) = Just (Con "GAnd" [Con "astToGrammar" [g]])
astToGrammarAnd _ = Nothing

extractParentNames :: Term -> Maybe Term
extractParentNames (Con "extractParentNames" [(Con "Con" [(Lit "\"DLang\""), args])]) = Just (Con "filterMap" [Con "extractParentFromArg" [], args])
extractParentNames _ = Nothing

extractParentNamesOther :: Term -> Maybe Term
extractParentNamesOther (Con "extractParentNames" [other]) = Just (Con "Nil" [])
extractParentNamesOther _ = Nothing

extractParentFromArg :: Term -> Maybe Term
extractParentFromArg (Con "extractParentFromArg" [(Con "Con" [(Lit "\"DImports\""), imports])]) = Just (Con "Some" [Con "filterMap" [Con "extractIdentName" [], imports]])
extractParentFromArg _ = Nothing

extractParentFromArgOther :: Term -> Maybe Term
extractParentFromArgOther (Con "extractParentFromArg" [other]) = Just (Con "None" [])
extractParentFromArgOther _ = Nothing

extractIdentName :: Term -> Maybe Term
extractIdentName (Con "extractIdentName" [(Con "Con" [(Lit "\"ident\""), (Con "Cons" [(Con "Var" [name]), (Con "Nil" [])])])]) = Just (Con "Some" [name])
extractIdentName _ = Nothing

extractIdentNameOther :: Term -> Maybe Term
extractIdentNameOther (Con "extractIdentName" [other]) = Just (Con "None" [])
extractIdentNameOther _ = Nothing

extractProductions :: Term -> Maybe Term
extractProductions (Con "extractProductions" [(Con "Con" [(Lit "\"DGrammar\""), (Con "Cons" [(Con "Con" [(Lit "\"ident\""), (Con "Cons" [(Con "Var" [lang]), (Con "Nil" [])])]), (Con "Cons" [pieces, (Con "Nil" [])])])])]) = Just (Con "concatMap" [Con "extractPieceProductions" [], Con "getList" [pieces]])
extractProductions _ = Nothing

extractPieceProductions :: Term -> Maybe Term
extractPieceProductions (Con "extractPieceProductions" [(Con "Con" [(Lit "\"DPiece\""), (Con "Cons" [(Con "Con" [(Lit "\"ident\""), (Con "Cons" [(Con "Var" [pieceName]), (Con "Nil" [])])]), (Con "Cons" [members, (Con "Nil" [])])])])]) = Just (Con "concatMap" [Con "extractMemberProd" [pieceName], Con "getList" [members]])
extractPieceProductions _ = Nothing

extractMemberProdSyntax :: Term -> Maybe Term
extractMemberProdSyntax (Con "extractMemberProd" [piece, (Con "Con" [(Lit "\"DSyntax\""), (Con "Cons" [(Con "Con" [(Lit "\"ident\""), (Con "Cons" [(Con "Var" [cat]), (Con "Nil" [])])]), (Con "Cons" [alts, (Con "Nil" [])])])])]) = Just (Con "map" [Con "mkProduction" [piece, cat], Con "splitByPipe" [Con "getList" [alts]]])
extractMemberProdSyntax _ = Nothing

mkProduction :: Term -> Maybe Term
mkProduction (Con "mkProduction" [piece, cat, alt]) = Just (Con "let" [Var "conName", Con "extractConName" [alt], Con "MkProd" [Con "concat" [piece, Con "concat" [Lit "\".\"", cat]], Con "astToGrammar" [alt], Var "conName"]])
mkProduction _ = Nothing

extractConName :: Term -> Maybe Term
extractConName (Con "extractConName" [alt]) = Just (Con "case" [Con "findArrow" [alt], Con "Some" [Var "name"], Var "name", Con "None" [], Lit "\"node\""])
extractConName _ = Nothing

extractRules :: Term -> Maybe Term
extractRules (Con "extractRules" [(Con "Con" [(Lit "\"DGrammar\""), (Con "Cons" [lang, (Con "Cons" [pieces, (Con "Nil" [])])])])]) = Just (Con "concatMap" [Con "extractPieceRules" [], Con "getList" [pieces]])
extractRules _ = Nothing

extractPieceRules :: Term -> Maybe Term
extractPieceRules (Con "extractPieceRules" [(Con "Con" [(Lit "\"DPiece\""), (Con "Cons" [name, (Con "Cons" [members, (Con "Nil" [])])])])]) = Just (Con "filterMap" [Con "extractRule" [], Con "getList" [members]])
extractPieceRules _ = Nothing

extractRule :: Term -> Maybe Term
extractRule (Con "extractRule" [(Con "Con" [(Lit "\"DRule\""), (Con "Cons" [(Con "Con" [(Lit "\"ident\""), (Con "Cons" [(Con "Var" [name]), (Con "Nil" [])])]), (Con "Cons" [pat, (Con "Cons" [template, (Con "Nil" [])])])])])]) = Just (Con "Some" [Con "MkRule" [name, pat, template]])
extractRule _ = Nothing

extractRuleNone :: Term -> Maybe Term
extractRuleNone (Con "extractRule" [other]) = Just (Con "None" [])
extractRuleNone _ = Nothing

parseWithGrammar :: Term -> Maybe Term
parseWithGrammar (Con "parseWithGrammar" [(Con "MkGrammar" [prods, tokProds, syms, start]), input]) = Just (Con "let" [Var "tokens", Con "tokenize" [input], Con "let" [Var "state", Con "MkState" [Var "tokens", Lit "0"], Con "parseProduction" [start, prods, Var "state"]]])
parseWithGrammar _ = Nothing

parseProduction :: Term -> Maybe Term
parseProduction (Con "parseProduction" [name, prods, state]) = Just (Con "case" [Con "findProd" [name, prods], Con "Some" [Con "MkProd" [Var "n", Var "g", Var "c"]], Con "parse" [Var "g", state], Con "None" [], Con "ParseFail" [Con "concat" [Lit "\"unknown production: \"", name], state]])
parseProduction _ = Nothing

findProdHit :: Term -> Maybe Term
findProdHit (Con "findProd" [name, (Con "Cons" [(Con "MkProd" [name0, g, c]), rest])]) | name0 == name = Just (Con "Some" [Con "MkProd" [name, g, c]])
findProdHit _ = Nothing

findProdMiss :: Term -> Maybe Term
findProdMiss (Con "findProd" [name, (Con "Cons" [(Con "MkProd" [other, g, c]), rest])]) = Just (Con "findProd" [name, rest])
findProdMiss _ = Nothing

findProdEmpty :: Term -> Maybe Term
findProdEmpty (Con "findProd" [name, (Con "Nil" [])]) = Just (Con "None" [])
findProdEmpty _ = Nothing

printWithGrammar :: Term -> Maybe Term
printWithGrammar (Con "printWithGrammar" [(Con "MkGrammar" [prods, tokProds, syms, start]), prodName, term]) = Just (Con "case" [Con "findProd" [prodName, prods], Con "Some" [Con "MkProd" [Var "n", Var "g", Var "c"]], Con "print" [Var "g", term], Con "None" [], Con "PrintFail" [Con "concat" [Lit "\"unknown production: \"", prodName]]])
printWithGrammar _ = Nothing

stripQuotes :: Term -> Maybe Term
stripQuotes (Con "stripQuotes" [s]) = Just (Con "if" [Con "and" [Con "startsWith" [s, Lit "\"\\\"\""], Con "endsWith" [s, Lit "\"\\\"\""]], Con "drop" [Lit "1", Con "dropRight" [Lit "1", s]], s])
stripQuotes _ = Nothing

stripAngleBrackets :: Term -> Maybe Term
stripAngleBrackets (Con "stripAngleBrackets" [s]) = Just (Con "if" [Con "and" [Con "startsWith" [s, Lit "\"<\""], Con "endsWith" [s, Lit "\">\""]], Con "drop" [Lit "1", Con "dropRight" [Lit "1", s]], s])
stripAngleBrackets _ = Nothing

splitByPipe :: Term -> Maybe Term
splitByPipe (Con "splitByPipe" [ts]) = Just (Con "splitBy" [Con "Lit" [Lit "\"|\""], ts])
splitByPipe _ = Nothing

getList :: Term -> Maybe Term
getList (Con "getList" [(Con "Con" [(Lit "\"list\""), xs])]) = Just (xs)
getList _ = Nothing

getListOther :: Term -> Maybe Term
getListOther (Con "getList" [v_t]) = Just (Con "Cons" [v_t, Con "Nil" []])
getListOther _ = Nothing

rtGrammar :: Term -> Maybe Term
rtGrammar (Con "rtGrammar" [(Con "MkRuntime" [grammar, rules])]) = Just (grammar)
rtGrammar _ = Nothing

rtRules :: Term -> Maybe Term
rtRules (Con "rtRules" [(Con "MkRuntime" [grammar, rules])]) = Just (rules)
rtRules _ = Nothing

loadBootstrap :: Term -> Maybe Term
loadBootstrap (Con "loadBootstrap" [content]) = Just (Con "case" [Con "parseBootstrap" [content], Con "Some" [Var "ast"], Con "let" [Var "prods", Con "extractProductions" [Var "ast"], Con "let" [Var "rules", Con "extractRules" [Var "ast"], Con "Some" [Con "MkRuntime" [Con "MkGrammar" [Var "prods", Con "Nil" [], Con "Nil" [], Lit "\"File.legoFile\""], Var "rules"]]]], Con "None" [], Con "None" []])
loadBootstrap _ = Nothing

parseBootstrap :: Term -> Maybe Term
parseBootstrap (Con "parseBootstrap" [content]) = Just (Con "hardcodedParse" [content])
parseBootstrap _ = Nothing

loadLego :: Term -> Maybe Term
loadLego (Con "loadLego" [bootstrapRt, content]) = Just (Con "case" [Con "parseLegoFile" [bootstrapRt, content], Con "Some" [Var "ast"], Con "let" [Var "prods", Con "extractProductions" [Var "ast"], Con "let" [Var "rules", Con "extractRules" [Var "ast"], Con "let" [Var "bootstrapProds", Con "rtGrammar" [bootstrapRt], Con "Some" [Con "MkRuntime" [Con "MkGrammar" [Con "append" [Var "prods", Con "grammarProds" [Var "bootstrapProds"]], Con "Nil" [], Con "Nil" [], Lit "\"File.legoFile\""], Con "append" [Var "rules", Con "rtRules" [bootstrapRt]]]]]]], Con "None" [], Con "None" []])
loadLego _ = Nothing

parseLegoFile :: Term -> Maybe Term
parseLegoFile (Con "parseLegoFile" [rt, content]) = Just (Con "parseWithGrammar" [Con "rtGrammar" [rt], content])
parseLegoFile _ = Nothing

parseLegoFileE :: Term -> Maybe Term
parseLegoFileE (Con "parseLegoFileE" [rt, content]) = Just (Con "case" [Con "parseWithGrammar" [Con "rtGrammar" [rt], content], Con "ParseOk" [Var "t", Var "s"], Con "Ok" [Var "t"], Con "ParseFail" [Var "msg", Var "s"], Con "Err" [Var "msg"]])
parseLegoFileE _ = Nothing

loadLanguage :: Term -> Maybe Term
loadLanguage (Con "loadLanguage" [rt, path]) = Just (Con "loadLanguageWithParents" [rt, path, Con "Nil" []])
loadLanguage _ = Nothing

loadLanguageWithParents :: Term -> Maybe Term
loadLanguageWithParents (Con "loadLanguageWithParents" [rt, path, visited]) = Just (Con "if" [Con "elem" [path, visited], Con "Err" [Con "concat" [Lit "\"Circular language inheritance: \"", path]], Con "case" [Con "readFile" [path], Con "Some" [Var "content"], Con "loadLanguageContent" [rt, path, Var "content", Con "Cons" [path, visited]], Con "None" [], Con "Err" [Con "concat" [Lit "\"Cannot read file: \"", path]]]])
loadLanguageWithParents _ = Nothing

loadLanguageContent :: Term -> Maybe Term
loadLanguageContent (Con "loadLanguageContent" [rt, path, content, visited]) = Just (Con "case" [Con "parseLegoFile" [rt, content], Con "Some" [Var "ast"], Con "let" [Var "parentNames", Con "extractParentNames" [Var "ast"], Con "loadWithParents" [rt, path, Var "ast", Var "parentNames", visited]], Con "None" [], Con "Err" [Lit "\"parse failed\""]])
loadLanguageContent _ = Nothing

loadWithParents :: Term -> Maybe Term
loadWithParents (Con "loadWithParents" [rt, path, ast, parentNames, visited]) = Just (Con "case" [Con "loadParentGrammars" [rt, path, parentNames, visited], Con "Ok" [Var "inheritedProds", Var "inheritedTokProds"], Con "let" [Var "childProds", Con "extractProductions" [ast], Con "let" [Var "childTokProds", Con "extractTokenProductions" [ast], Con "let" [Var "mergedProds", Con "append" [Var "inheritedProds", Var "childProds"], Con "let" [Var "mergedTokProds", Con "append" [Var "inheritedTokProds", Var "childTokProds"], Con "let" [Var "syms", Con "extractSymbols" [Var "mergedProds"], Con "let" [Var "start", Con "findStartProd" [Var "childProds"], Con "Ok" [Con "MkGrammar" [Var "mergedProds", Var "mergedTokProds", Var "syms", Var "start"]]]]]]]], Con "Err" [Var "e"], Con "Err" [Var "e"]])
loadWithParents _ = Nothing

loadParentGrammars :: Term -> Maybe Term
loadParentGrammars (Con "loadParentGrammars" [rt, childPath, (Con "Nil" []), visited]) = Just (Con "Ok" [Con "Nil" [], Con "Nil" []])
loadParentGrammars _ = Nothing

loadParentGrammarsNonEmpty :: Term -> Maybe Term
loadParentGrammarsNonEmpty (Con "loadParentGrammars" [rt, childPath, (Con "Cons" [parent, rest]), visited]) = Just (Con "case" [Con "resolveParentPath" [parent, childPath], Con "Some" [Var "parentPath"], Con "case" [Con "loadLanguageWithParents" [rt, Var "parentPath", visited], Con "Ok" [Var "parentGrammar"], Con "case" [Con "loadParentGrammars" [rt, childPath, rest, visited], Con "Ok" [Var "restProds", Var "restTokProds"], Con "Ok" [Con "append" [Con "grammarProds" [Var "parentGrammar"], Var "restProds"], Con "append" [Con "grammarTokProds" [Var "parentGrammar"], Var "restTokProds"]], Con "Err" [Var "e"], Con "Err" [Var "e"]], Con "Err" [Var "e"], Con "Err" [Con "concat" [Lit "\"Failed to load parent \"", Con "concat" [parent, Con "concat" [Lit "\": \"", Var "e"]]]]], Con "None" [], Con "if" [Con "eq" [parent, Lit "\"Bootstrap\""], Con "case" [Con "loadParentGrammars" [rt, childPath, rest, visited], Con "Ok" [Var "restProds", Var "restTokProds"], Con "Ok" [Con "append" [Con "grammarProds" [Con "rtGrammar" [rt]], Var "restProds"], Con "append" [Con "grammarTokProds" [Con "rtGrammar" [rt]], Var "restTokProds"]], Con "Err" [Var "e"], Con "Err" [Var "e"]], Con "Err" [Con "concat" [Lit "\"Cannot find parent language: \"", parent]]]])
loadParentGrammarsNonEmpty _ = Nothing

resolveParentPath :: Term -> Maybe Term
resolveParentPath (Con "resolveParentPath" [parentName, childPath]) = Just (Con "findFirst" [Con "fileExists" [], Con "Cons" [Con "concat" [Con "dirname" [childPath], Con "concat" [Lit "\"/\"", Con "concat" [parentName, Lit "\".lego\""]]], Con "Cons" [Con "concat" [Lit "\"test/\"", Con "concat" [parentName, Lit "\".lego\""]], Con "Cons" [Con "concat" [Lit "\"src/Lego/\"", Con "concat" [parentName, Lit "\".lego\""]], Con "Cons" [Con "concat" [Lit "\"src/Rosetta/\"", Con "concat" [parentName, Lit "\".lego\""]], Con "Nil" []]]]]])
resolveParentPath _ = Nothing

grammarProds :: Term -> Maybe Term
grammarProds (Con "grammarProds" [(Con "MkGrammar" [prods, tokProds, syms, start])]) = Just (prods)
grammarProds _ = Nothing

grammarTokProds :: Term -> Maybe Term
grammarTokProds (Con "grammarTokProds" [(Con "MkGrammar" [prods, tokProds, syms, start])]) = Just (tokProds)
grammarTokProds _ = Nothing

extractTokenProductions :: Term -> Maybe Term
extractTokenProductions (Con "extractTokenProductions" [ast]) = Just (Con "filter" [Con "isTokenProd" [], Con "extractProductions" [ast]])
extractTokenProductions _ = Nothing

isTokenProd :: Term -> Maybe Term
isTokenProd (Con "isTokenProd" [(Con "MkProd" [name, g, c])]) = Just (Con "startsWith" [name, Lit "\"TOKEN.\""])
isTokenProd _ = Nothing

extractSymbols :: Term -> Maybe Term
extractSymbols (Con "extractSymbols" [prods]) = Just (Con "nub" [Con "concatMap" [Con "prodSymbols" [], prods]])
extractSymbols _ = Nothing

prodSymbols :: Term -> Maybe Term
prodSymbols (Con "prodSymbols" [(Con "MkProd" [name, g, c])]) = Just (Con "grammarSymbols" [g])
prodSymbols _ = Nothing

grammarSymbolsRef :: Term -> Maybe Term
grammarSymbolsRef (Con "grammarSymbols" [(Con "GRef" [name])]) = Just (Con "Cons" [name, Con "Nil" []])
grammarSymbolsRef _ = Nothing

grammarSymbolsSeq :: Term -> Maybe Term
grammarSymbolsSeq (Con "grammarSymbols" [(Con "GSeq" [g1, g2])]) = Just (Con "append" [Con "grammarSymbols" [g1], Con "grammarSymbols" [g2]])
grammarSymbolsSeq _ = Nothing

grammarSymbolsAlt :: Term -> Maybe Term
grammarSymbolsAlt (Con "grammarSymbols" [(Con "GAlt" [g1, g2])]) = Just (Con "append" [Con "grammarSymbols" [g1], Con "grammarSymbols" [g2]])
grammarSymbolsAlt _ = Nothing

grammarSymbolsStar :: Term -> Maybe Term
grammarSymbolsStar (Con "grammarSymbols" [(Con "GStar" [g])]) = Just (Con "grammarSymbols" [g])
grammarSymbolsStar _ = Nothing

grammarSymbolsOther :: Term -> Maybe Term
grammarSymbolsOther (Con "grammarSymbols" [g]) = Just (Con "Nil" [])
grammarSymbolsOther _ = Nothing

findStartProd :: Term -> Maybe Term
findStartProd (Con "findStartProd" [(Con "Cons" [(Con "MkProd" [name, g, c]), rest])]) = Just (name)
findStartProd _ = Nothing

findStartProdEmpty :: Term -> Maybe Term
findStartProdEmpty (Con "findStartProd" [(Con "Nil" [])]) = Just (Lit "\"File.legoFile\"")
findStartProdEmpty _ = Nothing

normalize :: Term -> Maybe Term
normalize (Con "normalize" [rt, term]) = Just (Con "normalizeWith" [Lit "1000", Con "rtRules" [rt], term])
normalize _ = Nothing

normalizeWith :: Term -> Maybe Term
normalizeWith (Con "normalizeWith" [(Lit "0"), rules, v_t]) = Just (v_t)
normalizeWith _ = Nothing

normalizeWithFuel :: Term -> Maybe Term
normalizeWithFuel (Con "normalizeWith" [n, rules, v_t]) = Just (Con "case" [Con "tryApplyRules" [rules, v_t], Con "Some" [Var "t'"], Con "normalizeWith" [Con "sub" [n, Lit "1"], rules, Var "t'"], Con "None" [], Con "normalizeChildren" [n, rules, v_t]])
normalizeWithFuel _ = Nothing

tryApplyRules :: Term -> Maybe Term
tryApplyRules (Con "tryApplyRules" [(Con "Cons" [(Con "MkRule" [name, pat, tmpl]), rest]), v_t]) = Just (Con "case" [Con "matchPat" [pat, v_t], Con "Some" [Var "bindings"], Con "Some" [Con "subst" [tmpl, Var "bindings"]], Con "None" [], Con "tryApplyRules" [rest, v_t]])
tryApplyRules _ = Nothing

tryApplyRulesEmpty :: Term -> Maybe Term
tryApplyRulesEmpty (Con "tryApplyRules" [(Con "Nil" []), v_t]) = Just (Con "None" [])
tryApplyRulesEmpty _ = Nothing

normalizeChildren :: Term -> Maybe Term
normalizeChildren (Con "normalizeChildren" [n, rules, (Con "Var" [x])]) = Just (Con "Var" [x])
normalizeChildren _ = Nothing

printTerm :: Term -> Maybe Term
printTerm (Con "printTerm" [rt, term, prodName]) = Just (Con "case" [Con "printWithGrammar" [Con "rtGrammar" [rt], prodName, term], Con "PrintOk" [Var "tokens"], Con "Some" [Con "joinTokens" [Var "tokens"]], Con "PrintFail" [Var "msg"], Con "None" []])
printTerm _ = Nothing

joinTokens :: Term -> Maybe Term
joinTokens (Con "joinTokens" [tokens]) = Just (Con "intercalate" [Lit "\" \"", Con "map" [Con "tokenToString" [], tokens]])
joinTokens _ = Nothing

tokenToString :: Term -> Maybe Term
tokenToString (Con "tokenToString" [(Con "TokIdent" [s])]) = Just (s)
tokenToString _ = Nothing

tokenToStringStr :: Term -> Maybe Term
tokenToStringStr (Con "tokenToString" [(Con "TokString" [s])]) = Just (Con "concat" [Lit "\"\\\"\"", Con "concat" [s, Lit "\"\\\"\""]])
tokenToStringStr _ = Nothing

tokenToStringSym :: Term -> Maybe Term
tokenToStringSym (Con "tokenToString" [(Con "TokSym" [s])]) = Just (s)
tokenToStringSym _ = Nothing

initRuntime :: Term -> Maybe Term
initRuntime (Con "initRuntime" [bootstrapContent, legoContent]) = Just (Con "case" [Con "loadBootstrap" [bootstrapContent], Con "Some" [Var "bootstrapRt"], Con "case" [Con "loadLego" [Var "bootstrapRt", legoContent], Con "Some" [Var "legoRt"], Con "Ok" [Var "legoRt"], Con "None" [], Con "Err" [Lit "\"failed to load Lego.lego\""]], Con "None" [], Con "Err" [Lit "\"failed to load Bootstrap.lego\""]])
initRuntime _ = Nothing

valErrorFormat :: Term -> Maybe Term
valErrorFormat (Con "valErrorFormat" [(Con "UndefinedProduction" [ref, source])]) = Just (Con "concat" [Con "concat" [Con "concat" [Lit "\"ERROR: Undefined production '\"", ref], Lit "\"' referenced from '\""], Con "concat" [source, Lit "\"'\""]])
valErrorFormat _ = Nothing

valErrorFormatDup :: Term -> Maybe Term
valErrorFormatDup (Con "valErrorFormat" [(Con "DuplicateProduction" [name])]) = Just (Con "concat" [Con "concat" [Lit "\"ERROR: Duplicate production '\"", name], Lit "\"'\""])
valErrorFormatDup _ = Nothing

valErrorFormatUnbound :: Term -> Maybe Term
valErrorFormatUnbound (Con "valErrorFormat" [(Con "UnboundVariable" [var, rule])]) = Just (Con "concat" [Con "concat" [Con "concat" [Con "concat" [Lit "\"ERROR: Unbound variable '\"", var], Lit "\"' in rule '\""], rule], Lit "\"'\""])
valErrorFormatUnbound _ = Nothing

valErrorFormatCircular :: Term -> Maybe Term
valErrorFormatCircular (Con "valErrorFormat" [(Con "CircularImport" [mod])]) = Just (Con "concat" [Con "concat" [Lit "\"ERROR: Circular import of '\"", mod], Lit "\"'\""])
valErrorFormatCircular _ = Nothing

valErrorFormatInvalid :: Term -> Maybe Term
valErrorFormatInvalid (Con "valErrorFormat" [(Con "InvalidSyntax" [ctx, msg])]) = Just (Con "concat" [Con "concat" [Con "concat" [Lit "\"ERROR: Invalid syntax in \"", ctx], Lit "\": \""], msg])
valErrorFormatInvalid _ = Nothing

valWarnFormatConflict :: Term -> Maybe Term
valWarnFormatConflict (Con "valWarnFormat" [(Con "ConflictingRules" [r1, r2, reason])]) = Just (Con "concat" [Con "concat" [Con "concat" [Con "concat" [Con "concat" [Lit "\"WARNING: Conflicting rules '\"", r1], Lit "\"' and '\""], r2], Lit "\"': \""], reason])
valWarnFormatConflict _ = Nothing

valWarnFormatDirectLR :: Term -> Maybe Term
valWarnFormatDirectLR (Con "valWarnFormat" [(Con "DirectLeftRecursion" [name])]) = Just (Con "concat" [Con "concat" [Lit "\"WARNING: Direct left recursion in production '\"", name], Lit "\"'\""])
valWarnFormatDirectLR _ = Nothing

valWarnFormatIndirectLR :: Term -> Maybe Term
valWarnFormatIndirectLR (Con "valWarnFormat" [(Con "IndirectLeftRecursion" [path])]) = Just (Con "concat" [Lit "\"WARNING: Indirect left recursion: \"", Con "intercalate" [Lit "\" -> \"", path]])
valWarnFormatIndirectLR _ = Nothing

valWarnFormatUnused :: Term -> Maybe Term
valWarnFormatUnused (Con "valWarnFormat" [(Con "UnusedProduction" [name])]) = Just (Con "concat" [Con "concat" [Lit "\"WARNING: Unused production '\"", name], Lit "\"'\""])
valWarnFormatUnused _ = Nothing

valWarnFormatShadow :: Term -> Maybe Term
valWarnFormatShadow (Con "valWarnFormat" [(Con "ShadowedProduction" [name, by])]) = Just (Con "concat" [Con "concat" [Con "concat" [Con "concat" [Lit "\"WARNING: Production '\"", name], Lit "\"' shadowed by '\""], by], Lit "\"'\""])
valWarnFormatShadow _ = Nothing

valWarnFormatAmbig :: Term -> Maybe Term
valWarnFormatAmbig (Con "valWarnFormat" [(Con "AmbiguousGrammar" [name, reason])]) = Just (Con "concat" [Con "concat" [Con "concat" [Con "concat" [Lit "\"WARNING: Ambiguous grammar for '\"", name], Lit "\"': \""], reason], Lit "\"\""])
valWarnFormatAmbig _ = Nothing

valWarnFormatMissingCut :: Term -> Maybe Term
valWarnFormatMissingCut (Con "valWarnFormat" [(Con "MissingCut" [prod, kw])]) = Just (Con "concat" [Con "concat" [Con "concat" [Con "concat" [Lit "\"OPTIMIZE: Production '\"", prod], Lit "\"' could add cut after '\""], kw], Lit "\"' for better errors\""])
valWarnFormatMissingCut _ = Nothing

valWarnFormatCycle :: Term -> Maybe Term
valWarnFormatCycle (Con "valWarnFormat" [(Con "RuleCycle" [cycle])]) = Just (Con "concat" [Lit "\"WARNING: Potential non-terminating rule cycle: \"", Con "intercalate" [Lit "\" -> \"", cycle]])
valWarnFormatCycle _ = Nothing

valWarnFormatUnreachable :: Term -> Maybe Term
valWarnFormatUnreachable (Con "valWarnFormat" [(Con "UnreachableAlt" [prod, idx])]) = Just (Con "concat" [Con "concat" [Con "concat" [Lit "\"WARNING: Alternative \"", Con "toString" [idx]], Lit "\" in '\""], Con "concat" [prod, Lit "\"' is unreachable\""]])
valWarnFormatUnreachable _ = Nothing

valWarnFormatRedundant :: Term -> Maybe Term
valWarnFormatRedundant (Con "valWarnFormat" [(Con "RedundantAlt" [prod, i, j])]) = Just (Con "concat" [Con "concat" [Con "concat" [Con "concat" [Con "concat" [Lit "\"WARNING: Alternatives \"", Con "toString" [i]], Lit "\" and \""], Con "toString" [j]], Lit "\" in '\""], Con "concat" [prod, Lit "\"' are redundant\""]])
valWarnFormatRedundant _ = Nothing

valResultEmpty :: Term -> Maybe Term
valResultEmpty (Con "valResultEmpty" []) = Just (Con "MkValidationResult" [Con "Nil" [], Con "Nil" []])
valResultEmpty _ = Nothing

valResultAppend :: Term -> Maybe Term
valResultAppend (Con "valResultAppend" [(Con "MkValidationResult" [e1, w1]), (Con "MkValidationResult" [e2, w2])]) = Just (Con "MkValidationResult" [Con "append" [e1, e2], Con "append" [w1, w2]])
valResultAppend _ = Nothing

valResultAddError :: Term -> Maybe Term
valResultAddError (Con "valResultAddError" [(Con "MkValidationResult" [errs, warns]), e]) = Just (Con "MkValidationResult" [Con "Cons" [e, errs], warns])
valResultAddError _ = Nothing

valResultAddWarning :: Term -> Maybe Term
valResultAddWarning (Con "valResultAddWarning" [(Con "MkValidationResult" [errs, warns]), w]) = Just (Con "MkValidationResult" [errs, Con "Cons" [w, warns]])
valResultAddWarning _ = Nothing

valResultHasErrors :: Term -> Maybe Term
valResultHasErrors (Con "valResultHasErrors" [(Con "MkValidationResult" [errs, warns])]) = Just (Con "not" [Con "null" [errs]])
valResultHasErrors _ = Nothing

valResultFormat :: Term -> Maybe Term
valResultFormat (Con "valResultFormat" [(Con "MkValidationResult" [errs, warns])]) = Just (Con "append" [Con "map" [Con "valErrorFormat" [], errs], Con "map" [Con "valWarnFormat" [], warns]])
valResultFormat _ = Nothing

builtinProductions :: Term -> Maybe Term
builtinProductions (Con "builtinProductions" []) = Just (Con "Cons" [Lit "\"nat\"", Con "Cons" [Lit "\"int\"", Con "Cons" [Lit "\"str\"", Con "Cons" [Lit "\"string\"", Con "Cons" [Lit "\"ident\"", Con "Cons" [Lit "\"char\"", Con "Cons" [Lit "\"float\"", Con "Cons" [Lit "\"bool\"", Con "Nil" []]]]]]]]])
builtinProductions _ = Nothing

extractRefsEmpty :: Term -> Maybe Term
extractRefsEmpty (Con "extractRefs" [(Con "GEmpty" [])]) = Just (Con "Nil" [])
extractRefsEmpty _ = Nothing

extractRefsLit :: Term -> Maybe Term
extractRefsLit (Con "extractRefs" [(Con "GLit" [s])]) = Just (Con "Nil" [])
extractRefsLit _ = Nothing

extractRefsRef :: Term -> Maybe Term
extractRefsRef (Con "extractRefs" [(Con "GRef" [name])]) = Just (Con "Cons" [name, Con "Nil" []])
extractRefsRef _ = Nothing

extractRefsSeq :: Term -> Maybe Term
extractRefsSeq (Con "extractRefs" [(Con "GSeq" [g1, g2])]) = Just (Con "append" [Con "extractRefs" [g1], Con "extractRefs" [g2]])
extractRefsSeq _ = Nothing

extractRefsAlt :: Term -> Maybe Term
extractRefsAlt (Con "extractRefs" [(Con "GAlt" [g1, g2])]) = Just (Con "append" [Con "extractRefs" [g1], Con "extractRefs" [g2]])
extractRefsAlt _ = Nothing

extractRefsStar :: Term -> Maybe Term
extractRefsStar (Con "extractRefs" [(Con "GStar" [g])]) = Just (Con "extractRefs" [g])
extractRefsStar _ = Nothing

extractRefsPlus :: Term -> Maybe Term
extractRefsPlus (Con "extractRefs" [(Con "GPlus" [g])]) = Just (Con "extractRefs" [g])
extractRefsPlus _ = Nothing

extractRefsOpt :: Term -> Maybe Term
extractRefsOpt (Con "extractRefs" [(Con "GOpt" [g])]) = Just (Con "extractRefs" [g])
extractRefsOpt _ = Nothing

extractRefsNot :: Term -> Maybe Term
extractRefsNot (Con "extractRefs" [(Con "GNot" [g])]) = Just (Con "extractRefs" [g])
extractRefsNot _ = Nothing

extractRefsAnd :: Term -> Maybe Term
extractRefsAnd (Con "extractRefs" [(Con "GAnd" [g])]) = Just (Con "extractRefs" [g])
extractRefsAnd _ = Nothing

extractRefsCon :: Term -> Maybe Term
extractRefsCon (Con "extractRefs" [(Con "GCon" [name, g])]) = Just (Con "extractRefs" [g])
extractRefsCon _ = Nothing

checkUndefinedRefs :: Term -> Maybe Term
checkUndefinedRefs (Con "checkUndefinedRefs" [grammar]) = Just (Con "let" [Var "defined", Con "grammarDefinedNames" [grammar], Con "let" [Var "builtins", Con "builtinProductions" [], Con "foldl" [Con "acc" [Con "binder" [Lit "prod", Con "let" [Var "refs", Con "extractRefs" [Con "grammarLookup" [grammar, Var "prod"]], Con "foldl" [Con "acc2" [Con "binder" [Lit "ref", Con "if" [Con "or" [Con "contains" [Var "defined", Var "ref"], Con "contains" [Var "builtins", Con "baseName" [Var "ref"]]], Var "acc2", Con "valResultAddError" [Var "acc2", Con "UndefinedProduction" [Var "ref", Var "prod"]]]]], Var "acc", Var "refs"]]]], Con "valResultEmpty" [], Con "grammarProductions" [grammar]]]])
checkUndefinedRefs _ = Nothing

isDirectLeftRecEmpty :: Term -> Maybe Term
isDirectLeftRecEmpty (Con "isDirectLeftRec" [name, (Con "GEmpty" [])]) = Just (Con "False" [])
isDirectLeftRecEmpty _ = Nothing

isDirectLeftRecLit :: Term -> Maybe Term
isDirectLeftRecLit (Con "isDirectLeftRec" [name, (Con "GLit" [s])]) = Just (Con "False" [])
isDirectLeftRecLit _ = Nothing

isDirectLeftRecRef :: Term -> Maybe Term
isDirectLeftRecRef (Con "isDirectLeftRec" [name, (Con "GRef" [ref])]) = Just (Con "eq" [ref, name])
isDirectLeftRecRef _ = Nothing

isDirectLeftRecSeq :: Term -> Maybe Term
isDirectLeftRecSeq (Con "isDirectLeftRec" [name, (Con "GSeq" [g1, g2])]) = Just (Con "isDirectLeftRec" [name, g1])
isDirectLeftRecSeq _ = Nothing

isDirectLeftRecAlt :: Term -> Maybe Term
isDirectLeftRecAlt (Con "isDirectLeftRec" [name, (Con "GAlt" [g1, g2])]) = Just (Con "or" [Con "isDirectLeftRec" [name, g1], Con "isDirectLeftRec" [name, g2]])
isDirectLeftRecAlt _ = Nothing

isDirectLeftRecStar :: Term -> Maybe Term
isDirectLeftRecStar (Con "isDirectLeftRec" [name, (Con "GStar" [g])]) = Just (Con "isDirectLeftRec" [name, g])
isDirectLeftRecStar _ = Nothing

isDirectLeftRecPlus :: Term -> Maybe Term
isDirectLeftRecPlus (Con "isDirectLeftRec" [name, (Con "GPlus" [g])]) = Just (Con "isDirectLeftRec" [name, g])
isDirectLeftRecPlus _ = Nothing

isDirectLeftRecOpt :: Term -> Maybe Term
isDirectLeftRecOpt (Con "isDirectLeftRec" [name, (Con "GOpt" [g])]) = Just (Con "isDirectLeftRec" [name, g])
isDirectLeftRecOpt _ = Nothing

isDirectLeftRecCon :: Term -> Maybe Term
isDirectLeftRecCon (Con "isDirectLeftRec" [name, (Con "GCon" [c, g])]) = Just (Con "isDirectLeftRec" [name, g])
isDirectLeftRecCon _ = Nothing

checkLeftRecursion :: Term -> Maybe Term
checkLeftRecursion (Con "checkLeftRecursion" [grammar]) = Just (Con "foldl" [Con "acc" [Con "binder" [Lit "prod", Con "if" [Con "isDirectLeftRec" [Var "prod", Con "grammarLookup" [grammar, Var "prod"]], Con "valResultAddWarning" [Var "acc", Con "DirectLeftRecursion" [Var "prod"]], Var "acc"]]], Con "valResultEmpty" [], Con "grammarProductions" [grammar]])
checkLeftRecursion _ = Nothing

varsInVar :: Term -> Maybe Term
varsInVar (Con "varsIn" [(Con "Var" [v])]) = Just (Con "Cons" [v, Con "Nil" []])
varsInVar _ = Nothing

varsInLit :: Term -> Maybe Term
varsInLit (Con "varsIn" [(Con "Lit" [s])]) = Just (Con "Nil" [])
varsInLit _ = Nothing

varsInCon :: Term -> Maybe Term
varsInCon (Con "varsIn" [(Con "Con" [c, args])]) = Just (Con "flatMap" [Con "varsIn" [], args])
varsInCon _ = Nothing

patternVarsVar :: Term -> Maybe Term
patternVarsVar (Con "patternVars" [(Con "Var" [v])]) = Just (Con "if" [Con "startsWith" [v, Lit "\"$\""], Con "Cons" [v, Con "Nil" []], Con "Nil" []])
patternVarsVar _ = Nothing

patternVarsLit :: Term -> Maybe Term
patternVarsLit (Con "patternVars" [(Con "Lit" [s])]) = Just (Con "Nil" [])
patternVarsLit _ = Nothing

patternVarsCon :: Term -> Maybe Term
patternVarsCon (Con "patternVars" [(Con "Con" [c, args])]) = Just (Con "flatMap" [Con "patternVars" [], args])
patternVarsCon _ = Nothing

checkUnboundVars :: Term -> Maybe Term
checkUnboundVars (Con "checkUnboundVars" [rules]) = Just (Con "foldl" [Con "acc" [Con "binder" [Lit "rule", Con "let" [Var "patVars", Con "patternVars" [Con "rulePattern" [Var "rule"]], Con "let" [Var "tplVars", Con "filter" [Con "binder" [Lit "v", Con "startsWith" [Var "v", Lit "\"$\""]], Con "varsIn" [Con "ruleTemplate" [Var "rule"]]], Con "let" [Var "unbound", Con "filter" [Con "binder" [Lit "v", Con "not" [Con "contains" [Var "patVars", Var "v"]]], Var "tplVars"], Con "foldl" [Con "acc2" [Con "binder" [Lit "v", Con "valResultAddError" [Var "acc2", Con "UnboundVariable" [Var "v", Con "ruleName" [Var "rule"]]]]], Var "acc", Var "unbound"]]]]]], Con "valResultEmpty" [], rules])
checkUnboundVars _ = Nothing

patternKeyVar :: Term -> Maybe Term
patternKeyVar (Con "patternKey" [(Con "Var" [v])]) = Just (Lit "\"_\"")
patternKeyVar _ = Nothing

patternKeyLit :: Term -> Maybe Term
patternKeyLit (Con "patternKey" [(Con "Lit" [s])]) = Just (Con "concat" [Con "concat" [Lit "\"\\\"\"", s], Lit "\"\\\"\""])
patternKeyLit _ = Nothing

patternKeyCon :: Term -> Maybe Term
patternKeyCon (Con "patternKey" [(Con "Con" [name, args])]) = Just (Con "concat" [Con "concat" [Con "concat" [Lit "\"(\"", name], Con "concat" [Lit "\" \"", Con "intercalate" [Lit "\" \"", Con "map" [Con "patternKey" [], args]]]], Lit "\")\""])
patternKeyCon _ = Nothing

checkConflictingRules :: Term -> Maybe Term
checkConflictingRules (Con "checkConflictingRules" [rules]) = Just (Con "let" [Var "grouped", Con "groupBy" [Con "binder" [Lit "r", Con "patternKey" [Con "rulePattern" [Var "r"]]], rules], Con "foldl" [Con "acc" [Con "binder" [Lit "group", Con "if" [Con "gt" [Con "length" [Var "group"], Lit "1"], Con "let" [Var "names", Con "map" [Con "ruleName" [], Var "group"], Con "valResultAddWarning" [Var "acc", Con "ConflictingRules" [Con "head" [Var "names"], Con "head" [Con "tail" [Var "names"]], Lit "\"same pattern structure\""]]], Var "acc"]]], Con "valResultEmpty" [], Con "mapValues" [Var "grouped"]]])
checkConflictingRules _ = Nothing

validateGrammar :: Term -> Maybe Term
validateGrammar (Con "validateGrammar" [grammar, rules]) = Just (Con "valResultAppend" [Con "valResultAppend" [Con "checkUndefinedRefs" [grammar], Con "checkLeftRecursion" [grammar]], Con "valResultAppend" [Con "checkUnboundVars" [rules], Con "checkConflictingRules" [rules]]])
validateGrammar _ = Nothing

formatValidationResult :: Term -> Maybe Term
formatValidationResult (Con "formatValidationResult" [result]) = Just (Con "let" [Var "lines", Con "valResultFormat" [result], Con "intercalate" [Lit "\"\\n\"", Var "lines"]])
formatValidationResult _ = Nothing

