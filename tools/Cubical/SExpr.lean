/-
  Cubical.SExpr: S-expression parser for Grammar.sexpr

  This parses the portable grammar format (Grammar.sexpr) which is
  the single source of truth for code generation to multiple targets.

  NOTE: Uses String.Pos for proper UTF-8 handling.
-/

namespace Cubical

/-! ## S-Expression AST -/

/-- S-expression: the universal interchange format -/
inductive SExpr where
  | atom : String → SExpr
  | str  : String → SExpr
  | list : List SExpr → SExpr
  deriving Repr, BEq, Inhabited

namespace SExpr

/-! ## S-Expression Parser with UTF-8 support -/

/-- Parser state using String.Pos for UTF-8 -/
structure ParseState where
  input : String
  pos   : String.Pos
  deriving Repr

def ParseState.mk' (s : String) : ParseState := { input := s, pos := 0 }

def ParseState.atEnd (s : ParseState) : Bool := s.pos >= s.input.endPos

def ParseState.peek (s : ParseState) : Option Char :=
  if s.atEnd then none
  else some (s.input.get s.pos)

def ParseState.advance (s : ParseState) : ParseState :=
  if s.atEnd then s
  else { s with pos := s.input.next s.pos }

def ParseState.advanceN (s : ParseState) (n : Nat) : ParseState :=
  match n with
  | 0 => s
  | n + 1 => s.advance.advanceN n

/-- Skip whitespace and comments -/
partial def skipWhitespace (s : ParseState) : ParseState :=
  match s.peek with
  | some c =>
    if c.isWhitespace then skipWhitespace s.advance
    else if c == ';' then skipComment s.advance
    else s
  | none => s
where
  skipComment (s : ParseState) : ParseState :=
    match s.peek with
    | some '\n' => skipWhitespace s.advance
    | some _ => skipComment s.advance
    | none => s

/-- Parse an atom (unquoted symbol) -/
partial def parseAtom (s : ParseState) : Option (SExpr × ParseState) :=
  go "" s
where
  go (acc : String) (s : ParseState) : Option (SExpr × ParseState) :=
    match s.peek with
    | some c =>
      if c.isWhitespace || c == '(' || c == ')' || c == '"' then
        if acc.isEmpty then none
        else some (.atom acc, s)
      else
        go (acc.push c) s.advance
    | none =>
      if acc.isEmpty then none
      else some (.atom acc, s)

/-- Parse a string literal -/
partial def parseString (s : ParseState) : Option (SExpr × ParseState) :=
  match s.peek with
  | some '"' =>
    match go "" s.advance with
    | some (content, s') => some (.str content, s')
    | none => none
  | _ => none
where
  go (acc : String) (st : ParseState) : Option (String × ParseState) :=
    match st.peek with
    | some '"' => some (acc, st.advance)
    | some '\\' =>
      match st.advance.peek with
      | some c => go (acc.push c) st.advance.advance
      | none => none
    | some c => go (acc.push c) st.advance
    | none => none

/-- Parse an S-expression -/
partial def parse (s : ParseState) : Option (SExpr × ParseState) :=
  let s := skipWhitespace s
  match s.peek with
  | some '(' => parseList s.advance
  | some '"' => parseString s
  | some _ => parseAtom s
  | none => none
where
  parseList (s : ParseState) : Option (SExpr × ParseState) :=
    go [] s
  go (acc : List SExpr) (s : ParseState) : Option (SExpr × ParseState) :=
    let s := skipWhitespace s
    match s.peek with
    | some ')' => some (.list acc.reverse, s.advance)
    | some _ =>
      match parse s with
      | some (e, s') => go (e :: acc) s'
      | none => none
    | none => none

/-- Parse a complete S-expression from a string -/
def parseAll (input : String) : Option SExpr :=
  match parse (ParseState.mk' input) with
  | some (e, _) => some e
  | none => none

/-! ## S-Expression Printer -/

/-- Escape a string for printing -/
def escapeString (s : String) : String :=
  s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else acc.push c) ""

/-- Pretty-print an S-expression -/
partial def print : SExpr → String
  | .atom s => s
  | .str s => s!"\"{escapeString s}\""
  | .list es => "(" ++ " ".intercalate (es.map print) ++ ")"

instance : ToString SExpr := ⟨print⟩

/-! ## Grammar.sexpr Extraction -/

/-- Grammar production from Grammar.sexpr -/
structure GrammarProd where
  name : String
  expr : SExpr  -- The grammar expression S-expr
  deriving Repr

/-- Extract grammar productions from a (grammar ...) S-expression -/
def extractGrammar (sexpr : SExpr) : Option (List GrammarProd) :=
  match sexpr with
  | .list (.atom "grammar" :: prods) =>
    prods.filterMap extractProd
    |> some
  | _ => none
where
  extractProd : SExpr → Option GrammarProd
    | .list [.atom "prod", .str name, expr] => some { name, expr }
    | _ => none

end SExpr

end Cubical
