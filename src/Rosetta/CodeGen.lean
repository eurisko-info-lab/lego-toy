/-
  CodeGen.lean: Lean implementation of the CodeGen AST

  This mirrors the types in CodeGen.rosetta and provides:
  - Frag: Output fragment representation
  - Rendering functions: Frag → String

  This is the "Runtime" part that the codegen2*.rosetta rules target.
-/

namespace CodeGen

/-- Output fragment - abstract representation of generated code -/
inductive Frag where
  | Raw     : String → Frag                     -- literal string
  | Ident   : String → Frag                     -- identifier (may need escaping)
  | Keyword : String → Frag                     -- language keyword
  | Op      : String → Frag                     -- operator
  | Indent  : Frag → Frag                       -- indented block
  | FSeq    : List Frag → Frag                  -- sequence of fragments
  | Line    : Frag → Frag                       -- fragment followed by newline
  | Lines   : List Frag → Frag                  -- multiple lines
  | Sep     : String → List Frag → Frag         -- separated list (sep, items)
  | FEmpty  : Frag                              -- empty fragment
  deriving Repr, BEq, Inhabited

/-- Binary operators (abstract) -/
inductive BinOp where
  | EqOp | NeqOp | LtOp | GtOp | LeOp | GeOp
  | AndOp | OrOp
  | AddOp | SubOp | MulOp | DivOp | ModOp
  | ConsOp | AppendOp
  deriving Repr, BEq

/-- Unary operators (abstract) -/
inductive UnOp where
  | NotOp | NegOp
  deriving Repr, BEq

/-- Base types (abstract) -/
inductive BaseType where
  | StringType | IntType | NatType | BoolType
  | UnitType | FloatType | CharType
  deriving Repr, BEq

/-- Generic type constructors -/
inductive GenericType where
  | ListOf   : Frag → GenericType
  | OptionOf : Frag → GenericType
  | ResultOf : Frag → Frag → GenericType
  | ArrowT   : Frag → Frag → GenericType
  | ProdT    : Frag → Frag → GenericType
  deriving Repr, BEq

/-! ## Rendering -/

/-- Render state with indentation tracking -/
structure RenderState where
  indent : Nat := 0
  output : String := ""
  deriving Repr

/-- Add text to output -/
def RenderState.emit (st : RenderState) (s : String) : RenderState :=
  { st with output := st.output ++ s }

/-- Add newline with proper indentation -/
def RenderState.newline (st : RenderState) : RenderState :=
  { st with output := st.output ++ "\n" ++ String.mk (List.replicate (st.indent * 2) ' ') }

/-- Increase indent -/
def RenderState.push (st : RenderState) : RenderState :=
  { st with indent := st.indent + 1 }

/-- Decrease indent -/
def RenderState.pop (st : RenderState) : RenderState :=
  { st with indent := if st.indent > 0 then st.indent - 1 else 0 }

/-- Render a Frag to a RenderState -/
partial def renderFrag (f : Frag) (st : RenderState) : RenderState :=
  match f with
  | .Raw s => st.emit s
  | .Ident s => st.emit s
  | .Keyword s => st.emit s
  | .Op s => st.emit s
  | .FEmpty => st
  | .FSeq frags =>
    frags.foldl (fun acc frag => renderFrag frag acc) st
  | .Line frag =>
    let st' := renderFrag frag st
    st'.newline
  | .Lines frags =>
    frags.foldl (fun acc frag => renderFrag frag acc) st
  | .Indent frag =>
    let st' := st.push
    let st'' := renderFrag frag st'
    st''.pop
  | .Sep sep frags =>
    match frags with
    | [] => st
    | [f] => renderFrag f st
    | f :: fs =>
      let st' := renderFrag f st
      fs.foldl (fun acc frag => renderFrag frag (acc.emit sep)) st'

/-- Render a Frag to String -/
def render (f : Frag) : String :=
  (renderFrag f {}).output

/-! ## Target Language Configurations -/

/-- Language-specific configuration -/
structure LangConfig where
  name : String
  keywords : List String
  escapeString : String → String
  varPrefix : String := ""              -- prefix for sanitized vars
  listStart : String                    -- e.g., "[" or "List("
  listEnd : String                      -- e.g., "]" or ")"
  listEmpty : String                    -- e.g., "[]" or "Nil"
  optionSome : String                   -- e.g., "some" or "Some" or "Just"
  optionNone : String                   -- e.g., "none" or "None" or "Nothing"
  -- Term construction syntax
  termCon : String := ".Con "           -- e.g., ".Con " or "Term::Con(" or "Con "
  termConMid : String := " "            -- e.g., " " or ", " (between name and args)
  termConEnd : String := ""             -- e.g., "" or ")"
  termLit : String := ".Lit "           -- e.g., ".Lit " or "Term::Lit("
  termLitEnd : String := ""             -- e.g., "" or ")"
  termVar : String := ".Var "           -- e.g., ".Var " or "Term::Var("
  termVarEnd : String := ""             -- e.g., "" or ")"

/-- Lean 4 configuration -/
def leanConfig : LangConfig := {
  name := "Lean"
  keywords := ["def", "let", "if", "then", "else", "match", "with", "do", "return",
               "where", "structure", "inductive", "class", "instance", "namespace",
               "open", "section", "variable", "theorem", "lemma", "example", "t"]
  escapeString := fun s => s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n"
    else acc.push c) ""
  listStart := "["
  listEnd := "]"
  listEmpty := "[]"
  optionSome := "some"
  optionNone := "none"
}

/-- Scala configuration -/
def scalaConfig : LangConfig := {
  name := "Scala"
  keywords := ["abstract", "case", "catch", "class", "def", "do", "else", "extends",
               "false", "final", "finally", "for", "forSome", "if", "implicit",
               "import", "lazy", "match", "new", "null", "object", "override",
               "package", "private", "protected", "return", "sealed", "super",
               "this", "throw", "trait", "try", "true", "type", "val", "var",
               "while", "with", "yield", "t"]
  escapeString := fun s => s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n"
    else acc.push c) ""
  listStart := "List("
  listEnd := ")"
  listEmpty := "Nil"
  optionSome := "Some"
  optionNone := "None"
  -- Scala uses Con("name", List(...))
  termCon := "Con("
  termConMid := ", "
  termConEnd := ")"
  termLit := "Lit("
  termLitEnd := ")"
  termVar := "Var("
  termVarEnd := ")"
}

/-- Haskell configuration -/
def haskellConfig : LangConfig := {
  name := "Haskell"
  keywords := ["case", "class", "data", "default", "deriving", "do", "else",
               "foreign", "if", "import", "in", "infix", "infixl", "infixr",
               "instance", "let", "module", "newtype", "of", "then", "type",
               "where", "t"]
  escapeString := fun s => s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n"
    else acc.push c) ""
  listStart := "["
  listEnd := "]"
  listEmpty := "[]"
  optionSome := "Just"
  optionNone := "Nothing"
  -- Haskell uses Con "name" [...]
  termCon := "Con "
  termConMid := " "
  termConEnd := ""
  termLit := "Lit "
  termLitEnd := ""
  termVar := "Var "
  termVarEnd := ""
}

/-- Rust configuration -/
def rustConfig : LangConfig := {
  name := "Rust"
  keywords := ["as", "break", "const", "continue", "crate", "else", "enum",
               "extern", "false", "fn", "for", "if", "impl", "in", "let",
               "loop", "match", "mod", "move", "mut", "pub", "ref", "return",
               "self", "Self", "static", "struct", "super", "trait", "true",
               "type", "unsafe", "use", "where", "while", "async", "await",
               "dyn", "t"]
  escapeString := fun s => s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n"
    else acc.push c) ""
  listStart := "vec!["
  listEnd := "]"
  listEmpty := "vec![]"
  optionSome := "Some"
  optionNone := "None"
  -- Rust uses Term::Con("name", vec![...])
  termCon := "Term::Con("
  termConMid := ".to_string(), "
  termConEnd := ")"
  termLit := "Term::Lit("
  termLitEnd := ".to_string())"
  termVar := "Term::Var("
  termVarEnd := ".to_string())"
}

/-- Sanitize a variable name for a target language -/
def sanitizeVar (cfg : LangConfig) (name : String) : String :=
  -- Handle tick marks (common in Lego patterns)
  let sanitized := name.foldl (fun acc c =>
    if c == '\'' then acc ++ "_prime"
    else acc.push c) ""
  -- Prefix if keyword conflict
  if cfg.keywords.contains sanitized then "v_" ++ sanitized
  else sanitized

end CodeGen
