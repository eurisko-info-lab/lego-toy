/-
  CodeGen.lean: Fragment-based code rendering

  Provides:
  - Frag: Abstract representation of output fragments
  - render: Frag → String with indentation tracking

  The grammar interpreter (Interp.lean) uses these primitives
  when processing @nl, @indent, @dedent layout annotations.
  Language-specific syntax (keywords, escaping, etc.) comes
  from the target grammar (.lego file), not from here.
-/

namespace CodeGen

/-- Output fragment - abstract representation of generated code -/
inductive Frag where
  | Raw     : String → Frag                     -- literal string
  | Ident   : String → Frag                     -- identifier
  | Indent  : Frag → Frag                       -- indented block
  | FSeq    : List Frag → Frag                  -- sequence of fragments
  | Line    : Frag → Frag                       -- fragment followed by newline
  | Lines   : List Frag → Frag                  -- multiple lines
  | Sep     : String → List Frag → Frag         -- separated list (sep, items)
  | FEmpty  : Frag                              -- empty fragment
  deriving Repr, BEq, Inhabited

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

end CodeGen
