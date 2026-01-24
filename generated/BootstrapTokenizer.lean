/-
  Generated Tokenizer from Bootstrap.lego

  Purely grammar-driven lexing. All token patterns are defined in the
  Token piece grammar and interpreted by tokenizeWithGrammar.

  DO NOT EDIT - regenerate with:
    lake exe tolean --tokenizer test/Bootstrap.lego -o generated/BootstrapTokenizer.lean
-/

import Lego.Algebra
import Lego.Interp

namespace Lego.Generated.Bootstrap

open GrammarExpr
open Lego

/-! ## Token Grammar -/

/-- Token piece -/
def tokenPiece : Piece := {
  name := "Token"
  level := .token
  grammar := [
    ("Token.digit", ((lit "0").alt ((lit "1").alt ((lit "2").alt ((lit "3").alt ((lit "4").alt ((lit "5").alt ((lit "6").alt ((lit "7").alt ((lit "8").alt (lit "9"))))))))))),
    ("Token.lower", ((lit "a").alt ((lit "b").alt ((lit "c").alt ((lit "d").alt ((lit "e").alt ((lit "f").alt ((lit "g").alt ((lit "h").alt ((lit "i").alt ((lit "j").alt ((lit "k").alt ((lit "l").alt ((lit "m").alt ((lit "n").alt ((lit "o").alt ((lit "p").alt ((lit "q").alt ((lit "r").alt ((lit "s").alt ((lit "t").alt ((lit "u").alt ((lit "v").alt ((lit "w").alt ((lit "x").alt ((lit "y").alt (lit "z"))))))))))))))))))))))))))),
    ("Token.upper", ((lit "A").alt ((lit "B").alt ((lit "C").alt ((lit "D").alt ((lit "E").alt ((lit "F").alt ((lit "G").alt ((lit "H").alt ((lit "I").alt ((lit "J").alt ((lit "K").alt ((lit "L").alt ((lit "M").alt ((lit "N").alt ((lit "O").alt ((lit "P").alt ((lit "Q").alt ((lit "R").alt ((lit "S").alt ((lit "T").alt ((lit "U").alt ((lit "V").alt ((lit "W").alt ((lit "X").alt ((lit "Y").alt (lit "Z"))))))))))))))))))))))))))),
    ("Token.greek", ((lit "α").alt ((lit "β").alt ((lit "γ").alt ((lit "δ").alt ((lit "ε").alt ((lit "ζ").alt ((lit "η").alt ((lit "θ").alt ((lit "ι").alt ((lit "κ").alt ((lit "λ").alt ((lit "μ").alt ((lit "ν").alt ((lit "ξ").alt ((lit "ο").alt ((lit "π").alt ((lit "ρ").alt ((lit "σ").alt ((lit "τ").alt ((lit "υ").alt ((lit "φ").alt ((lit "χ").alt ((lit "ψ").alt ((lit "ω").alt ((lit "Α").alt ((lit "Β").alt ((lit "Γ").alt ((lit "Δ").alt ((lit "Ε").alt ((lit "Ζ").alt ((lit "Η").alt ((lit "Θ").alt ((lit "Ι").alt ((lit "Κ").alt ((lit "Λ").alt ((lit "Μ").alt ((lit "Ν").alt ((lit "Ξ").alt ((lit "Ο").alt ((lit "Π").alt ((lit "Ρ").alt ((lit "Σ").alt ((lit "Τ").alt ((lit "Υ").alt ((lit "Φ").alt ((lit "Χ").alt ((lit "Ψ").alt (lit "Ω"))))))))))))))))))))))))))))))))))))))))))))))))),
    ("Token.mathbb", ((lit "𝕀").alt ((lit "𝔽").alt (lit "𝕊")))),
    ("Token.super", ((lit "¹").alt ((lit "²").alt (lit "³")))),
    ("Token.sub", ((lit "₀").alt ((lit "₁").alt ((lit "₂").alt ((lit "₃").alt ((lit "₄").alt ((lit "₅").alt ((lit "₆").alt ((lit "₇").alt ((lit "₈").alt (lit "₉"))))))))))),
    ("Token.mathrel", ((lit "≈").alt ((lit "≅").alt ((lit "≤").alt ((lit "≥").alt (lit "≡")))))),
    ("Token.mathop", ((lit "∘").alt ((lit "⊗").alt ((lit "⊙").alt ((lit "∧").alt ((lit "∨").alt ((lit "∷").alt ((lit "⋆").alt ((lit "¯").alt ((lit "⊤").alt (lit "⊥"))))))))))),
    ("Token.alpha", ((ref "Token.lower").alt ((ref "Token.upper").alt ((ref "Token.greek").alt ((ref "Token.mathbb").alt ((ref "Token.super").alt ((ref "Token.sub").alt ((ref "Token.mathrel").alt ((ref "Token.mathop").alt (lit "_")))))))))),
    ("Token.symch", ((lit "(").alt ((lit ")").alt ((lit "[").alt ((lit "]").alt ((lit "{").alt ((lit "}").alt ((lit "<").alt ((lit ">").alt ((lit ":").alt ((lit ";").alt ((lit ",").alt ((lit ".").alt ((lit "|").alt ((lit "!").alt ((lit "?").alt ((lit "@").alt ((lit "#").alt ((lit "$").alt ((lit "%").alt ((lit "^").alt ((lit "&").alt ((lit "*").alt ((lit "+").alt ((lit "-").alt ((lit "=").alt ((lit "~").alt ((lit "/").alt ((lit "\\").alt ((lit "→").alt ((lit "←").alt ((lit "↔").alt ((lit "⊕").alt ((lit "⊢").alt ((lit "×").alt ((lit "λ").alt ((lit "∂").alt ((lit "∀").alt ((lit "∃").alt ((lit "⦉").alt ((lit "⦊").alt ((lit "«").alt ((lit "»").alt ((lit "★").alt ((lit "☆").alt ((lit "`").alt ((lit "↦").alt ((lit "↾").alt ((lit "⟨").alt (lit "⟩")))))))))))))))))))))))))))))))))))))))))))))))))),
    ("Token.ident", ((ref "Token.alpha").seq (((ref "Token.alpha").alt ((ref "Token.digit").alt ((lit "-").alt ((lit "/").alt (lit "'"))))).star))),
    ("Token.hashident", (((lit "#").seq (ref "Token.alpha")).seq (((ref "Token.alpha").alt (ref "Token.digit")).star))),
    ("Token.number", ((ref "Token.digit").seq ((ref "Token.digit").star))),
    ("Token.string", (((lit "\"").seq ((ref "Token.strchar").star)).seq (lit "\""))),
    ("Token.strchar", (((empty.seq (lit "\\")).seq (ref "Token.escape")).alt (ref "Token.printable"))),
    ("Token.escape", ((lit "\"").alt ((lit "\\").alt ((lit "n").alt ((lit "t").alt ((lit "r").alt (lit "'"))))))),
    ("Token.printable", ((ref "Token.alpha").alt ((ref "Token.digit").alt ((ref "Token.symch").alt (lit " "))))),
    ("Token.char", (((lit "'").seq (ref "Token.charinner")).seq (lit "'"))),
    ("Token.charinner", (((empty.seq (lit "\\")).seq (ref "Token.escape")).alt ((ref "Token.alpha").alt ((ref "Token.digit").alt ((ref "Token.symch").alt ((lit " ").alt (lit "\""))))))),
    ("Token.ws", ((lit " ").alt ((lit "\t").alt ((lit "\n").alt (lit "
"))))),
    ("Token.comment", (((lit "-").seq (lit "-")).seq ((ref "Token.nonnl").star))),
    ("Token.nonnl", ((ref "Token.alpha").alt ((ref "Token.digit").alt ((ref "Token.symch").alt ((lit " ").alt ((lit "\t").alt ((lit "'").alt (lit "\"")))))))),
    ("Token.op3", ((((empty.seq (lit ":")).seq (lit ":")).seq (lit "=")).alt (((empty.seq (lit "=")).seq (lit "I")).seq (lit "=")))),
    ("Token.op2", ((((empty.seq (lit "~")).seq (lit "~")).seq (lit ">")).alt (((empty.seq (lit ":")).seq (lit "=")).alt (((empty.seq (lit "~")).seq (lit ">")).alt (((empty.seq (lit "-")).seq (lit ">")).alt (((empty.seq (lit "<")).seq (lit "-")).alt (((empty.seq (lit "=")).seq (lit ">")).alt ((empty.seq (lit "@")).seq (lit "@"))))))))),
    -- Layout annotation tokens for pretty-printing
    ("Token.layout", (longest [
      (((((((lit "@").seq (lit "i")).seq (lit "n")).seq (lit "d")).seq (lit "e")).seq (lit "n")).seq (lit "t")),
      (((((((lit "@").seq (lit "d")).seq (lit "e")).seq (lit "d")).seq (lit "e")).seq (lit "n")).seq (lit "t")),
      (((lit "@").seq (lit "n")).seq (lit "l")),
      (((lit "@").seq (lit "s")).seq (lit "p")),
      ((((lit "@").seq (lit "n")).seq (lit "s")).seq (lit "p"))
    ])),
    ("Token.special", (((lit "<").seq ((ref "Token.alpha").seq ((ref "Token.alpha").star))).seq (lit ">"))),
    ("Token.sym", (ref "Token.symch"))
  ]
  rules := []
}

/-- Token productions -/
def tokenProductions : Productions := tokenPiece.grammar

/-- Main token productions in priority order -/
def mainTokenProds : List String := ["Token.comment", "Token.ws", "Token.op3", "Token.op2", "Token.layout", "Token.string", "Token.char", "Token.special", "Token.hashident", "Token.ident", "Token.number", "Token.sym"]

/-! ## Tokenizer -/

/-- Tokenize using grammar-driven lexing -/
def tokenize (s : String) : TokenStream :=
  tokenizeWithGrammar defaultFuel tokenProductions mainTokenProds s

end Lego.Generated.Bootstrap
