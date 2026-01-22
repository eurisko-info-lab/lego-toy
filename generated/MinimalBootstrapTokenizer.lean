/-
  Generated Tokenizer from MinimalBootstrap.lego

  Purely grammar-driven lexing. All token patterns are defined in the
  Token piece grammar and interpreted by tokenizeWithGrammar.

  DO NOT EDIT - regenerate with:
    lake exe tolean --tokenizer test/MinimalBootstrap.lego -o generated/MinimalBootstrapTokenizer.lean
-/

import Lego.Algebra
import Lego.Interp

namespace Lego.Generated.MinimalBootstrap

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
    ("Token.alpha", ((ref "Token.lower").alt ((ref "Token.upper").alt (lit "_")))),
    ("Token.symch", ((lit "(").alt ((lit ")").alt ((lit "[").alt ((lit "]").alt ((lit "{").alt ((lit "}").alt ((lit "<").alt ((lit ">").alt ((lit ":").alt ((lit ";").alt ((lit ",").alt ((lit ".").alt ((lit "|").alt ((lit "!").alt ((lit "?").alt ((lit "@").alt ((lit "#").alt ((lit "$").alt ((lit "%").alt ((lit "^").alt ((lit "&").alt ((lit "*").alt ((lit "+").alt ((lit "-").alt ((lit "=").alt ((lit "~").alt ((lit "/").alt ((lit "\\").alt ((lit "`").alt ((lit "'").alt (lit "\"")))))))))))))))))))))))))))))))),
    ("Token.ident", ((ref "Token.alpha").seq (((ref "Token.alpha").alt ((ref "Token.digit").alt ((lit "-").alt ((lit "/").alt (lit "'"))))).star))),
    ("Token.number", ((ref "Token.digit").seq ((ref "Token.digit").star))),
    ("Token.string", (((lit "\"").seq ((ref "Token.printable").star)).seq (lit "\""))),
    ("Token.char", (((lit "'").seq (ref "Token.printable")).seq (lit "'"))),
    ("Token.printable", ((ref "Token.alpha").alt ((ref "Token.digit").alt ((ref "Token.symch").alt (lit " "))))),
    ("Token.ws", ((lit " ").alt ((lit "\t").alt ((lit "\n").alt (lit ""))))),
    ("Token.comment", (((lit "-").seq (lit "-")).seq ((ref "Token.nonnl").star))),
    ("Token.nonnl", ((ref "Token.alpha").alt ((ref "Token.digit").alt ((ref "Token.symch").alt ((lit " ").alt (lit "\t")))))),
    ("Token.op3", (((lit ":").seq (lit ":")).seq (lit "="))),
    ("Token.op2", ((((empty.seq (lit "~")).seq (lit "~")).seq (lit ">")).alt (((empty.seq (lit ":")).seq (lit "=")).alt (((empty.seq (lit "~")).seq (lit ">")).alt ((empty.seq (lit "-")).seq (lit ">")))))),
    ("Token.special", (((lit "<").seq ((ref "Token.alpha").seq ((ref "Token.alpha").star))).seq (lit ">"))),
    ("Token.sym", (ref "Token.symch"))
  ]
  rules := []
}

/-- Token productions -/
def tokenProductions : Productions := tokenPiece.grammar

/-- Main token productions in priority order -/
def mainTokenProds : List String := ["Token.comment", "Token.ws", "Token.op3", "Token.op2", "Token.string", "Token.char", "Token.special", "Token.ident", "Token.number", "Token.sym"]

/-! ## Tokenizer -/

/-- Tokenize using grammar-driven lexing -/
def tokenize (s : String) : TokenStream :=
  tokenizeWithGrammar defaultFuel tokenProductions mainTokenProds s

end Lego.Generated.MinimalBootstrap
