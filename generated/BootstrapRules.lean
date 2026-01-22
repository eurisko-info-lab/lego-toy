/-
  Bootstrap Rules and Helper Functions

  This module contains:
  1. Hand-coded helper functions (combineSeq, splitSeq, wrapNode, unwrapNode)
     used by the interpreter during parsing
  2. Generated rewrite rules from Bootstrap.lego that express the same logic

  Eventually the hand-coded functions can be replaced by applying the rules,
  but for now we keep both for bootstrapping.

  Regenerate with:
    lake exe tolean --rules test/Bootstrap.lego -o generated/BootstrapRules.lean
-/

import Lego.Algebra

namespace Lego.Generated.Bootstrap

open Lego

/-! ## Helper Functions (used by Interp.lean) -/

/-- Combine two terms into a sequence -/
def combineSeq (t1 t2 : Term) : Term :=
  match t1, t2 with
  | .con "seq" ts, .con "seq" us => .con "seq" (ts ++ us)
  | .con "seq" ts, t => .con "seq" (ts ++ [t])
  | t, .con "seq" us => .con "seq" (t :: us)
  | .con "unit" [], t => t
  | t, .con "unit" [] => t
  | t1, t2 => .con "seq" [t1, t2]

/-- Split first element from a sequence -/
def splitSeq (t : Term) : Term × Term :=
  match t with
  | .con "seq" (h :: rest) => (h, .con "seq" rest)
  | t => (t, .con "unit" [])

/-- Wrap a term with a node name -/
def wrapNode (name : String) (t : Term) : Term :=
  match t with
  | .con "seq" ts => .con name ts
  | _ => .con name [t]

/-- Unwrap a node if name matches -/
def unwrapNode (name : String) (t : Term) : Term :=
  match t with
  | .con n ts => if n == name then .con "seq" ts else t
  | _ => t


/-! ## Rewrite Rules -/

/-- Rule: combine-seq-seq -/
def rule_combine_seq_seq : Rule := {
  name := "combine-seq-seq"
  pattern := .con "combineSeq" [.con "seq" [.var "$ts1"], .con "seq" [.var "$ts2"]]
  template := .con "seq" [.con "append" [.var "$ts1", .var "$ts2"]]
}

/-- Rule: combine-seq-left -/
def rule_combine_seq_left : Rule := {
  name := "combine-seq-left"
  pattern := .con "combineSeq" [.con "seq" [.var "$ts"], .var "$t"]
  template := .con "seq" [.con "append" [.var "$ts", .con "list" [.var "$t"]]]
}

/-- Rule: combine-seq-right -/
def rule_combine_seq_right : Rule := {
  name := "combine-seq-right"
  pattern := .con "combineSeq" [.var "$t", .con "seq" [.var "$ts"]]
  template := .con "seq" [.con "cons" [.var "$t", .var "$ts"]]
}

/-- Rule: combine-seq-unit-l -/
def rule_combine_seq_unit_l : Rule := {
  name := "combine-seq-unit-l"
  pattern := .con "combineSeq" [.con "unit" [], .var "$t"]
  template := .var "$t"
}

/-- Rule: combine-seq-unit-r -/
def rule_combine_seq_unit_r : Rule := {
  name := "combine-seq-unit-r"
  pattern := .con "combineSeq" [.var "$t", .con "unit" []]
  template := .var "$t"
}

/-- Rule: combine-seq-default -/
def rule_combine_seq_default : Rule := {
  name := "combine-seq-default"
  pattern := .con "combineSeq" [.var "$t1", .var "$t2"]
  template := .con "seq" [.con "list" [.var "$t1", .var "$t2"]]
}

/-- Rule: split-seq -/
def rule_split_seq : Rule := {
  name := "split-seq"
  pattern := .con "splitSeq" [.con "seq" [.con "cons" [.var "$h", .var "$rest"]]]
  template := .con "pair" [.var "$h", .con "seq" [.var "$rest"]]
}

/-- Rule: split-single -/
def rule_split_single : Rule := {
  name := "split-single"
  pattern := .con "splitSeq" [.var "$t"]
  template := .con "pair" [.var "$t", .con "unit" []]
}

/-- Rule: wrap-seq -/
def rule_wrap_seq : Rule := {
  name := "wrap-seq"
  pattern := .con "wrapNode" [.var "$name", .con "seq" [.var "$ts"]]
  template := .con "con" [.var "$name", .var "$ts"]
}

/-- Rule: wrap-other -/
def rule_wrap_other : Rule := {
  name := "wrap-other"
  pattern := .con "wrapNode" [.var "$name", .var "$t"]
  template := .con "con" [.var "$name", .con "list" [.var "$t"]]
}

/-- Rule: unwrap-match -/
def rule_unwrap_match : Rule := {
  name := "unwrap-match"
  pattern := .con "unwrapNode" [.var "$name", .con "con" [.var "$name", .var "$ts"]]
  template := .con "seq" [.var "$ts"]
}

/-- Rule: unwrap-nomatch -/
def rule_unwrap_nomatch : Rule := {
  name := "unwrap-nomatch"
  pattern := .con "unwrapNode" [.var "$name", .var "$t"]
  template := .var "$t"
}

/-- All rules for this language -/
def allRules : List Rule := [rule_combine_seq_seq, rule_combine_seq_left, rule_combine_seq_right, rule_combine_seq_unit_l, rule_combine_seq_unit_r, rule_combine_seq_default, rule_split_seq, rule_split_single, rule_wrap_seq, rule_wrap_other, rule_unwrap_match, rule_unwrap_nomatch]

/-- Combined interpreter from all rules -/
def ruleInterp : Iso Term Term := Language.combineRules allRules

/-- Apply rules to normalize a term -/
partial def normalize (t : Term) : Term :=
  match ruleInterp.forward t with
  | some t' => normalize t'
  | none =>
    match t with
    | .con c args => .con c (args.map normalize)
    | _ => t

end Lego.Generated.Bootstrap
