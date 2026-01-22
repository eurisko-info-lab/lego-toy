/-
  Bootstrap Tokenizer

  Hand-written tokenizer for the meta-grammar.
  Eventually this can be generated from the token grammar in Bootstrap.lego.

  DO NOT EDIT - regenerate with:
    lake exe tolean --tokenizer test/Bootstrap.lego > generated/BootstrapTokenizer.lean

  Initial version: Hand-written bootstrap (copied from original Bootstrap.lean)
-/

import Lego.Algebra

namespace Lego.Generated.Bootstrap

open Lego

/-! ## Tokenizer -/

/-- Reserved keywords that should be tokenized as symbols, not identifiers.
    This prevents them from being consumed as regular identifiers in expressions. -/
def reservedKeywords : List String :=
  ["def", "data", "import", "public", "where", "let", "in", "elim"]

/-- Check if a string is a reserved keyword -/
def isReservedKeyword (s : String) : Bool :=
  reservedKeywords.contains s

/-- Check if a character is a symbol character (ASCII) -/
def isSymChar (c : Char) : Bool :=
  c ∈ ['(', ')', '[', ']', '{', '}', ':', '=', '|', '*', '+', '?', '~', '>', '<', '$', '.', ',', ';', '^']

/-- Check if a character is a Unicode symbol -/
def isUnicodeSymChar (c : Char) : Bool :=
  c ∈ ['→', '←', '×', '∂', '∨', '∧', '∀', '∃', '▸', '▹', '⊢', '⦉', '⦊']

/-- Check if a character is a Unicode letter (Greek, etc.) that can start identifiers -/
def isUnicodeLetter (c : Char) : Bool :=
  c ∈ ['λ', 'Σ', 'Π', 'α', 'β', 'γ', 'δ', 'φ', 'ψ', 'τ', 'σ', 'ρ', '𝕀', 'ε', 'μ', 'ω', 'π']

/-- Check if a character is an operator character that can be multi-char -/
def isOpChar (c : Char) : Bool :=
  c ∈ [':', '=', '~', '>', '<', '-']

/-- Remove comments from a line -/
def removeLineComment (s : String) : String :=
  match s.splitOn "--" with
  | [] => ""
  | h :: _ => h

/-- Tokenize a string into tokens (proper lexer).
    Skips comments and newlines by default. -/
partial def tokenize (s : String) : TokenStream :=
  -- Remove comments and tokenize each line, then concatenate
  let lines := s.splitOn "\n" |>.map removeLineComment |>.map String.trim |>.filter (· ≠ "")
  lines.foldl (fun acc line => acc ++ tokenizeLine line.toList []) []
where
  tokenizeLine (chars : List Char) (acc : List Token) : TokenStream :=
    match chars with
    | [] => acc.reverse
    | c :: rest =>
      if c.isWhitespace then
        tokenizeLine rest acc
      -- String literal (double quotes)
      else if c == '"' then
        let (str, rest') := takeString rest ""
        tokenizeLine rest' (Token.lit s!"\"{str}\"" :: acc)
      -- Character literal (single quotes) - for token grammars
      else if c == '\'' then
        let (chr, rest') := takeChar rest
        tokenizeLine rest' (Token.lit s!"'{chr}'" :: acc)
      -- Multi-char operators: ::= ~> ~~> :=
      else if c == ':' && rest.head? == some ':' && rest.tail.head? == some '=' then
        tokenizeLine rest.tail.tail (Token.sym "::=" :: acc)
      else if c == ':' && rest.head? == some '=' then
        tokenizeLine rest.tail (Token.sym ":=" :: acc)
      else if c == '~' && rest.head? == some '~' && rest.tail.head? == some '>' then
        tokenizeLine rest.tail.tail (Token.sym "~~>" :: acc)
      else if c == '~' && rest.head? == some '>' then
        tokenizeLine rest.tail (Token.sym "~>" :: acc)
      -- Special syntax: <ident> as single token
      else if c == '<' then
        let (special, rest') := takeSpecial rest ""
        tokenizeLine rest' (Token.sym s!"<{special}>" :: acc)
      -- Single-char symbols (ASCII)
      else if isSymChar c && c != '<' then
        tokenizeLine rest (Token.sym (String.singleton c) :: acc)
      -- Unicode symbols (single char)
      else if isUnicodeSymChar c then
        tokenizeLine rest (Token.sym (String.singleton c) :: acc)
      -- Identifier or keyword (ASCII or Unicode letter)
      else if c.isAlpha || c == '_' || isUnicodeLetter c then
        let (ident, rest') := takeIdent chars ""
        -- Reserved keywords become symbols, not identifiers
        let tok := if isReservedKeyword ident then Token.sym ident else Token.ident ident
        tokenizeLine rest' (tok :: acc)
      -- Number
      else if c.isDigit then
        let (num, rest') := takeNumber chars ""
        tokenizeLine rest' (Token.number num :: acc)
      else
        -- Skip unknown character
        tokenizeLine rest acc

  takeChar (chars : List Char) : String × List Char :=
    match chars with
    | [] => ("", [])
    | '\\' :: c :: '\'' :: rest => (String.mk ['\\', c], rest)  -- escape sequence
    | c :: '\'' :: rest => (String.singleton c, rest)
    | _ => ("", chars)  -- malformed

  takeString (chars : List Char) (acc : String) : String × List Char :=
    match chars with
    | [] => (acc, [])
    | '"' :: rest => (acc, rest)
    | '\\' :: c :: rest => takeString rest (acc.push '\\' |>.push c)
    | c :: rest => takeString rest (acc.push c)

  takeIdent (chars : List Char) (acc : String) : String × List Char :=
    match chars with
    | [] => (acc, [])
    | c :: rest =>
      -- Allow alphanumeric, _, /, ', - in identifiers for redtt compatibility
      if c.isAlpha || c.isDigit || c == '_' || c == '/' || c == '\'' || c == '-' || isUnicodeLetter c then
        takeIdent rest (acc.push c)
      -- Special: → followed by letter is part of identifier (e.g., binnat→nat)
      else if c == '→' then
        match rest with
        | c' :: _ =>
          if c'.isAlpha || c' == '_' || isUnicodeLetter c' then
            takeIdent rest (acc.push c)
          else
            (acc, chars)
        | [] => (acc, chars)
      -- Special: + or * followed by letter or digit is part of identifier (e.g., m+n, n+0)
      -- This is for redtt where IH variables can have operators in names like n+0
      else if (c == '+' || c == '*') && !acc.isEmpty then
        match rest with
        | c' :: _ =>
          if c'.isAlpha || c'.isDigit || c' == '_' || isUnicodeLetter c' then
            takeIdent rest (acc.push c)
          else
            (acc, chars)
        | [] => (acc, chars)
      else
        (acc, chars)

  takeNumber (chars : List Char) (acc : String) : String × List Char :=
    match chars with
    | [] => (acc, [])
    | c :: rest =>
      if c.isDigit then
        takeNumber rest (acc.push c)
      else
        (acc, chars)

  takeSpecial (chars : List Char) (acc : String) : String × List Char :=
    match chars with
    | [] => (acc, [])
    | '>' :: rest => (acc, rest)
    | c :: rest =>
      if c.isAlpha || c.isDigit || c == '_' then
        takeSpecial rest (acc.push c)
      else
        (acc, chars)  -- malformed, but recover

end Lego.Generated.Bootstrap
