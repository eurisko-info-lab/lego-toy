/-
  Lego: A Minimal Language for Building Languages

  Core principle: Everything is a BiReducer (bidirectional transformation).

  - Grammar:  TokenStream ⇌ Term  (representation ⇌ structure)
  - Rules:    Term ⇌ Term         (structure ⇌ structure)
  - Language: Composition of Pieces via pushout

  The 5 Pieces:
  1. Vocab    - Reserved words
  2. Grammar  - Syntax specification
  3. Rules    - Rewrite rules (with free interpreter)
  4. Types    - Type annotations
  5. Tests    - Verification

  The 3 Operations:
  1. Pushout  (⊕) - Merge languages
  2. Sequence (⬝) - Sequential composition
  3. Star     (*) - Kleene iteration
-/

import Lego.Algebra
import Lego.Attr
import Lego.AttrEval
import Lego.Interp
import Lego.Bootstrap
import Lego.Loader
import Lego.Validation
import Lego.RedValidation
import Lego.Runtime
import Lego.LanguageRegistry

-- Re-export everything for convenient access
