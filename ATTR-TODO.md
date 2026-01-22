# Attribute Grammar Implementation

**Status**: Phase 11 Complete ✅ (Scope Handling for Binders)

## Mathematical Foundation

Attribute Grammars are catamorphisms + paramorphisms over parse trees:

| Attribute Type | Algebraic Morphism | Direction |
|----------------|-------------------|-----------|
| **Synthesized** | Catamorphism (fold) | Bottom-up: `Fix F → A` |
| **Inherited** | Paramorphism | Top-down: carries context |
| **Both** | Hylomorphism | Anamorphism ∘ Catamorphism |

## Implementation Status

### Phase 1: Core Data Types ✅
- [x] `AttrFlow` enum: Syn | Inh | SynInh
- [x] `AttrRef` structure: attribute path + name
- [x] `AttrRule` structure: production + target + expression
- [x] `AttrDef` structure: name + flow + type + rules
- [x] `AttrEnv` structure: environment for computed attributes
- [x] `AttrLanguage` structure: Language + attributes

### Phase 2: Catamorphism Evaluation ✅
- [x] `evalSyn`: Synthesized attribute via catamorphism
- [x] `evalAttrExpr`: Expression evaluation in environment
- [x] `findRule`: Rule lookup by production

### Phase 3: Paramorphism Evaluation ✅
- [x] `evalInh`: Inherited attribute via paramorphism
- [x] `evalAttrs`: Combined two-pass evaluation

### Phase 4: Generic Morphisms ✅
- [x] `cataT`: Generic catamorphism over Term
- [x] `paraT`: Generic paramorphism over Term
- [x] `mapWithIndex`: Helper for indexed mapping

### Phase 5: Pushout Compatibility ✅
- [x] `AttrLanguage.pushout`: Coproduct of attribute algebras

### Phase 6: Grammar Syntax ✅
- [x] `attrs Name` section groups declarations and rules
- [x] `syn name : Type ;` declarations
- [x] `inh name : Type ;` declarations
- [x] `prod.attr = expr ;` rule equations
- [x] Multi-part paths: `prod.child.attr = expr ;`
- [x] Bootstrap grammar regenerated (33 productions)
- [x] Loader extraction: `extractAttrDefs`, `extractAttrRules`, `extractAttributes`
- [x] Tests: 89/89 passing (including 733/733 redtt)

### Phase 7: Integration with Redtt ✅
- [x] RedttElab.lego: type-checking attribute grammar
- [x] TypeCheck attrs: ctx (inh), expected (inh), type (syn), elab (syn)
- [x] CubicalCheck attrs: dimctx (inh), isCofib (syn) for cubical operations
- [x] Bidirectional attrs: mode (inh), ok (syn) for check/infer switching
- [x] 8 attribute definitions, 40 attribute rules
- [x] All tests passing: 89/89 (733/733 redtt)

### Phase 8: Attribute Evaluation Runtime ✅
- [x] `SourceLoc`: File, line, column, span tracking for error locations
- [x] `Context`: Typing context with name/type/value bindings
- [x] `DimContext`: Dimension context for cubical operations
- [x] `EvalEnv`: Combined environment (attrs + ctx + dimCtx + errors + loc)
- [x] `evalSynWithErrors`: Synthesized evaluation with error collection
- [x] `evalInhWithErrors`: Inherited evaluation with error collection
- [x] `evalAllAttrs`: Two-pass evaluation (inherited → synthesized)
- [x] `typecheck`/`elaborateTerm`: High-level API functions

### Phase 9: Error Reporting ✅
- [x] `Severity`: Error levels (error, warning, info)
- [x] `TypeError`: Structured errors with expected/actual/context
- [x] `EvalResult`: Result monad with error accumulation
- [x] `formatErrors`: Pretty-print error list with source locations
- [x] `countBySeverity`: Error statistics by severity level
- [x] `errorSummary`: Summary string with counts
- [x] All tests passing: 114/114 (including 733/733 redtt)

### Phase 10: Full Integration Test ✅
- [x] `runRedttAttrEvalTests`: test attribute evaluation on redtt-style terms
- [x] `testContext`: pre-populated typing context with common bindings
- [x] Tests for all major constructs: var, lit, lam, app, pi, refl, path, coe, hcom
- [x] Validates `evalAllAttrs` produces expected synthesized attributes
- [x] All 124 tests pass (113 fast + 11 redtt attr eval + 733/733 parsing)

### Phase 11: Scope Handling for Binders ✅
- [x] `binderProductions`: List of (prod, binderIdx, typeIdx, bodyIdx)
      - lam, Pi, Sigma: (0, 1, 2) - binder name, type, body
      - let: (0, 1, 3) - name, type, value, body
- [x] `getBinderInfo`: Lookup binder metadata by production name
- [x] `extractName`: Extract variable name from Term.var or Term.lit
- [x] `isBindingPosition`: Skip variable lookup for binder names
- [x] Context extension: Extend ctx with binder when evaluating body
- [x] Tests: lam_id (λ w : Type . w), lam_nested, pi_dep
- [x] All 127 tests pass

## Completed ✅

All 11 phases complete! The attribute grammar system is fully operational:
- Core types and evaluation
- Grammar syntax parsing
- Redtt integration
- Error reporting with source locations
- Full integration tests
- **Proper scope handling for binders**

## Next Steps

### Future Work (Optional)
- [ ] Production-ready type inference rules in AttrEval
- [ ] let bindings with values (extend context with value as well as type)
- [ ] Performance optimization for large files
- [ ] Integration with CubicalTypecheck.red

## Usage Example

```lean
-- Define a "depth" synthesized attribute
let depthAttr : AttrDef := {
  name := "depth"
  flow := .syn
  type := some (Term.var "Nat")
  rules := [
    { prod := "var", target := [], expr := Term.lit "0" },
    { prod := "lit", target := [], expr := Term.lit "0" },
    { prod := "lam", target := [], expr := Term.con "succ" [Term.var "$child1.depth"] }
  ]
}

-- Evaluate on a term
let term := Term.con "lam" [Term.var "x", Term.var "x"]
let env := evalSyn depthAttr term
```

## Key Files

- `src/Lego/Attr.lean`: Core attribute grammar implementation (AttrFlow, AttrRef, etc.)
- `src/Lego/AttrEval.lean`: Attribute evaluation runtime with error reporting
- `test/RedttElab.lego`: Redtt type-checking attribute grammar
- `Test.lean`: Attribute grammar tests (25+ tests)

## Algebraic Laws

The pushout of attributed languages satisfies:
```
(L₁, A₁) ⊔ (L₂, A₂) = (L₁ ⊔ L₂, A₁ ⋈ A₂)
```

Where `A₁ ⋈ A₂` is the coproduct of attribute algebras:
- Productions from L₁ use A₁ rules
- Productions from L₂ use A₂ rules
- Shared productions need resolution (priority or merge)
