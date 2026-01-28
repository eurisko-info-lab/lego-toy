# RedTT for Working Developers

## A Practical Introduction to Proof-Assisted Programming

**Target audience**: Software developers who want bug-free code but have never touched type theory.

**What you'll learn**: How to write programs that are *mathematically guaranteed* to be correct, and why that matters for your day job.

---

## Part 1: Why Should I Care?

### The Problem You Already Have

You write tests. Lots of them. Unit tests, integration tests, property-based tests. And still, bugs slip through.

```javascript
// You wrote this
function divide(a, b) {
  return a / b;
}

// You tested it
test("divide works", () => {
  expect(divide(10, 2)).toBe(5);
  expect(divide(9, 3)).toBe(3);
});

// Tests pass! Ship it! 🚀
// ... then production crashes with divide(x, 0)
```

Tests check *some* inputs. Proofs check *all* inputs.

### What RedTT Offers

RedTT is a proof assistant that lets you:
1. **State exactly what your code should do** (specification)
2. **Write the code** (implementation)  
3. **Prove they match** (verification)

The compiler then *mathematically guarantees* your code meets the spec. Not "probably works" — **definitely works**.

---

## Part 2: Your First RedTT Program

### Installation

```bash
# Clone and build
git clone https://github.com/RedPRL/redtt
cd redtt
opam install --deps-only .
dune build
```

### Hello, Proofs!

Create a file `first.red`:

```
-- This is a comment

-- Define the boolean type
data bool where
| tt   -- true
| ff   -- false

-- A function that negates a boolean
def not : bool → bool =
  λ b →
    elim b [
    | tt → ff
    | ff → tt
    ]

-- PROVE that applying not twice gives back the original
def not-not : (b : bool) → path bool (not (not b)) b =
  λ b →
    elim b [
    | tt → refl
    | ff → refl
    ]
```

**What just happened?**

1. `data bool` — We defined booleans with two values: `tt` (true) and `ff` (false)
2. `def not` — A function that flips booleans
3. `def not-not` — A **proof** that `not(not(b)) = b` for ALL booleans

The `→` means "for all". So `(b : bool) → ...` means "for every boolean b".

Run it:
```bash
./redtt first.red
```

If it compiles, **your proof is correct**. The compiler checked every case.

---

## Part 3: Types Are Specifications

### Think of Types as Contracts

In everyday programming:
```typescript
function sort(arr: number[]): number[] { ... }
```

The type says "takes numbers, returns numbers". But does it actually sort? Who knows!

In RedTT, types can say *exactly* what the function does:

```
-- A type that says "this list is sorted"
def is-sorted : list nat → type = ...

-- A function that MUST return a sorted list
def sort : (xs : list nat) → (ys : list nat) × is-sorted ys = ...
```

The return type `(ys : list nat) × is-sorted ys` means:
- Returns a list `ys`
- **AND** a proof that `ys` is sorted

If you try to return an unsorted list, **it won't compile**.

---

## Part 4: Practical Example — Safe Division

Let's solve our division-by-zero problem properly.

```
-- Natural numbers: 0, 1, 2, 3, ...
data nat where
| zero
| suc (n : nat)  -- successor: suc zero = 1, suc (suc zero) = 2

-- "n is not zero" as a type
def nonzero : nat → type =
  λ n →
    elim n [
    | zero → void      -- zero IS zero, so this is impossible (void)
    | suc _ → unit     -- any suc is nonzero, trivially true (unit)
    ]

-- Safe division: you MUST provide proof that divisor isn't zero
def safe-div : nat → (d : nat) → nonzero d → nat = ...
```

**How you use it:**

```
-- This works: 10 / 2
-- The proof 'tt' witnesses that (suc (suc zero)) is nonzero
def ten-div-two : nat = safe-div 10 2 tt

-- This WON'T COMPILE: 10 / 0
-- There's no proof that zero is nonzero!
def crash : nat = safe-div 10 0 ???  -- no valid proof exists!
```

The compiler **refuses to build** code that could divide by zero. Not at runtime — at compile time.

---

## Part 5: Equality and Paths

### The Big Idea

In RedTT, equality is called a "path". Think of it geometrically:

```
    a ════════════ b
         path
```

A path from `a` to `b` is proof that `a = b`.

### Why "Path" Instead of "Equals"?

Because paths can be:
- **Combined**: If `a = b` and `b = c`, then `a = c`
- **Reversed**: If `a = b`, then `b = a`  
- **Transformed**: If `a = b` and `f` is a function, then `f(a) = f(b)`

```
-- Reflexivity: everything equals itself
def refl : (a : A) → path A a a

-- Symmetry: equality goes both ways
def symm : path A a b → path A b a

-- Transitivity: chain equalities together
def trans : path A a b → path A b c → path A a c

-- Congruence: functions preserve equality
def ap : (f : A → B) → path A a a' → path B (f a) (f a')
```

### Real Example: Proving Commutativity

```
-- Addition (you'd define this with recursion)
def add : nat → nat → nat = ...

-- PROVE that addition is commutative: a + b = b + a
def add-comm : (a b : nat) → path nat (add a b) (add b a) =
  λ a b →
    -- proof by induction on a
    elim a [
    | zero → ...      -- base case: 0 + b = b + 0
    | suc a' → ...    -- inductive case: (1+a') + b = b + (1+a')
    ]
```

If this compiles, you've **mathematically proven** that your `add` function is commutative. For ALL natural numbers. Forever.

---

## Part 6: The Killer Feature — Refactoring with Confidence

### Scenario: You Need to Optimize

You have a slow `reverse` function:

```
def reverse-slow : list A → list A = ...
```

You write a faster version:

```
def reverse-fast : list A → list A = ...
```

**Traditional approach**: Run tests, hope you didn't break anything.

**RedTT approach**: Prove they're equivalent!

```
def reverse-equiv : (xs : list A) → path (list A) (reverse-slow xs) (reverse-fast xs) =
  λ xs → ...
```

If this compiles:
- The functions produce identical results for ALL inputs
- You can swap them anywhere with **zero risk**
- No tests needed — it's mathematically proven

---

## Part 7: Cubical Type Theory — What Makes RedTT Special

### The "Cubical" Part

RedTT uses "cubical type theory", which gives you:

1. **Univalence**: Equivalent types can be treated as equal
2. **Higher Inductive Types**: Define types with custom equality

### Practical Benefit: Quotient Types

Say you're modeling rational numbers:

```
-- A fraction is a pair (numerator, denominator)
data frac where
| mkfrac (num : int) (den : int)

-- Problem: 1/2 and 2/4 are different values but equal rationals!
```

In normal programming, you'd normalize fractions everywhere. Bug-prone!

In RedTT, use a **quotient type**:

```
-- Rational numbers: fractions where equivalent fracs are EQUAL
data rat where
| mkrat (f : frac)
| quot (a b : frac) (eq : equiv a b) (i : dim)
    -- ^ this "glues" equivalent fractions together!
```

Now `1/2` and `2/4` are **literally the same value**. Functions on `rat` automatically respect this — the type system enforces it.

---

## Part 8: How to Think in RedTT

### Step 1: Specify Before You Implement

```
-- Write the TYPE first — it's your spec
def sort : (xs : list nat) → (ys : list nat) × (is-sorted ys) × (same-elements xs ys)

-- Then fill in the implementation
def sort = λ xs → ...
```

### Step 2: Prove Incrementally

Don't try to prove everything at once. Use `?` for holes:

```
def my-proof : ... =
  ?  -- RedTT will tell you what type goes here
```

### Step 3: Follow the Types

The type tells you what to do:

- `A × B` — need to provide both an A and a B
- `A → B` — introduce a lambda: `λ a → ...`
- `path A x y` — show how to continuously transform x into y
- `(x : A) × B x` — provide an x and a proof of B for that x

---

## Part 9: Common Patterns

### Pattern: Dependent Pairs (Σ types)

"A value together with a property about it"

```
-- A number together with proof it's positive
def positive-nat : type = (n : nat) × is-positive n

-- A sorted list
def sorted-list : type = (xs : list nat) × is-sorted xs
```

### Pattern: Induction

"Prove something for all cases"

```
def all-nats-have-property : (n : nat) → P n =
  λ n →
    elim n [
    | zero → ... -- prove P holds for 0
    | suc n' → 
        -- you get: proof that P holds for n'
        -- you must: prove P holds for n'+1
        ...
    ]
```

### Pattern: Function Extensionality

"Two functions are equal if they give equal results for all inputs"

```
def funext : ((x : A) → path B (f x) (g x)) → path (A → B) f g
```

---

## Part 10: When to Use Proof Assistants

### Good Use Cases

✅ **Financial calculations** — prove no rounding errors compound  
✅ **Cryptographic protocols** — prove security properties  
✅ **Parsers** — prove they accept exactly the right language  
✅ **Data structures** — prove invariants are maintained  
✅ **Compilers** — prove transformations preserve meaning  
✅ **Concurrent code** — prove absence of race conditions  

### Not Worth It (Yet)

❌ Throwaway scripts  
❌ Rapid prototyping  
❌ UI code (specifications too fuzzy)  
❌ When requirements change daily  

---

## Part 11: RedTT Cheat Sheet

### Syntax Quick Reference

```
-- Type definitions
data MyType where
| constructor1
| constructor2 (arg : SomeType)

-- Function definitions  
def myFunc : InputType → OutputType =
  λ input → ...

-- Pattern matching
elim x [
| case1 → result1
| case2 arg → result2
]

-- Let bindings
let x : T = value in body

-- Lambda (anonymous function)
λ x → body
λ (x : Type) → body

-- Paths (equality proofs)
path A x y           -- type: "x equals y in type A"
refl                 -- proof: x = x
symm p               -- if p : x = y, then symm p : y = x
trans p q            -- if p : x = y and q : y = z, then trans p q : x = z

-- Dimension variables (for paths)
λ i → ...            -- i ranges from 0 to 1
```

### Reading Type Signatures

```
(x : A) → B          -- "for all x of type A, we get B"
A → B                -- "function from A to B" (same when B doesn't mention x)
A × B                -- "pair of A and B"
(x : A) × B x        -- "pair where second component depends on first"
path A x y           -- "proof that x equals y"
```

---

## Part 12: Next Steps

### Resources

1. **RedTT Repository**: https://github.com/RedPRL/redtt
2. **CoolTT** (newer version): https://github.com/RedPRL/cooltt
3. **Cubical Agda** (similar ideas, larger community): https://agda.readthedocs.io/en/v2.6.2/language/cubical.html

### Practice Problems

1. **Prove** that list append is associative: `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)`
2. **Implement** a safe `head` that requires proof the list is non-empty
3. **Prove** that `map f (map g xs) = map (f ∘ g) xs`
4. **Define** integers as pairs of naturals quotiented by equivalence

### Philosophy

> "Program testing can be used to show the presence of bugs, but never to show their absence." — Edsger Dijkstra

RedTT lets you show their absence.

---

## Appendix: Full Working Examples

### Example 1: Vectors (Length-Indexed Lists)

```
-- A list that knows its length at the type level
data vec (A : type) : nat → type where
| nil : vec A zero
| cons (n : nat) (head : A) (tail : vec A n) : vec A (suc n)

-- Safe head: only works on non-empty vectors
def head : (n : nat) → vec A (suc n) → A =
  λ n v →
    elim v [
    | cons _ h _ → h
    ]
-- Note: no nil case needed! The type (suc n) rules it out.

-- Safe tail
def tail : (n : nat) → vec A (suc n) → vec A n =
  λ n v →
    elim v [
    | cons _ _ t → t
    ]
```

### Example 2: Verified Insertion Sort

```
-- Less-than-or-equal as a type
data leq : nat → nat → type where
| leq-zero (n : nat) : leq zero n
| leq-suc (m n : nat) (p : leq m n) : leq (suc m) (suc n)

-- A list where each element ≤ the next
data sorted-list : type where
| snil : sorted-list
| sone (x : nat) : sorted-list
| scons (x y : nat) (p : leq x y) (rest : sorted-list) : sorted-list

-- Insert maintaining sortedness
def insert : nat → sorted-list → sorted-list = ...

-- Insertion sort with proof
def isort : list nat → sorted-list =
  λ xs →
    elim xs [
    | nil → snil
    | cons x xs' → insert x (isort xs')
    ]
```

---

**Remember**: The compiler is your proof checker. If it compiles, it's correct. No exceptions. No edge cases. No "works on my machine."

Welcome to the future of programming. 🎉
