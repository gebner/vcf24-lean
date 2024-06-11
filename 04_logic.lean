import Mathlib.Order.Nat

#check True ∧ False ∨ (3 > 1 → 1 < 3)
#check 4 = 2+2
#check ∀ n : ℕ, n ≠ 0 → ∃ m, n = m+1

/-
  Curry-Howard: Propositions as types

  (A proposition is true if there is a value of the type.)
-/

-- Functions are proofs of implication
theorem p1 {a b : Prop} : a → b → a :=
  fun ha hb => ha

-- Functions are proofs of forall
theorem p2 : ∀ n : ℕ, n = n :=
  fun n => rfl

-- Conjunction is a product (defined as a structure!)
theorem p3 {a b : Prop} (ha : a) (hb : b) : a ∧ b :=
  { left := ha, right := hb }

-- A proof of exists is a pair of witness and proof
theorem p4 (n : ℕ) : ∃ m, n+1 ≤ m :=
  ⟨n+1, le_refl _⟩

-- Disjunction is a sum type
theorem p5 {a b : Prop} (ha : a) : a ∨ b :=
  .inl ha

/-
  Proofs are "just" expressions; pattern-matching, recursive definitions,
  etc. just work.
-/

theorem p6 {a b : Prop} : a ∨ b → b ∨ a
  | .inl ha => .inr ha
  | .inr hb => .inl hb

theorem p7 {α : Type u} (p q : α → Prop) : (∃ x, p x) → (∃ x, q x) → (∃ x y, p x ∧ q y)
  | ⟨x, hpx⟩, ⟨y, hpy⟩ => ⟨x, y, hpx, hpy⟩

theorem p8 : ∀ n : ℕ, 0 ≤ n
  | 0 => le_refl _
  | (n+1) =>
    let  h1 : n ≥ 0 := p8 n
    have h2 : n+1 ≥ n := Nat.le_succ n
    show 0 ≤ n+1 from le_trans h1 h2

/-
  Subtypes restrict types to a subset of values.
-/
def PositiveNat := { n : ℕ // n > 0 }

example : PositiveNat := ⟨10, by decide⟩

/-
  There are two different kinds of "truth values":
   - Prop: types, erased at runtime
   - Bool: inductive type with values true/false, computable
-/

#check True ∧ False ∨ True
#check true && false || true

-- Lean automatically converts ("coerces") bools into Props
-- x  is coerced into  x = true
example : (true : Prop) := rfl

-- We can convert a Prop p into a bool if it is "decidable",
-- i.e. there is a function that computes whether p is true or not
#eval (∀ x ∈ [1,2,3,4], x^2 < x + 10 : Bool)

-- Decidable is implemented as a typeclass, and you can add your own instances

-- Many definitions in Lean use decidable propositions instead of bool:
#eval if ∀ x ∈ [1,2,3,4], x^2 < x + 10 then "ok" else "ko"
#check guard <| ∀ x ∈ [1,2,3,4], x^2 < x + 10
#check List.filter (fun x => x^2 < x + 10)

example {p : Prop} : p ∨ ¬ p :=
  Classical.em p

-- Classical logic implies that all propositions are decidable.
-- If we mark `Classical.propDecidable` as a type-class instance,
-- then if-then-else works on all propositions.
attribute [local instance] Classical.propDecidable

-- However we cannot execute definitions that use `Classical.propDecidable` to
-- construct data, such definitions are then marked as "noncomputable".
noncomputable def find_zero (f : ℕ → ℕ) : ℕ :=
  if h : ∃ i, f i = 0 then Classical.choose h else 0
