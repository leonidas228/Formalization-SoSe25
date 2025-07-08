import Mathlib.Tactic

/-
For the following exercises, use the tactics:
1. `rfl` - to close goals that are literally equal.
2. `rw` - to rewrite terms along equalities.
3. `intro` - to introduce assumptions.
4. `exact` - to provide exact matches for goals.
5. `apply` - to apply functions to goals.
6. `have` - to introduce new assumptions.
7. `constructor` - to prove equivalences and conjunctions.
8. `obtain` - to split assumptions in conjunctions and existential quantifiers.
9. `left` - to prove disjunctions.
10. `right` - to prove disjunctions.
11. `rcases` - to split disjunctions.
12. `use` - to provide witnesses for existential quantifiers.
13. `simp` - to simplify terms.
-/

section contradiction
/- In this section we also use `by_contra`. -/

-- This first one should not require `by_contra`.
example (P : Prop) (h : P) : ¬¬P := by
  by_contra hp
  apply hp
  exact h



example (P : Prop) (h : ¬¬P) : P := by
  by_contra hp
  apply h
  exact hp

example (P : Prop) : (P → ¬P) → ¬P := by
  intro h
  by_contra hp
  have q:= h hp
  exact q hp


-- Let's prove the famous De Morgan's laws.
-- Note these two are harder than the three previous ones.
example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  . intro h
    constructor
    . by_contra hp
      apply h
      left
      exact hp
    . by_contra hq
      apply h
      right
      exact hq
  . intro h
    by_contra hpq
    rcases hpq with hp | hq
    exact h.1 hp
    exact h.2 hq






example (P Q : Prop) : ¬ (P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  . intro h
    by_contra hpq
    apply h
    constructor
    . by_contra hp
      apply hpq
      left
      exact hp
    . by_contra hq
      apply hpq
      right
      exact hq
  . intro h
    rcases h with hp | hq
    . by_contra hpq
      obtain ⟨hpp,hqq⟩ := hpq
      apply hp hpp
    . by_contra hpq
      apply hq hpq.2


end contradiction

section indexed_operations

-- For the exercises in this section you will need to use:
#check Set.mem_iUnion
#check Set.mem_inter_iff

/- You can use them directly, but it's probably easier to use:
`simp only [Set.mem_iUnion]`
`simp only [Set.mem_iInter]`
`simp only [Set.mem_inter_iff]`
-/

example {α I : Type} (A : I → Set α)  (s : Set α) : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext a
  constructor
  . rw [Set.mem_inter_iff]
    rw [Set.mem_iUnion]
    intro h
    rw [Set.mem_iUnion]
    obtain ⟨hs,i,hai⟩ := h
    use i
    constructor
    . exact hai
    . exact hs
  . rw [Set.mem_iUnion]
    rw [Set.mem_inter_iff]
    rw [Set.mem_iUnion]
    intro h
    obtain ⟨i,ha,hs⟩  := h
    constructor
    . exact hs
    . use i


example {α I : Type} (A B : I → Set α) : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext a
  constructor
  . rw [Set.mem_iInter]
    rw [Set.mem_inter_iff]
    rw [Set.mem_iInter]
    rw [Set.mem_iInter]
    intro h
    constructor
    . intro i
      have f:= h i
      exact f.1
    . intro i
      have g:= h i
      exact g.2
  . rw [Set.mem_iInter]
    rw [Set.mem_inter_iff]
    rw [Set.mem_iInter]
    rw [Set.mem_iInter]
    intro h
    obtain ⟨hA,hB⟩ := h
    intro i
    have f := hA i
    have g := hB i
    constructor
    . exact f
    . exact g

example {α I : Type} (A : I → Set α) (s : Set α) : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext a
  constructor
  . rw [Set.mem_iInter]
    intro h
    intro i
    rcases h with hs | hA
    . right
      exact hs
    . left
      have f := Set.mem_iInter.1 hA
      exact f i
  . rw [Set.mem_iInter]
    intro h





end indexed_operations

section set_theory

example (X : Type ) (a : X) : a ∈ (∅ : Set X) → False := by
  sorry


example (X : Type) (A B : Set X) (hAinB : A ⊆ B) : A ∪ B = B := by
  sorry

example (X : Type) (A B : Set X) (hab : A ∩ B = ∅) : A \ B = A := by
  sorry


example (X : Type) ( A B C : Set X): A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  sorry

example  (X : Type) ( A B C : Set X) : (A \ B) \ C = A \ (B ∪ C) := by
  sorry

example (X : Type) ( A B C : Set X) : (A \ B) \ C = A \ (B ∪ C) := by
  sorry

end set_theory

section functions_basics

/- The `Empty` type is a type with no elements.
That means if I have `x : Empty`, then `cases x` will close every goal!
Let's prove that every function out of `Empty` is injective. -/
example (X : Type) (f : Empty →  X) : Function.Injective f := by
  sorry

/- The `Unit` type is a type with one element.
That means if `x : Unit`, then `x = Unit.unit`.
We obtain that via `cases x`.
Let's use that to prove that every function out of `Unit` is injective. -/
example (X : Type) (f : Unit →  X) : Function.Injective f := by
  sorry

-- Recall that if a type `X` is inhabited, then there is a default element `default : X`.
example (X : Type) [Inhabited X] (f : X →  Unit) : Function.Surjective f := by
  sorry

example (X Y : Type) (A B : Set Y) (f : X → Y) : f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B := by
  sorry

example {X Y : Type} {f : X → Y} (A : Set X) (h : Function.Injective f) : f ⁻¹' (f '' A) ⊆ A := by
  sorry

example {X Y : Type} {f : X → Y} (B : Set Y) : f '' (f ⁻¹' B) ⊆ B := by
  sorry

example {X Y : Type} {f : X → Y} (B : Set Y) (h : Function.Surjective f) : B ⊆ f '' (f ⁻¹' B) := by
  sorry

example {X Y : Type} {A B : Set X} (f : X → Y) (h : A ⊆ B) : f '' A ⊆ f '' B := by
  sorry


example {X Y : Type} {A B : Set Y} (f : X → Y)  (h : A ⊆ B) : f ⁻¹' A ⊆ f ⁻¹' B := by
  sorry

example {X Y : Type} {A B : Set Y} (f : X → Y) : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B := by
  sorry

example {X Y : Type} {A B : Set X} (f : X → Y) : f '' (A ∩ B) ⊆ f '' A ∩ f '' B := by
  sorry

example {X Y : Type} {A B : Set X} (f : X → Y) (h : Function.Injective f) : f '' A ∩ f '' B ⊆ f '' (A ∩ B) := by
  sorry


example {X Y : Type} {A B : Set X} (f : X → Y) : f '' A \ f '' B ⊆ f '' (A \ B) := by
  sorry

example {X Y : Type} {A B : Set Y} (f : X → Y) : f ⁻¹' A \ f ⁻¹' B ⊆ f ⁻¹' (A \ B) := by
  sorry

example {X Y : Type} {A : Set X} {B : Set Y} (f : X → Y) : f '' A ∩ B = f '' (A ∩ f ⁻¹' B) := by
  sorry

example {X Y : Type} {A : Set X} {B : Set Y} (f : X → Y) : f '' (A ∩ f ⁻¹' B) ⊆ f '' A ∩ B := by
  sorry

example {X Y : Type} {A : Set X} {B : Set Y} (f : X → Y) : A ∩ f ⁻¹' B ⊆ f ⁻¹' (f '' A ∩ B) := by
  sorry

example {X Y : Type} {A : Set X} {B : Set Y} (f : X → Y) : A ∪ f ⁻¹' B ⊆ f ⁻¹' (f '' A ∪ B) := by
  sorry

end functions_basics


section squares_and_roots
/- For the next exercises we need to know some facts about
squares and square roots.-/
#check Real.sq_sqrt
#check Real.sqrt_sq
#check sq_nonneg

-- You also want to benefit from the `calc` tactic.
example : Set.InjOn Real.sqrt { x | x ≥ 0 } := by
  sorry


example : Set.InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : (Set.range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end squares_and_roots
