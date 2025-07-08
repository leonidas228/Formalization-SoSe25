import Mathlib.Tactic

-- Let's do some basic tactics exercises.

section rw

/-
In this section, only use the `rw` tactic.
You will also need the following functions: -/
#check mul_comm
#check mul_assoc

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw[mul_comm a b]
  rw[mul_assoc]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw[mul_comm c b]
  rw[mul_comm a c]
  rw[mul_assoc b c a]


example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw[← mul_assoc a b c]
  rw[mul_comm a b]
  rw[mul_assoc b a c]


example (a b c : ℝ) : a * b * c = b * c * a := by
  rw[mul_comm a b]
  rw[mul_assoc b a c]
  rw[mul_comm a c]
  rw[← mul_assoc b c a]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw[mul_comm b c]
  rw[← mul_assoc a c b]
  rw[mul_comm a c]
  rw[mul_comm (c*a) b]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
rw[← mul_assoc a b c]
rw[mul_comm a b]
rw[mul_assoc b a c]


example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [← mul_assoc a b e]
  rw [h]
  rw [h']
  rw [mul_assoc c d f]


example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [h]
  rw [← mul_assoc a e f]

-- For this next exercise, you should also need:
#check sub_self

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  rw [sub_self]

end rw

section logic

/-
For the following exercises, use the tactics:
- `intro`
- `exact`
- `constructor`
- `left`
- `right`
- `apply`
- `obtain`
- `rcases`
- `rw`
-/

example (P Q R S : Prop) (h : P → R) (h' : Q → S) : P ∧ Q → R ∧ S := by
  intro n
  constructor
  . have p := h n.1
    exact p
  . have q := h' n.2
    exact q


example (α : Type) (P Q : α → Prop) : (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro h
  obtain ⟨x, hP, hQ⟩ := h
  use x

-- For the next exercise you also need the function
#check le_trans

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀ h₁

-- For the next exercise, you can also use `ring`.
-- You will also need the following:
#check add_zero

example (a b : ℝ) : a = b ↔ b - a = 0 := by
  constructor
  . intro h
    rw [← h]
    ring
  . intro h
    rw [← add_zero a]
    rw [← h]
    ring


example (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
 constructor
 . intro h
   obtain ⟨hP, hQR⟩ := h
   rcases hQR with sQ | sR
   . left
     constructor
     . exact hP
     . exact sQ
   . right
     constructor
     . exact hP
     . exact sR
 . intro h
   constructor
   . rcases h with hPQ | hPR
     . exact hPQ.1
     . exact hPR.1
   . rcases h with hPQ | hPR
     left
     . exact hPQ.2
     right
     . exact hPR.2










example (α : Type) (P Q : α → Prop) : (∀ x, P x ∧ Q x) ↔ ((∀ x, Q x) ∧ (∀ x, P x)) := by
 constructor
 . intro h
   constructor
   . intro x
     have hx := h x
     obtain ⟨hP, hQ⟩ := hx
     exact hQ
   . intro x
     have hx := h x
     obtain ⟨hP, hQ⟩ := hx
     exact hP
 . intro h
   intro x
   obtain ⟨hQ, hP⟩ := h
   have hQx := hQ x
   have hPx := hP x
   constructor
   . exact hPx
   . exact hQx


end logic
