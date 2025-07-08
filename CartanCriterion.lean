
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Submodule
-- import Mathlib.Algebra.Lie.Weights
-- set_option trace.Meta.Tactic.simp true
set_option diagnostics true


namespace LieAlgebra

open LieModule


variable {K L : Type*} [Field K] [CharZero K]
variable [LieRing L] [LieAlgebra K L]


/-- Die „Killing‐Orthogonale“ zur gesamten Algebra. -/
def killingRad (K L :Type*) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]: LieIdeal K L where
  carrier :=
    { s | ∀ t : L, (LieModule.traceForm K L L) s t = 0 }
  zero_mem' := by
    intro t
    simp
  add_mem' := by
    intro x y hx hy t
    simp [hx t, hy t]                       -- Linearität der Form
  smul_mem' := by
    intro k x hx t
    simp [hx t]                             -- K‑Linearität in jedem Argument
  lie_mem := by
    -- Invarianz der Trace‑Form zeigt die Schließung unter Lie‑Klammer
    intro x y hy t
    -- `traceForm_invariant` ist schon in Mathlib:
    --have h : traceForm K L L ⁅x, y⁆ t = traceForm K L L y ⁅x, t⁆ :=
  --traceForm_apply_lie_apply K L L x y t     -- B(⁅x,y⁆,t)=B(y,⁅x,t⁆)
    have h := traceForm_apply_lie_apply K L L x y t
    rw [traceForm_comm K L L x ⁅y, t⁆] at h
    have h2 := h
    rw [traceForm_lieInvariant K L L] at h2
    rw [← h2] at h
    rw [hy] at h
    -- Setze jetzt y ∈ S ⇒ rechts 0, also links 0
    simp [h]



instance {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [FiniteDimensional K L] [HasTrivialRadical K L] :
    IsKilling K L := by
    constructor
    . ext x
      constructor
      . intro h
        unfold LieIdeal.killingCompl at h
        rw [← HasTrivialRadical.radical_eq_bot]
        unfold killingForm at h
        simp [InvariantForm.mem_orthogonal] at h
        let S := killingRad K L
        let xinS : x∈ S := by {
          intro s
          rw [traceForm_comm]
          apply h
        }

        let carr : S ≤ radical K L :=by {
          unfold radical

          intro h2 p q r
          obtain ⟨hs, hq⟩ := r
          rw [← hq]
          rw [Set.mem_iInter]
          intro hq2
          simp at hq2
          have stuff := hq2 S
          let solve : IsSolvable S := by {
            constructor
            unfold derivedSeries
            unfold derivedSeriesOfIdeal
            use 1
            ext m
            constructor
            . intro inCom
              simp
              sorry

            . intro inBot
              simp at inBot
              simp [inBot]
          }
          have hope := stuff solve
          have more := hope p
          exact more
        }
        apply carr
        apply xinS
      .  intro h
         simp
         simp at h
         rw [h]
         simp



end LieAlgebra
