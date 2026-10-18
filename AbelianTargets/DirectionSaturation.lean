import AbelianTargets.Dimension
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Equality in the signed-unit-vector bound

Lemma 7.4 of arXiv:2609.39824v1 uses the following saturation argument:
if `n` signed coordinate vectors sum to `n` times a single signed
coordinate vector, then every summand is that vector. This file proves
the claim over exact integers. It uses nonnegative deficits in the
distinguished oriented coordinate, rather than assuming a norm-equality
principle or the surrounding twelve-tile rigidity theorem.
-/

namespace AbelianTargets

open scoped BigOperators

/-- Evaluate a direction on the distinguished axis of `u`, with the
orientation of `u` chosen as positive. -/
def SignedDirection.alignment {m : ℕ} (u s : SignedDirection m) : ℤ :=
  if u.positive then s.vector u.axis else -s.vector u.axis

theorem SignedDirection.vector_axis {m : ℕ} (u : SignedDirection m) :
    u.vector u.axis = if u.positive then (1 : ℤ) else -1 := by
  cases hu : u.positive <;> simp [SignedDirection.vector, hu, unitVector]

theorem SignedDirection.alignment_le_one {m : ℕ} (u s : SignedDirection m) :
    u.alignment s ≤ 1 := by
  rcases u with ⟨i, b⟩
  rcases s with ⟨j, c⟩
  by_cases hij : i = j
  · subst j
    cases b <;> cases c <;>
      norm_num [SignedDirection.alignment, SignedDirection.vector, unitVector]
  · cases b <;> cases c <;>
      simp [SignedDirection.alignment, SignedDirection.vector, unitVector, hij]

/-- Alignment reaches its upper bound exactly for the same signed vector. -/
theorem SignedDirection.alignment_eq_one_iff {m : ℕ} (u s : SignedDirection m) :
    u.alignment s = 1 ↔ s = u := by
  rcases u with ⟨i, b⟩
  rcases s with ⟨j, c⟩
  by_cases hij : i = j
  · subst j
    cases b <;> cases c <;>
      norm_num [SignedDirection.alignment, SignedDirection.vector, unitVector,
        SignedDirection.mk.injEq]
  · cases b <;> cases c <;>
      simp [SignedDirection.alignment, SignedDirection.vector, unitVector,
        SignedDirection.mk.injEq, hij, Ne.symm hij]

/-- Exact saturation: a sum of `n` signed unit vectors equals `n • u`
only when every summand is `u`. This is the norm-saturation step in
the boundary-cycle and tile-row arguments of Lemma 7.4. -/
theorem signedDirection_sum_saturation {n m : ℕ}
    (s : Fin n → SignedDirection m) (u : SignedDirection m)
    (hsum : (∑ j, (s j).vector : Lattice m) = n • u.vector) :
    ∀ j, s j = u := by
  have hcoordinate : (∑ j, (s j).vector u.axis : ℤ) =
      (n : ℤ) * (if u.positive then 1 else -1) := by
    simpa only [Finset.sum_apply, Pi.smul_apply, Int.nsmul_eq_mul,
      SignedDirection.vector_axis] using congrFun hsum u.axis
  have halign : (∑ j, u.alignment (s j) : ℤ) = (n : ℤ) := by
    cases hu : u.positive with
    | false =>
      have hc : (∑ j, (s j).vector u.axis : ℤ) = -(n : ℤ) := by
        simpa [hu] using hcoordinate
      simpa [SignedDirection.alignment, hu, Finset.sum_neg_distrib] using
        congrArg Neg.neg hc
    | true => simpa [SignedDirection.alignment, hu] using hcoordinate
  have hdeficit : (∑ j, (1 - u.alignment (s j)) : ℤ) = 0 := by
    rw [Finset.sum_sub_distrib, halign]
    simp
  have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      (0 : ℤ) ≤ 1 - u.alignment (s j) := by
    intro j _
    exact sub_nonneg.mpr (u.alignment_le_one (s j))
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hdeficit
  intro j
  apply (u.alignment_eq_one_iff (s j)).mp
  have hj := hzero j (Finset.mem_univ j)
  omega

end AbelianTargets
