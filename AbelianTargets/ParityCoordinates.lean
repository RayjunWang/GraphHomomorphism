import AbelianTargets.Actions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# The unimodular parity coordinate change in Proposition 6.1

The new first coordinate is the sum of the original coordinates. Hence
every original generator has first coordinate one, and each of the
remaining generators changes only one transverse coordinate as well.
-/

namespace AbelianTargets

open scoped BigOperators

def firstAxis {d : ℕ} (hd : 1 ≤ d) : Fin d := ⟨0, by omega⟩

def shearCoordinates {d : ℕ} (hd : 1 ≤ d) (g : Lattice d) : Lattice d :=
  fun i => if i = firstAxis hd then ∑ j, g j else g i

def unshearCoordinates {d : ℕ} (hd : 1 ≤ d) (g : Lattice d) : Lattice d :=
  fun i => if i = firstAxis hd then
    g (firstAxis hd) - ∑ j ∈ Finset.univ.erase (firstAxis hd), g j else g i

theorem sum_erase_shearCoordinates {d : ℕ} (hd : 1 ≤ d) (g : Lattice d) :
    (∑ j ∈ Finset.univ.erase (firstAxis hd), shearCoordinates hd g j) =
      ∑ j ∈ Finset.univ.erase (firstAxis hd), g j := by
  apply Finset.sum_congr rfl
  intro j hj
  simp only [shearCoordinates, if_neg (Finset.mem_erase.mp hj).1]

theorem unshear_shearCoordinates {d : ℕ} (hd : 1 ≤ d) (g : Lattice d) :
    unshearCoordinates hd (shearCoordinates hd g) = g := by
  funext i
  by_cases hi : i = firstAxis hd
  · subst i
    change (∑ j, g j) - (∑ j ∈ Finset.univ.erase (firstAxis hd),
      shearCoordinates hd g j) = g (firstAxis hd)
    rw [sum_erase_shearCoordinates]
    have he := Finset.sum_erase_add (Finset.univ : Finset (Fin d)) g
      (Finset.mem_univ (firstAxis hd))
    omega
  · simp [unshearCoordinates, shearCoordinates, hi]

theorem shear_unshearCoordinates {d : ℕ} (hd : 1 ≤ d) (g : Lattice d) :
    shearCoordinates hd (unshearCoordinates hd g) = g := by
  funext i
  by_cases hi : i = firstAxis hd
  · subst i
    change (∑ j, unshearCoordinates hd g j) = g (firstAxis hd)
    have hsum : (∑ j ∈ Finset.univ.erase (firstAxis hd), unshearCoordinates hd g j) =
        ∑ j ∈ Finset.univ.erase (firstAxis hd), g j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [unshearCoordinates, if_neg (Finset.mem_erase.mp hj).1]
    have he := Finset.sum_erase_add (Finset.univ : Finset (Fin d))
      (unshearCoordinates hd g) (Finset.mem_univ (firstAxis hd))
    change (∑ j ∈ Finset.univ.erase (firstAxis hd), unshearCoordinates hd g j) +
      (g (firstAxis hd) - ∑ j ∈ Finset.univ.erase (firstAxis hd), g j) =
      ∑ j, unshearCoordinates hd g j at he
    rw [hsum] at he
    omega
  · simp [unshearCoordinates, shearCoordinates, hi]

/-- The literal integer-lattice automorphism corresponding to the
basis `e₁, e₂-e₁, …, e_d-e₁`. -/
def parityCoordinateEquiv {d : ℕ} (hd : 1 ≤ d) : Lattice d ≃+ Lattice d where
  toFun := shearCoordinates hd
  invFun := unshearCoordinates hd
  left_inv := unshear_shearCoordinates hd
  right_inv := shear_unshearCoordinates hd
  map_add' := by
    intro g h
    funext i
    by_cases hi : i = firstAxis hd
    · simp [shearCoordinates, hi, Finset.sum_add_distrib]
    · simp [shearCoordinates, hi]

@[simp] theorem shearCoordinates_first {d : ℕ} (hd : 1 ≤ d) (g : Lattice d) :
    shearCoordinates hd g (firstAxis hd) = ∑ i, g i := by simp [shearCoordinates]

theorem shearCoordinates_generator_first {d : ℕ} (hd : 1 ≤ d) (i : Fin d) :
    shearCoordinates hd (unitVector i) (firstAxis hd) = 1 := by
  simp [shearCoordinates, unitVector]

theorem shearCoordinates_first_generator {d : ℕ} (hd : 1 ≤ d) :
    shearCoordinates hd (unitVector (firstAxis hd)) = unitVector (firstAxis hd) := by
  funext i
  by_cases hi : i = firstAxis hd
  · subst i; simp [shearCoordinates, unitVector]
  · simp [shearCoordinates, unitVector, hi]

theorem shearCoordinates_other_generator {d : ℕ} (hd : 1 ≤ d) (i : Fin d)
    (hi : i ≠ firstAxis hd) :
    shearCoordinates hd (unitVector i) = unitVector (firstAxis hd) + unitVector i := by
  funext j
  by_cases hj : j = firstAxis hd
  · subst j
    simp [shearCoordinates, unitVector, Ne.symm hi]
  · simp [shearCoordinates, unitVector, hj]

end AbelianTargets
