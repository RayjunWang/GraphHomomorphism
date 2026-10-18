import AbelianTargets.Actions
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

/-!
# Anisotropic marker packing

Integer quotient buckets prove the uniform finite bound for markers in
a scaled box. The bound is independent of the coordinate scales, as
required by the priority construction of the rectangular atlas.
-/

namespace AbelianTargets

theorem abs_sub_lt_of_ediv_eq {a b l : ℤ} (hl : 0 < l)
    (heq : a/l = b/l) : |a-b| < l := by
  have ha₀ := Int.emod_nonneg a hl.ne'
  have hb₀ := Int.emod_nonneg b hl.ne'
  have ha₁ := Int.emod_lt_of_pos a hl
  have hb₁ := Int.emod_lt_of_pos b hl
  have ha := Int.emod_add_ediv_mul a l
  have hb := Int.emod_add_ediv_mul b l
  rw [heq] at ha
  rw [abs_lt]
  omega

def packingBucket (S : ℕ) (x l : ℤ) (hl : 0 < l)
    (hx : -(S : ℤ)*l ≤ x ∧ x ≤ (S : ℤ)*l) : Fin (2*S+1) := by
  have hlo : -(S : ℤ) ≤ x/l := (Int.le_ediv_iff_mul_le hl).mpr hx.1
  have hhi : x/l ≤ (S : ℤ) := (Int.ediv_le_iff_le_mul hl).mpr (by omega)
  exact ⟨(x/l+S).toNat, by omega⟩

theorem packingBucket_value (S : ℕ) (x l : ℤ) (hl : 0 < l)
    (hx : -(S : ℤ)*l ≤ x ∧ x ≤ (S : ℤ)*l) :
    ((packingBucket S x l hl hx).val : ℤ) = x/l+S := by
  change ((x/l+S).toNat : ℤ) = x/l+S
  apply Int.toNat_of_nonneg
  have := (Int.le_ediv_iff_mul_le hl).mpr hx.1
  omega

/-- A separated marker family has at most `(2S+1)^d` points within
scaled coordinate distance `S` of a chosen origin. -/
theorem anisotropic_marker_packing {d : ℕ} (S : ℕ) (L : Fin d → ℕ)
    (hL : ∀ i, 1 ≤ L i) (A : Finset (Lattice d))
    (hbounded : ∀ a ∈ A, ∀ i, -(S : ℤ)*(L i : ℤ) ≤ a i ∧ a i ≤ (S : ℤ)*(L i : ℤ))
    (hseparated : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∃ i, (L i : ℤ) < |a i-b i|) :
    A.card ≤ (2*S+1)^d := by
  classical
  have hpos : ∀ i, 0 < (L i : ℤ) := by
    intro i
    exact_mod_cast (show 0 < L i by have := hL i; omega)
  let bucket : A → (Fin d → Fin (2*S+1)) :=
    fun a i => packingBucket S (a.val i) (L i) (hpos i) (hbounded a.val a.property i)
  have hinj : Function.Injective bucket := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    obtain ⟨i,hi⟩ := hseparated a.val a.property b.val b.property hne
    have hcoord := congrArg (fun f : Fin d → Fin (2*S+1) => ((f i).val : ℤ)) hab
    have heq : a.val i/(L i : ℤ) = b.val i/(L i : ℤ) := by
      change ((packingBucket S (a.val i) (L i) (hpos i) (hbounded a.val a.property i)).val : ℤ) =
        ((packingBucket S (b.val i) (L i) (hpos i) (hbounded b.val b.property i)).val : ℤ) at hcoord
      rw [packingBucket_value,packingBucket_value] at hcoord
      omega
    have := abs_sub_lt_of_ediv_eq (hpos i) heq
    omega
  have hc := Fintype.card_le_of_injective bucket hinj
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using hc

/-- The slightly larger constant used in the paper is therefore valid. -/
theorem anisotropic_marker_packing_paper_bound {d : ℕ} (S : ℕ) (L : Fin d → ℕ)
    (hL : ∀ i, 1 ≤ L i) (A : Finset (Lattice d))
    (hbounded : ∀ a ∈ A, ∀ i, -(S : ℤ)*(L i : ℤ) ≤ a i ∧ a i ≤ (S : ℤ)*(L i : ℤ))
    (hseparated : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∃ i, (L i : ℤ) < |a i-b i|) :
    A.card ≤ (2*S+3)^d :=
  (anisotropic_marker_packing S L hL A hbounded hseparated).trans
    (Nat.pow_le_pow_left (show 2*S+1 ≤ 2*S+3 by omega) d)

end AbelianTargets
