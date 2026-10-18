import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The finite cut-selection argument in Lemma 3.2

The earlier parallel cuts exclude a controlled number of integer
candidates. This module proves the actual separated-cut existence with
the paper's constants. It does not assume the rectangular atlas.
-/

namespace AbelianTargets

open scoped BigOperators

def forbiddenCuts (earlier : Finset ℤ) (δ : ℕ) : Finset ℤ :=
  earlier.biUnion (fun b => Finset.Icc (b-(δ : ℤ)) (b+δ))

theorem forbiddenCuts_card_le (earlier : Finset ℤ) (δ : ℕ) :
    (forbiddenCuts earlier δ).card ≤ earlier.card * (2*δ+1) := by
  unfold forbiddenCuts
  calc
    _ ≤ ∑ b ∈ earlier, (Finset.Icc (b-(δ : ℤ)) (b+δ)).card := Finset.card_biUnion_le
    _ = earlier.card * (2*δ+1) := by
      have hcard : ∀ b : ℤ, (Finset.Icc (b-(δ : ℤ)) (b+δ)).card = 2*δ+1 := by
        intro b
        rw [Int.card_Icc]
        have he : b+(δ : ℤ)+1-(b-δ) = ((2*δ+1 : ℕ) : ℤ) := by push_cast; ring
        rw [he, Int.toNat_natCast]
      simp [hcard, nsmul_eq_mul]

theorem cut_budget_strict {P L : ℕ} (hP : 1 ≤ P) (hL : 32*P ≤ L) :
    2*P*(2*(L/(16*P))+1) < L+1 := by
  have hdiv := Nat.mul_div_le L (16*P)
  nlinarith

/-- An integer candidate separated from every earlier cut. The stronger
strict separation here is enough for the non-strict bound in the paper. -/
theorem exists_separated_cut {P L : ℕ} (hP : 1 ≤ P) (hL : 32*P ≤ L)
    (a : ℤ) (earlier : Finset ℤ) (hearlier : earlier.card ≤ 2*P) :
    ∃ c : ℤ, a ≤ c ∧ c ≤ a+L ∧
      ∀ b ∈ earlier, ((L/(16*P) : ℕ) : ℤ) < |c-b| := by
  let δ := L/(16*P)
  let candidates := Finset.Icc a (a+(L : ℤ))
  have hcard : candidates.card = L+1 := by
    dsimp [candidates]
    rw [Int.card_Icc]
    have he : a+(L : ℤ)+1-a = ((L+1 : ℕ) : ℤ) := by push_cast; ring
    rw [he, Int.toNat_natCast]
  have hbad : (forbiddenCuts earlier δ).card < candidates.card := by
    rw [hcard]
    exact ((forbiddenCuts_card_le earlier δ).trans
      (Nat.mul_le_mul_right (2*δ+1) hearlier)).trans_lt (cut_budget_strict hP hL)
  have hnsubset : ¬candidates ⊆ forbiddenCuts earlier δ := by
    intro hs
    have := Finset.card_le_card hs
    omega
  obtain ⟨c,hc,hnot⟩ := Finset.not_subset.mp hnsubset
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hc
  refine ⟨c,hlo,hhi,?_⟩
  intro b hb
  have hnotIcc : c ∉ Finset.Icc (b-(δ : ℤ)) (b+δ) := by
    intro hc'
    exact hnot (Finset.mem_biUnion.mpr ⟨b,hb,hc'⟩)
  have hnotbetween : ¬(b-(δ : ℤ) ≤ c ∧ c ≤ b+δ) := by
    simpa only [Finset.mem_Icc] using hnotIcc
  change (δ : ℤ) < |c-b|
  rw [lt_abs]
  omega

/-- The integer spacing is positive once the scales exceed the stated
threshold. -/
theorem atlas_cut_spacing_pos {P L : ℕ} (hP : 1 ≤ P) (hL : 32*P ≤ L) :
    1 ≤ L/(16*P) := by
  apply Nat.le_div_iff_mul_le (by omega) |>.mpr
  omega

end AbelianTargets
