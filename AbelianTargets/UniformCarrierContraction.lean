import AbelianTargets.CommonHeightCarrierContraction
import AbelianTargets.CarrierTranslationEquiv

set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets.ControlledContraction
open scoped NNReal
noncomputable section

def weaken {Z : Type*} [MetricSpace Z] {p : Z} {D J : ℝ≥0}
    (H : ControlledContraction p D J) (D' J' : ℝ≥0) (hD : D ≤ D') (hJ : J ≤ J') :
    ControlledContraction p D' J' where
  map := H.map
  continuous := H.continuous
  at_zero := H.at_zero
  at_one := H.at_one
  fixes := H.fixes
  track z := (H.track z).weaken hD
  joint := H.joint.weaken hJ

end
end AbelianTargets.ControlledContraction

namespace AbelianTargets.IntervalCarriers
open scoped NNReal BigOperators
noncomputable section

def uniformCarrierSpeed (m T : ℕ) : ℝ≥0 := (2*((3*m+8)*(T+1)) : ℕ)

theorem commonHeightSpeed_le_uniform (m T R : ℕ) (hlog : Nat.log m R ≤ T) :
    commonHeightSpeed m T R ≤ uniformCarrierSpeed m T := by
  have h₀ : T*(m+2)≤(3*m+8)*(T+1) := by nlinarith
  have h₁ : carryRowBudget m R+2≤(3*m+8)*(T+1) := by
    dsimp [carryRowBudget]
    nlinarith
  unfold commonHeightSpeed uniformCarrierSpeed
  have ht : (T : ℝ≥0)*(m+2 : ℕ) ≤ ((3*m+8)*(T+1) : ℕ) := by exact_mod_cast h₀
  have hb : (carryRowBudget m R+2 : ℝ≥0) ≤ ((3*m+8)*(T+1) : ℕ) := by exact_mod_cast h₁
  calc
    _ ≤ 2*(((3*m+8)*(T+1) : ℕ) : ℝ≥0) := mul_le_mul_left' (max_le ht hb) 2
    _ = ((2*((3*m+8)*(T+1)) : ℕ) : ℝ≥0) := by norm_cast

theorem exists_uniformCarrierContractions (m : ℕ) (hm : 2 ≤ m) (T S : ℕ)
    (hST : Nat.log m S ≤ T) :
    ∃ J : ℝ≥0,∀ R : ℕ,∀ hR : 0 < R,R ≤ S →
      Nonempty (ControlledContraction
        (point (carrierBase T R) : Realization m T 0 R) (uniformCarrierSpeed m T) J) := by
  classical
  let Q (r : Fin (S+1)) (hr : 0 < r.val) :=
    exists_commonHeightControlledContraction m hm T r.val hr
      ((Nat.log_mono_right (by omega : r.val ≤ S)).trans hST)
  let j : Fin (S+1) → ℝ≥0 := fun r => if hr : 0 < r.val then (Q r hr).choose else 0
  refine ⟨∑ r,j r,?_⟩
  intro R hR hRS
  let r : Fin (S+1) := ⟨R,by omega⟩
  obtain ⟨C⟩ := (Q r hR).choose_spec
  have hj : (Q r hR).choose ≤ ∑ a,j a := by
    have hs : j r ≤ ∑ a,j a := Finset.single_le_sum (fun a _ => by positivity) (Finset.mem_univ r)
    have he : j r=(Q r hR).choose := by unfold j; rw [dif_pos hR]
    rw [he] at hs
    exact hs
  exact ⟨C.weaken (uniformCarrierSpeed m T) (∑ a,j a)
    (commonHeightSpeed_le_uniform m T R ((Nat.log_mono_right hRS).trans hST)) hj⟩

theorem exists_translated_uniformCarrierContractions (m : ℕ) (hm : 2 ≤ m) (T S : ℕ)
    (hST : Nat.log m S ≤ T) :
    ∃ J : ℝ≥0,∀ (A : ℤ) (R : ℕ) (hR : 0 < R),R ≤ S →
      Nonempty (ControlledContraction
        ((realizationTranslationEquiv (m := m) (K := T) (A := 0) (B := R) A)
          (point (carrierBase T R))) (uniformCarrierSpeed m T) J) := by
  obtain ⟨J,hJ⟩ := exists_uniformCarrierContractions m hm T S hST
  refine ⟨J,?_⟩
  intro A R hR hRS
  obtain ⟨C⟩ := hJ R hR hRS
  exact ⟨C.transport (realizationTranslationEquiv A)⟩

end
end AbelianTargets.IntervalCarriers
