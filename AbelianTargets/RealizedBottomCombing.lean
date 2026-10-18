import AbelianTargets.DigitBottomCombing

/-! The logarithmic-speed bottom combing takes values in the actual carrier. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

def realizedBottomCombing (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (z : ℝ × unitInterval) : Realization m (Nat.log m R) 0 R :=
  (ambientEquiv m (Nat.log m R) 0 R).symm
    ⟨bottomCombing m hm R z,bottomCombing_mem m hm R hR z⟩

@[simp] theorem realizedBottomCombing_mass (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (z : ℝ × unitInterval) : (realizedBottomCombing m hm R hR z).1.mass =
      bottomCombing m hm R z :=
  congrArg Subtype.val ((ambientEquiv m (Nat.log m R) 0 R).apply_symm_apply _)

theorem realizedBottomCombing_continuous (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R) :
    Continuous (realizedBottomCombing m hm R hR) :=
  (ambientEquiv m (Nat.log m R) 0 R).symm.continuous.comp
    ((bottomCombing_continuous m hm R hR).subtype_mk _)

theorem realizedBottomCombing_path_time_lipschitz (m : ℕ) (hm : 2 ≤ m) (R : ℕ)
    (hR : 0 < R) (x : ℝ) : LipschitzWith (carryRowBudget m R+2 : ℝ≥0)
      (fun u => realizedBottomCombing m hm R hR (x,u)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change dist (realizedBottomCombing m hm R hR (x,u)).1.mass
    (realizedBottomCombing m hm R hR (x,v)).1.mass ≤ _
  rw [realizedBottomCombing_mass,realizedBottomCombing_mass]
  exact (bottomCombing_path_time_lipschitz m hm R hR x).dist_le_mul u v

theorem realizedBottomCombing_joint_lipschitz (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R) :
    ∃ J : ℝ≥0, LipschitzWith J (realizedBottomCombing m hm R hR) := by
  obtain ⟨J,hJ⟩ := bottomCombing_joint_lipschitz m hm R hR
  refine ⟨J,LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  change dist (realizedBottomCombing m hm R hR x).1.mass
    (realizedBottomCombing m hm R hR y).1.mass ≤ _
  rw [realizedBottomCombing_mass,realizedBottomCombing_mass]
  exact hJ.dist_le_mul x y

@[simp] theorem realizedBottomCombing_source (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (x : ℝ) : realizedBottomCombing m hm R hR (x,0) = point (carrierBase (Nat.log m R) R) := by
  apply Subtype.ext
  apply Probability.ext
  rw [realizedBottomCombing_mass,bottomCombing_source m hm R hR,bottomMass_eq _ R 0 (by omega)]
  have he : bottomVertex (Nat.log m R) R 0 (by omega) = carrierBase (Nat.log m R) R := by
    apply Subtype.ext
    rfl
  rw [he]
  rfl

@[simp] theorem realizedBottomCombing_target_mass (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (x : ℝ) : (realizedBottomCombing m hm R hR (x,1)).1.mass = bottomMap (Nat.log m R) R x := by
  rw [realizedBottomCombing_mass,bottomCombing_target m hm R hR]

@[simp] theorem realizedBottomCombing_base (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (u : unitInterval) : realizedBottomCombing m hm R hR (0,u) = point (carrierBase (Nat.log m R) R) := by
  apply Subtype.ext
  apply Probability.ext
  rw [realizedBottomCombing_mass,bottomCombing_base m hm R hR,bottomMass_eq _ R 0 (by omega)]
  have he : bottomVertex (Nat.log m R) R 0 (by omega) = carrierBase (Nat.log m R) R := by
    apply Subtype.ext
    rfl
  rw [he]
  rfl

end
end AbelianTargets.IntervalCarriers
