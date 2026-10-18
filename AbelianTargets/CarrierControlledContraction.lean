import AbelianTargets.CarrierHeightDeformation
import AbelianTargets.BottomHeightZero
import AbelianTargets.RealizedBottomCombing
import AbelianTargets.RelativePathComparison

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! An actual controlled contraction of the finite triangulated interval
carrier. Every track has logarithmic speed; the joint constant is finite. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

def bottomFinish (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (z : Realization m (Nat.log m R) 0 R × unitInterval) :
    Realization m (Nat.log m R) 0 R :=
  realizedBottomCombing m hm R hR
    (bottomCoordinate (Nat.log m R) R
      (heightDeformation (by omega : 1 ≤ m) (Nat.log m R) 0 R (z.1,1)).1,
      unitInterval.symm z.2)

theorem bottomFinish_zero (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (p : Realization m (Nat.log m R) 0 R) :
    bottomFinish m hm R hR (p,0)=heightDeformation (by omega : 1 ≤ m) (Nat.log m R) 0 R (p,1) := by
  apply Subtype.ext
  apply Probability.ext
  simp only [bottomFinish,unitInterval.symm_zero,realizedBottomCombing_target_mass]
  exact bottomMap_inverse_height_zero (by omega : 1 ≤ m) _
    (heightDeformation_terminal (by omega : 1 ≤ m) p)

@[simp] theorem bottomFinish_one (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (p : Realization m (Nat.log m R) 0 R) :
    bottomFinish m hm R hR (p,1)=point (carrierBase (Nat.log m R) R) := by
  simp [bottomFinish]

theorem bottomFinish_track (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (p : Realization m (Nat.log m R) 0 R) :
    LipschitzWith (carryRowBudget m R+2 : ℝ≥0) (fun t => bottomFinish m hm R hR (p,t)) := by
  simpa only [bottomFinish,Function.comp_def,mul_one] using
    (realizedBottomCombing_path_time_lipschitz m hm R hR _).comp lipschitz_interval_symm

theorem bottomFinish_joint (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R) :
    ∃ J : ℝ≥0, LipschitzWith J (bottomFinish m hm R hR) := by
  obtain ⟨Jh,hJh⟩ := heightDeformation_joint (K := Nat.log m R) (A := 0) (B := R) (by omega : 1 ≤ m)
  obtain ⟨Jb,hJb⟩ := realizedBottomCombing_joint_lipschitz m hm R hR
  have hendpoint := hJh.comp ((LipschitzWith.id : LipschitzWith 1 (id : Realization m (Nat.log m R) 0 R → _)).prodMk
    (LipschitzWith.const (1 : unitInterval)))
  have hcoordinate := (bottomCoordinate_lipschitz (Nat.log m R) R).comp
    (isometry_subtype_coe.lipschitz.comp hendpoint)
  have hpair := (hcoordinate.comp LipschitzWith.prod_fst).prodMk
    (lipschitz_interval_symm.comp LipschitzWith.prod_snd)
  refine ⟨Jb * max ((Probability.weightedCoordinateConstant (fun v : CarrierVertex (Nat.log m R) 0 R =>
      (v.val.1 : ℝ)) * (1 * (Jh * max 1 0))) * 1) (1 * 1),?_⟩
  simpa only [bottomFinish,Function.comp_def] using hJb.comp hpair

theorem base_height_zero (K R : ℕ) (v : CarrierVertex K 0 R)
    (hv : 0 < (point (carrierBase K R) : Realization m K 0 R).1.mass v) : v.1.2=0 := by
  classical
  have he : v=carrierBase K R := by
    by_contra h
    change 0 < (Probability.dirac (carrierBase K R)).mass v at hv
    simp [Probability.dirac_mass,h] at hv
  rw [he]
  rfl

theorem bottomFinish_base (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (t : unitInterval) :
    bottomFinish m hm R hR (point (carrierBase (Nat.log m R) R),t)=point (carrierBase (Nat.log m R) R) := by
  unfold bottomFinish
  rw [heightDeformation_fixes_bottom (by omega : 1 ≤ m) _ (base_height_zero _ _)]
  have hc : bottomCoordinate (Nat.log m R) R (point (carrierBase (Nat.log m R) R) : Realization m (Nat.log m R) 0 R).1=0 := by
    classical
    simp [bottomCoordinate,Probability.weightedCoordinate,point,Probability.dirac_mass,carrierBase]
  rw [hc]
  exact realizedBottomCombing_base m hm R hR _

def carrierContractionStages (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R) :
    ℕ → Realization m (Nat.log m R) 0 R × unitInterval → Realization m (Nat.log m R) 0 R
  | 0 => heightDeformation (by omega : 1 ≤ m) (Nat.log m R) 0 R
  | 1 => bottomFinish m hm R hR
  | _+2 => fun _ => point (carrierBase (Nat.log m R) R)

theorem carrierContractionStages_seam (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (n : ℕ) (p : Realization m (Nat.log m R) 0 R) :
    carrierContractionStages m hm R hR n (p,1)=carrierContractionStages m hm R hR (n+1) (p,0) := by
  cases n with
  | zero => exact (bottomFinish_zero m hm R hR p).symm
  | succ n =>
    cases n with
    | zero => exact bottomFinish_one m hm R hR p
    | succ n => rfl

def carrierContractionSpeed (m R : ℕ) : ℝ≥0 :=
  2*max ((Nat.log m R : ℝ≥0)*(m+2 : ℕ)) (carryRowBudget m R+2 : ℝ≥0)

def carrierContractionMap (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R) :=
  familyHomotopy (carrierContractionStages m hm R hR) 2

theorem carrierContractionMap_track (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (p : Realization m (Nat.log m R) 0 R) :
    LipschitzWith (carrierContractionSpeed m R) (fun t => carrierContractionMap m hm R hR (p,t)) := by
  apply familyHomotopy_track _ (carrierContractionStages_seam m hm R hR)
    (max ((Nat.log m R : ℝ≥0)*(m+2 : ℕ)) (carryRowBudget m R+2 : ℝ≥0)) _ 2 p
  intro n q
  cases n with
  | zero => exact (heightDeformation_track (by omega : 1 ≤ m) q).weaken (le_max_left _ _)
  | succ n =>
    cases n with
    | zero => exact (bottomFinish_track m hm R hR q).weaken (le_max_right _ _)
    | succ n => exact (LipschitzWith.const _).weaken (by positivity)

theorem carrierContractionMap_joint (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R) :
    ∃ J : ℝ≥0,LipschitzWith J (carrierContractionMap m hm R hR) := by
  apply familyHomotopy_joint _ (carrierContractionStages_seam m hm R hR) _ 2
  intro n
  cases n with
  | zero => exact heightDeformation_joint (by omega : 1 ≤ m)
  | succ n =>
    cases n with
    | zero => exact bottomFinish_joint m hm R hR
    | succ n => exact ⟨0,LipschitzWith.const _⟩

@[simp] theorem carrierContractionMap_zero (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (p : Realization m (Nat.log m R) 0 R) : carrierContractionMap m hm R hR (p,0)=p := by
  change familyCurve _ 2 (0,p)=p
  rw [familyCurve_zero]
  exact heightDeformation_zero (by omega : 1 ≤ m) p

@[simp] theorem carrierContractionMap_one (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (p : Realization m (Nat.log m R) 0 R) :
    carrierContractionMap m hm R hR (p,1)=point (carrierBase (Nat.log m R) R) := by
  change familyCurve _ (1+1) (1,p)=_
  rw [familyCurve_one]
  exact bottomFinish_one m hm R hR p

theorem carrierContractionMap_base (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (t : unitInterval) :
    carrierContractionMap m hm R hR (point (carrierBase (Nat.log m R) R),t)=point (carrierBase (Nat.log m R) R) := by
  apply familyCurve_fixed
  intro n u
  cases n with
  | zero => exact heightDeformation_fixes_bottom (by omega : 1 ≤ m) _ (base_height_zero _ _) u
  | succ n =>
    cases n with
    | zero => exact bottomFinish_base m hm R hR u
    | succ n => rfl

theorem exists_carrierControlledContraction (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R) :
    ∃ J : ℝ≥0,Nonempty (ControlledContraction
      (point (carrierBase (Nat.log m R) R) : Realization m (Nat.log m R) 0 R)
      (carrierContractionSpeed m R) J) := by
  obtain ⟨J,hJ⟩ := carrierContractionMap_joint m hm R hR
  refine ⟨J,⟨{
    map := carrierContractionMap m hm R hR
    continuous := hJ.continuous
    at_zero := carrierContractionMap_zero m hm R hR
    at_one := carrierContractionMap_one m hm R hR
    fixes := carrierContractionMap_base m hm R hR
    track := carrierContractionMap_track m hm R hR
    joint := hJ }⟩⟩

end
end AbelianTargets.IntervalCarriers
