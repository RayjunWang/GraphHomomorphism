import AbelianTargets.CarrierControlledContraction
import AbelianTargets.GeneralCarrierHeightRestriction
import AbelianTargets.ProbabilityPushDirac

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Controlled contractions at a common height, including intervals shorter
than the ambient logarithmic scale. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

theorem carrierInclude_point {m K T : ℕ} {A B : ℤ} (hKT : K ≤ T)
    (v : CarrierVertex K A B) : carrierInclude (m := m) hKT (point v)=point (vertexInclude hKT v) := by
  apply Subtype.ext
  exact Probability.push_dirac _ _

@[simp] theorem carrierInclude_base {m K T R : ℕ} (hKT : K ≤ T) :
    carrierInclude (m := m) hKT (point (carrierBase K R))=point (carrierBase T R) := by
  rw [carrierInclude_point]
  rfl

def bottomEndpointLower (m : ℕ) (hm : 1 ≤ m) (T R : ℕ) (hlog : Nat.log m R ≤ T)
    (p : Realization m T 0 R) : Realization m (Nat.log m R) 0 R :=
  restrictCarrierHeight hm hlog (heightDeformation hm T 0 R (p,1))
    (fun v hv => by rw [heightDeformation_terminal hm p v hv]; exact Nat.zero_le _)

theorem include_bottomEndpointLower (m : ℕ) (hm : 1 ≤ m) (T R : ℕ)
    (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) :
    carrierInclude hlog (bottomEndpointLower m hm T R hlog p)=heightDeformation hm T 0 R (p,1) :=
  carrierInclude_restrictCarrierHeight hm hlog _ _

theorem bottomEndpointLower_bottom (m : ℕ) (hm : 1 ≤ m) (T R : ℕ)
    (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) :
    ∀ v,0 < (bottomEndpointLower m hm T R hlog p).1.mass v → v.1.2=0 :=
  restrictCarrierHeight_preserves_bottom hm hlog _ _ (heightDeformation_terminal hm p)

theorem bottomEndpointLower_joint (m : ℕ) (hm : 1 ≤ m) (T R : ℕ)
    (hlog : Nat.log m R ≤ T) : ∃ J : ℝ≥0,LipschitzWith J (bottomEndpointLower m hm T R hlog) := by
  obtain ⟨J,hJ⟩ := heightDeformation_joint (K := T) (A := 0) (B := R) hm
  have he := hJ.comp ((LipschitzWith.id : LipschitzWith 1 (id : Realization m T 0 R → _)).prodMk
    (LipschitzWith.const (1 : unitInterval)))
  refine ⟨J*max 1 0,LipschitzWith.of_dist_le_mul fun p q => ?_⟩
  rw [←(isometry_include (m := m) (A := 0) (B := R) hlog).dist_eq,
    include_bottomEndpointLower,include_bottomEndpointLower]
  exact he.dist_le_mul p q

@[simp] theorem bottomEndpointLower_base (m : ℕ) (hm : 1 ≤ m) (T R : ℕ)
    (hlog : Nat.log m R ≤ T) :
    bottomEndpointLower m hm T R hlog (point (carrierBase T R))=point (carrierBase (Nat.log m R) R) := by
  apply (isometry_include (m := m) (A := 0) (B := R) hlog).injective
  rw [include_bottomEndpointLower,carrierInclude_base,
    heightDeformation_fixes_bottom hm _ (base_height_zero _ _)]

def commonHeightBottomFinish (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) (z : Realization m T 0 R × unitInterval) : Realization m T 0 R :=
  carrierInclude hlog (bottomFinish m hm R hR
    (bottomEndpointLower m (by omega : 1 ≤ m) T R hlog z.1,z.2))

theorem commonHeightBottomFinish_zero (m : ℕ) (hm : 2 ≤ m) (T R : ℕ)
    (hR : 0 < R) (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) :
    commonHeightBottomFinish m hm T R hR hlog (p,0)=heightDeformation (by omega : 1 ≤ m) T 0 R (p,1) := by
  unfold commonHeightBottomFinish
  rw [bottomFinish_zero,heightDeformation_fixes_bottom (by omega : 1 ≤ m) _
    (bottomEndpointLower_bottom m (by omega : 1 ≤ m) T R hlog p),include_bottomEndpointLower]

@[simp] theorem commonHeightBottomFinish_one (m : ℕ) (hm : 2 ≤ m) (T R : ℕ)
    (hR : 0 < R) (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) :
    commonHeightBottomFinish m hm T R hR hlog (p,1)=point (carrierBase T R) := by
  simp [commonHeightBottomFinish]

theorem commonHeightBottomFinish_track (m : ℕ) (hm : 2 ≤ m) (T R : ℕ)
    (hR : 0 < R) (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) :
    LipschitzWith (carryRowBudget m R+2 : ℝ≥0)
      (fun t => commonHeightBottomFinish m hm T R hR hlog (p,t)) := by
  simpa only [commonHeightBottomFinish,Function.comp_def,one_mul] using
    (isometry_include (m := m) (A := 0) (B := R) hlog).lipschitz.comp
      (bottomFinish_track m hm R hR (bottomEndpointLower m (by omega : 1 ≤ m) T R hlog p))

theorem commonHeightBottomFinish_joint (m : ℕ) (hm : 2 ≤ m) (T R : ℕ)
    (hR : 0 < R) (hlog : Nat.log m R ≤ T) :
    ∃ J : ℝ≥0,LipschitzWith J (commonHeightBottomFinish m hm T R hR hlog) := by
  obtain ⟨Jr,hJr⟩ := bottomEndpointLower_joint m (by omega : 1 ≤ m) T R hlog
  obtain ⟨Jb,hJb⟩ := bottomFinish_joint m hm R hR
  have hp := (hJr.comp LipschitzWith.prod_fst).prodMk
    (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : Realization m T 0 R × unitInterval → unitInterval))
  refine ⟨Jb*max (Jr*1) 1,?_⟩
  simpa only [commonHeightBottomFinish,Function.comp_def,one_mul] using
    (isometry_include (m := m) (A := 0) (B := R) hlog).lipschitz.comp (hJb.comp hp)

theorem commonHeightBottomFinish_base (m : ℕ) (hm : 2 ≤ m) (T R : ℕ)
    (hR : 0 < R) (hlog : Nat.log m R ≤ T) (t : unitInterval) :
    commonHeightBottomFinish m hm T R hR hlog (point (carrierBase T R),t)=point (carrierBase T R) := by
  simp [commonHeightBottomFinish,bottomFinish_base]

def commonHeightStages (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) : ℕ → Realization m T 0 R × unitInterval → Realization m T 0 R
  | 0 => heightDeformation (by omega : 1 ≤ m) T 0 R
  | 1 => commonHeightBottomFinish m hm T R hR hlog
  | _+2 => fun _ => point (carrierBase T R)

theorem commonHeightStages_seam (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) (n : ℕ) (p : Realization m T 0 R) :
    commonHeightStages m hm T R hR hlog n (p,1)=commonHeightStages m hm T R hR hlog (n+1) (p,0) := by
  cases n with
  | zero => exact (commonHeightBottomFinish_zero m hm T R hR hlog p).symm
  | succ n =>
    cases n with
    | zero => exact commonHeightBottomFinish_one m hm T R hR hlog p
    | succ n => rfl

def commonHeightSpeed (m T R : ℕ) : ℝ≥0 :=
  2*max ((T : ℝ≥0)*(m+2 : ℕ)) (carryRowBudget m R+2 : ℝ≥0)

def commonHeightContractionMap (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) := familyHomotopy (commonHeightStages m hm T R hR hlog) 2

theorem commonHeightContractionMap_track (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) :
    LipschitzWith (commonHeightSpeed m T R) (fun t => commonHeightContractionMap m hm T R hR hlog (p,t)) := by
  apply familyHomotopy_track _ (commonHeightStages_seam m hm T R hR hlog)
    (max ((T : ℝ≥0)*(m+2 : ℕ)) (carryRowBudget m R+2 : ℝ≥0)) _ 2 p
  intro n q
  cases n with
  | zero => exact (heightDeformation_track (by omega : 1 ≤ m) q).weaken (le_max_left _ _)
  | succ n =>
    cases n with
    | zero => exact (commonHeightBottomFinish_track m hm T R hR hlog q).weaken (le_max_right _ _)
    | succ n => exact (LipschitzWith.const _).weaken (by positivity)

theorem commonHeightContractionMap_joint (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) : ∃ J : ℝ≥0,LipschitzWith J (commonHeightContractionMap m hm T R hR hlog) := by
  apply familyHomotopy_joint _ (commonHeightStages_seam m hm T R hR hlog) _ 2
  intro n
  cases n with
  | zero => exact heightDeformation_joint (by omega : 1 ≤ m)
  | succ n =>
    cases n with
    | zero => exact commonHeightBottomFinish_joint m hm T R hR hlog
    | succ n => exact ⟨0,LipschitzWith.const _⟩

@[simp] theorem commonHeightContractionMap_zero (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) : commonHeightContractionMap m hm T R hR hlog (p,0)=p := by
  change familyCurve _ 2 (0,p)=p
  rw [familyCurve_zero]
  exact heightDeformation_zero (by omega : 1 ≤ m) p

@[simp] theorem commonHeightContractionMap_one (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) (p : Realization m T 0 R) :
    commonHeightContractionMap m hm T R hR hlog (p,1)=point (carrierBase T R) := by
  change familyCurve _ (1+1) (1,p)=_
  rw [familyCurve_one]
  exact commonHeightBottomFinish_one m hm T R hR hlog p

theorem commonHeightContractionMap_base (m : ℕ) (hm : 2 ≤ m) (T R : ℕ) (hR : 0 < R)
    (hlog : Nat.log m R ≤ T) (t : unitInterval) :
    commonHeightContractionMap m hm T R hR hlog (point (carrierBase T R),t)=point (carrierBase T R) := by
  apply familyCurve_fixed
  intro n u
  cases n with
  | zero => exact heightDeformation_fixes_bottom (by omega : 1 ≤ m) _ (base_height_zero _ _) u
  | succ n =>
    cases n with
    | zero => exact commonHeightBottomFinish_base m hm T R hR hlog u
    | succ n => rfl

theorem exists_commonHeightControlledContraction (m : ℕ) (hm : 2 ≤ m) (T R : ℕ)
    (hR : 0 < R) (hlog : Nat.log m R ≤ T) :
    ∃ J : ℝ≥0,Nonempty (ControlledContraction
      (point (carrierBase T R) : Realization m T 0 R) (commonHeightSpeed m T R) J) := by
  obtain ⟨J,hJ⟩ := commonHeightContractionMap_joint m hm T R hR hlog
  refine ⟨J,⟨{
    map := commonHeightContractionMap m hm T R hR hlog
    continuous := hJ.continuous
    at_zero := commonHeightContractionMap_zero m hm T R hR hlog
    at_one := commonHeightContractionMap_one m hm T R hR hlog
    fixes := commonHeightContractionMap_base m hm T R hR hlog
    track := commonHeightContractionMap_track m hm T R hR hlog
    joint := hJ }⟩⟩

end
end AbelianTargets.IntervalCarriers
