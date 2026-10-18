import AbelianTargets.CarrierHeightChain

/-! The actual finite strip is deformed to its literal bottom edges in
logarithmic-height time, with a speed independent of its horizontal size. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

def heightDeformation {m : ℕ} (hm : 1 ≤ m) (K : ℕ) (A B : ℤ)
    (z : Realization m K A B × unitInterval) : Realization m K A B :=
  familyHomotopy (heightChain hm K A B).curve K z

theorem heightDeformation_joint {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) :
    ∃ J : ℝ≥0, LipschitzWith J (heightDeformation hm K A B) :=
  familyHomotopy_joint _ (heightChain hm K A B).seam (heightChain hm K A B).joint K

theorem continuous_heightDeformation {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) :
    Continuous (heightDeformation hm K A B) :=
  (heightDeformation_joint (K := K) (A := A) (B := B) hm).choose_spec.continuous

theorem heightDeformation_track {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m K A B) :
    LipschitzWith ((K : ℝ≥0)*(m+2 : ℕ)) (fun t => heightDeformation hm K A B (p,t)) :=
  familyHomotopy_track _ (heightChain hm K A B).seam _ (heightChain hm K A B).track K p

@[simp] theorem heightDeformation_zero {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m K A B) : heightDeformation hm K A B (p,0)=p := by
  unfold heightDeformation familyHomotopy
  change familyCurve (heightChain hm K A B).curve K (0,p)=p
  rw [familyCurve_zero,(heightChain hm K A B).initial]

theorem heightDeformation_one {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m K A B) :
    heightDeformation hm K A B (p,1)=(heightChain hm K A B).curve K (p,0) := by
  cases K with
  | zero =>
    unfold heightDeformation familyHomotopy familyCurve
    rfl
  | succ K =>
    unfold heightDeformation familyHomotopy
    change familyCurve (heightChain hm (K+1) A B).curve (K+1) (1,p)=_
    rw [familyCurve_one,(heightChain hm (K+1) A B).seam]

theorem heightDeformation_terminal {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m K A B) (v : CarrierVertex K A B)
    (hv : 0 < (heightDeformation hm K A B (p,1)).1.mass v) : v.1.2=0 := by
  rw [heightDeformation_one] at hv
  exact (heightChain hm K A B).terminal p v hv

theorem heightDeformation_fixes_bottom {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m K A B) (hp : ∀ v,0 < p.1.mass v → v.1.2=0)
    (t : unitInterval) : heightDeformation hm K A B (p,t)=p :=
  familyCurve_fixed _ p p ((heightChain hm K A B).fixes_bottom p hp) K t

end
end AbelianTargets.IntervalCarriers
