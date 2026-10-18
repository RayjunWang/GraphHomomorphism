import AbelianTargets.OneHeightDeformation
import AbelianTargets.CarrierCollapseFixed
import AbelianTargets.CarrierNesting

set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

theorem oneHeightStage_fixes_lower {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Probability (CarrierVertex (K+1) A B)) (hp : ∀ v, 0 < p.mass v → v.1.2 ≤ K)
    (n : ℕ) (t : unitInterval) : oneHeightStage hm n (p,t) = p := by
  cases n with
  | zero => exact top_mapList_fixes_lower hm p hp _ t
  | succ n =>
    simp only [oneHeightStage]
    split_ifs
    · exact fan_mapList_fixes_lower hm _ p hp _ t
    · exact verticalMap_fixes_lower p hp t
    · rfl

theorem oneHeightHomotopy_fixes_lower {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m (K+1) A B) (hp : ∀ v, 0 < p.1.mass v → v.1.2 ≤ K)
    (t : unitInterval) : oneHeightHomotopy hm p t = p := by
  apply Subtype.ext
  exact stageCurve_fixed (fun p : Realization m (K+1) A B => p.1) (oneHeightStage hm)
    p p.1 rfl (fun n t => oneHeightStage_fixes_lower hm p.1 hp n t) (m+2) t

def oneHeightRetraction {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B) :
    Realization m K A B :=
  restrictHeight hm (oneHeightHomotopy hm p 1) (oneHeightHomotopy_one_height hm p)

theorem include_oneHeightRetraction {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B) :
    carrierInclude (by omega : K ≤ K+1) (oneHeightRetraction hm p) = oneHeightHomotopy hm p 1 :=
  include_restrictHeight hm _ _

theorem oneHeightRetraction_joint {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) :
    ∃ J : ℝ≥0, LipschitzWith J (oneHeightRetraction (K := K) (A := A) (B := B) hm) := by
  obtain ⟨J,hJ⟩ := oneHeightHomotopy_joint (K := K) (A := A) (B := B) hm
  refine ⟨J,LipschitzWith.of_dist_le_mul ?_⟩
  intro p q
  have hd : dist (oneHeightRetraction hm p) (oneHeightRetraction hm q) =
      dist (oneHeightHomotopy hm p 1) (oneHeightHomotopy hm q 1) := by
    rw [←include_oneHeightRetraction hm p,←include_oneHeightRetraction hm q]
    exact ((isometry_include (m := m) (A := A) (B := B) (by omega : K ≤ K+1)).dist_eq _ _).symm
  rw [hd]
  simpa only [Prod.dist_eq,dist_self,max_eq_left dist_nonneg] using hJ.dist_le_mul (p,1) (q,1)

theorem continuous_oneHeightRetraction {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) :
    Continuous (oneHeightRetraction (K := K) (A := A) (B := B) hm) :=
  (oneHeightRetraction_joint hm).choose_spec.continuous

theorem oneHeightRetraction_preserves_bottom {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m (K+1) A B) (hp : ∀ v, 0 < p.1.mass v → v.1.2 = 0)
    (v : CarrierVertex K A B) (hv : 0 < (oneHeightRetraction hm p).1.mass v) : v.1.2 = 0 := by
  have hpl : ∀ u, 0 < p.1.mass u → u.1.2 ≤ K := fun u hu => by rw [hp u hu]; exact Nat.zero_le _
  change 0 < (Probability.push vertexLower (oneHeightHomotopy hm p 1).1).mass v at hv
  rw [oneHeightHomotopy_fixes_lower hm p hpl 1] at hv
  obtain ⟨u,hu,hup⟩ := (Probability.push_pos_iff vertexLower p.1 v).mp hv
  rw [←hu]
  simp only [vertexLower,hp u hup,Nat.zero_min]

end
end AbelianTargets.IntervalCarriers
