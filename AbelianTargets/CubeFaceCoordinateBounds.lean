import AbelianTargets.CubeBoundaryGluing

/-! Coordinate telescoping on a fixed face of a finite maximum-norm cube. -/
namespace AbelianTargets
open scoped BigOperators NNReal
noncomputable section

def cubeFaceHybrid {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ConeSphere (ι → ℝ)) (j : ι) (hj : |x.1 j|=1) (he : x.1 j=y.1 j)
    (s : Finset ι) : ConeSphere (ι → ℝ) :=
  ⟨fun k => if k∈s then y.1 k else x.1 k,by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ)≤1)).mpr
      intro k
      by_cases hk : k∈s
      · simpa only [hk,if_true,Real.norm_eq_abs] using coneSphere_coordinate_bound y k
      · simpa only [hk,if_false,Real.norm_eq_abs] using coneSphere_coordinate_bound x k
    · have hh := norm_le_pi_norm (fun k => if k∈s then y.1 k else x.1 k) j
      by_cases hjs : j∈s
      · simpa only [hjs,if_true,Real.norm_eq_abs,←he,hj] using hh
      · simpa only [hjs,if_false,Real.norm_eq_abs,hj] using hh⟩

theorem cubeFaceHybrid_extreme {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ConeSphere (ι → ℝ)) (j : ι) (hj : |x.1 j|=1) (he : x.1 j=y.1 j) (s : Finset ι) :
    (cubeFaceHybrid x y j hj he s).1 j=x.1 j := by
  simp only [cubeFaceHybrid]
  split_ifs
  · exact he.symm
  · rfl

theorem cubeFace_dist_le_sum {ι Z : Type*} [Fintype ι] [PseudoMetricSpace Z]
    (f : ConeSphere (ι → ℝ)→Z) (C : ι→ℝ≥0)
    (hcoord : ∀ j k (x y : ConeSphere (ι → ℝ)),|x.1 j|=1→x.1 j=y.1 j→
      (∀ l,l≠k→x.1 l=y.1 l)→dist (f x) (f y)≤C k*|x.1 k-y.1 k|)
    (j : ι) (x y : ConeSphere (ι → ℝ)) (hj : |x.1 j|=1) (he : x.1 j=y.1 j) :
    dist (f x) (f y)≤∑ k,(C k : ℝ)*|x.1 k-y.1 k| := by
  classical
  have h : ∀ s : Finset ι,dist (f x) (f (cubeFaceHybrid x y j hj he s))≤
      ∑ k∈s,(C k : ℝ)*|x.1 k-y.1 k| := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have hz : cubeFaceHybrid x y j hj he ∅=x := by apply Subtype.ext; funext k; simp [cubeFaceHybrid]
      simp [hz]
    | @insert k s hks ih =>
      have h₁ := cubeFaceHybrid_extreme x y j hj he s
      have h₂ := cubeFaceHybrid_extreme x y j hj he (insert k s)
      have hh := hcoord j k (cubeFaceHybrid x y j hj he s) (cubeFaceHybrid x y j hj he (insert k s))
        (by rw [h₁];exact hj) (h₁.trans h₂.symm) (fun l hl => by
          simp [cubeFaceHybrid,Finset.mem_insert,hl])
      simp only [cubeFaceHybrid,hks,if_false,Finset.mem_insert_self,if_true] at hh
      calc
        _ ≤ dist (f x) (f (cubeFaceHybrid x y j hj he s))+
            dist (f (cubeFaceHybrid x y j hj he s)) (f (cubeFaceHybrid x y j hj he (insert k s))) := dist_triangle _ _ _
        _ ≤ (∑ l∈s,(C l : ℝ)*|x.1 l-y.1 l|)+(C k : ℝ)*|x.1 k-y.1 k| := add_le_add ih hh
        _ = _ := by rw [Finset.sum_insert hks];ring
  have hh := h Finset.univ
  have hy : cubeFaceHybrid x y j hj he Finset.univ=y := by apply Subtype.ext;funext k;simp [cubeFaceHybrid]
  simpa only [hy] using hh

theorem lipschitz_cubeBoundary_of_coordinate_faces {ι Z : Type*} [Fintype ι] [PseudoMetricSpace Z]
    (f : ConeSphere (ι → ℝ)→Z) (C : ι→ℝ≥0) (D : ℝ≥0)
    (hdiam : ∀ x y,dist (f x) (f y)≤D)
    (hcoord : ∀ j k (x y : ConeSphere (ι → ℝ)),|x.1 j|=1→x.1 j=y.1 j→
      (∀ l,l≠k→x.1 l=y.1 l)→dist (f x) (f y)≤C k*|x.1 k-y.1 k|) :
    LipschitzWith (2*(∑ k,C k)+D) f := by
  apply lipschitz_cubeBoundary_of_faces f (∑ k,C k) D hdiam
  intro j x y hj he
  calc
    _ ≤ ∑ k,(C k : ℝ)*|x.1 k-y.1 k| := cubeFace_dist_le_sum f C hcoord j x y hj he
    _ ≤ ∑ k,(C k : ℝ)*dist x y := Finset.sum_le_sum (fun k hk =>
      mul_le_mul_of_nonneg_left (dist_le_pi_dist x.1 y.1 k) (C k).2)
    _ = _ := by rw [←Finset.sum_mul];simp

end
end AbelianTargets
