import AbelianTargets.RectangleHalfGluing
import AbelianTargets.RowSlotScaling

/-! The complete moving-endpoint family across one bottom edge. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def halfPoint : unitInterval := ⟨1/2,by constructor <;> norm_num⟩
def upperHalf (r : unitInterval) : unitInterval :=
  ⟨((r : ℝ)+1)/2,by constructor <;> linarith [r.property.1,r.property.2]⟩

theorem upperHalf_lipschitz : LipschitzWith 1 upperHalf := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  change |((r : ℝ)+1)/2-((s : ℝ)+1)/2| ≤ (1 : ℝ)*|(r : ℝ)-(s : ℝ)|
  rw [show ((r : ℝ)+1)/2-((s : ℝ)+1)/2 = ((r : ℝ)-(s : ℝ))/2 by ring,
    abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2),one_mul]
  nlinarith [abs_nonneg ((r : ℝ)-(s : ℝ))]

theorem interval_dist_le_one (r s : unitInterval) : dist r s ≤ 1 := by
  change |(r : ℝ)-(s : ℝ)| ≤ 1
  rw [abs_le]
  constructor <;> linarith [r.property.1,r.property.2,s.property.1,s.property.2]

theorem mix_eq_lineMap (a b : E) (r : unitInterval) :
    mix a b r = AffineMap.lineMap a b (r : ℝ) := (AffineMap.lineMap_apply_module _ _ _).symm

structure BottomSpliceData (n : ℕ) (base p q : E) (S : Set E) (Δ : ℝ≥0) where
  leftRow : ℕ → E
  carrySource : BasedRow n base q
  carryTarget : BasedRow n base q
  left_source : leftRow 0 = base
  left_target : leftRow (n+2) = p
  left_edges : ∀ j ≤ n+1, dist (leftRow j) (leftRow (j+1)) ≤ Δ
  seam_edges : ∀ j ≤ n+1,
    dist (appendRowEndpoint carrySource.vertices n (mix p q halfPoint) j)
      (appendRowEndpoint carrySource.vertices n (mix p q halfPoint) (j+1)) ≤ Δ
  left_charts : ∀ j ≤ n+1, ∃ F : Set E, Convex ℝ F ∧ F ⊆ S ∧
    leftRow j ∈ F ∧ leftRow (j+1) ∈ F ∧
    appendRowEndpoint carrySource.vertices n (mix p q halfPoint) j ∈ F ∧
    appendRowEndpoint carrySource.vertices n (mix p q halfPoint) (j+1) ∈ F
  corresponding_bound : ∃ C : ℝ≥0, ∀ j ≤ n+2,
    dist (leftRow j) (appendRowEndpoint carrySource.vertices n (mix p q halfPoint) j) ≤ C
  edge_bound : dist p q ≤ Δ
  edge_chart : ∃ F : Set E, Convex ℝ F ∧ F ⊆ S ∧ p ∈ F ∧ q ∈ F
  carry : carrySource.path.Homotopy carryTarget.path
  carry_mem : ∀ t, carry t ∈ S
  carry_speed : ∀ r, LipschitzWith (Δ*(n+1)) (carry.eval r)
  carry_joint : ∃ J : ℝ≥0, LipschitzWith J carry

namespace BottomSpliceData
variable {n : ℕ} {base p q : E} {S : Set E} {Δ : ℝ≥0}
variable (D : BottomSpliceData n base p q S Δ)

def seamRow : ℕ → E := appendRowEndpoint D.carrySource.vertices n (mix p q halfPoint)
def leftFamily := rowFamily D.leftRow D.seamRow (n+1)
def rightFamily := correctedCarry n D.carry q (fun r => mix p q (upperHalf r))
def family := halfGlue D.leftFamily D.rightFamily

theorem seam_match (u : unitInterval) : D.leftFamily (1,u) = D.rightFamily (0,u) := by
  rw [leftFamily,rowFamily_one]
  have hh := correctedCarry_row_eq n D.carrySource.vertices q
    (fun r => mix p q (upperHalf r)) D.carry 0
    (fun u => D.carry.map_zero_left u) D.carrySource.target u
  have he : upperHalf 0 = halfPoint := by apply Subtype.ext; norm_num [upperHalf,halfPoint]
  rw [he] at hh
  exact hh.symm

theorem continuous_family : Continuous D.family := by
  apply halfGlue_continuous _ _ (rowFamily_continuous _ _ _) _ D.seam_match
  exact correctedCarry_continuous n D.carry D.carry.continuous q _
    ((mix_lipschitz p q Δ D.edge_bound).continuous.comp upperHalf_lipschitz.continuous)
    (fun r => D.carry.target r)

theorem family_path_time_lipschitz (r : unitInterval) :
    LipschitzWith (Δ*(n+2)) (fun u => D.family (r,u)) := by
  apply halfGlue_path_time_lipschitz
  · intro r
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two,leftFamily] using
      rowFamily_path_time_lipschitz D.leftRow D.seamRow (n+1) Δ D.left_edges D.seam_edges r
  · exact correctedCarry_path_time_lipschitz n D.carry q _ Δ D.carry_speed
      (fun r => D.carry.target r) (fun r => by
        have h := (mix_lipschitz p q Δ D.edge_bound).dist_le_mul 1 (upperHalf r)
        rw [mix_one] at h
        exact h.trans (mul_le_of_le_one_right Δ.property (interval_dist_le_one _ _)))

theorem family_joint_lipschitz : ∃ J : ℝ≥0, LipschitzWith J D.family := by
  obtain ⟨C,hC⟩ := D.corresponding_bound
  have hL := rowFamily_joint_lipschitz D.leftRow D.seamRow (n+1) Δ C D.left_edges D.seam_edges hC
  obtain ⟨J,hJ⟩ := D.carry_joint
  have he : LipschitzWith Δ (fun r => mix p q (upperHalf r)) := by
    simpa only [mul_one] using (mix_lipschitz p q Δ D.edge_bound).comp upperHalf_lipschitz
  obtain ⟨K,hK⟩ := correctedCarry_joint_lipschitz n D.carry q _ hJ
    (fun r => D.carry.target r) he (fun r => by
      have h := (mix_lipschitz p q Δ D.edge_bound).dist_le_mul 1 (upperHalf r)
      rw [mix_one] at h
      exact h.trans (mul_le_of_le_one_right Δ.property (interval_dist_le_one _ _)))
  exact ⟨_,halfGlue_joint_lipschitz _ _ hL hK D.seam_match⟩

theorem family_mem (t : unitInterval × unitInterval) : D.family t ∈ S := by
  apply halfGlue_mem _ _ _ _ t
  · exact rowFamily_mem_charts D.leftRow D.seamRow (n+1) D.left_charts
  · apply correctedCarry_mem n D.carry q _ D.carry_mem
    intro r t
    obtain ⟨F,hconv,hsub,hp,hq⟩ := D.edge_chart
    exact hsub (mix_mem hconv hq (mix_mem hconv hp hq (upperHalf r)) t)

@[simp] theorem family_source (r : unitInterval) : D.family (r,0) = base := by
  unfold family halfGlue halfGlueRaw leftFamily rightFamily
  split_ifs
  · rw [rowFamily_source,D.left_source]
    have hs : D.seamRow 0 = base := by
      simp only [seamRow,appendRowEndpoint,if_pos (show 0 ≤ n+1 by omega),D.carrySource.source]
    rw [hs,mix_self]
  · rw [correctedCarry_source]
    exact D.carry.source _

@[simp] theorem family_target (r : unitInterval) : D.family (r,1) = mix p q r := by
  unfold family halfGlue halfGlueRaw leftFamily rightFamily
  split_ifs with hr
  · rw [rowFamily_target,D.left_target]
    have ht : D.seamRow (n+1+1) = mix p q halfPoint := by
      simp only [seamRow,appendRowEndpoint,if_neg (show ¬n+1+1 ≤ n+1 by omega)]
    rw [ht]
    have htime : 0 ≤ 2*(r : ℝ) ∧ 2*(r : ℝ) ≤ 1 := by constructor <;> linarith [r.property.1]
    rw [show clampInterval (2*(r : ℝ)) = ⟨_,htime⟩ from clampInterval_coe ⟨_,htime⟩]
    rw [mix_eq_lineMap,mix_eq_lineMap,mix_eq_lineMap]
    change AffineMap.lineMap p (AffineMap.lineMap p q (1/2 : ℝ)) (2*(r : ℝ)) = _
    rw [AffineMap.lineMap_lineMap_right]
    congr 1
    ring
  · rw [correctedCarry_target]
    have htime : 0 ≤ 2*(r : ℝ)-1 ∧ 2*(r : ℝ)-1 ≤ 1 := by
      constructor <;> linarith [r.property.2]
    rw [show clampInterval (2*(r : ℝ)-1) = ⟨_,htime⟩ from clampInterval_coe ⟨_,htime⟩]
    congr 1
    apply Subtype.ext
    change ((2*(r : ℝ)-1)+1)/2 = (r : ℝ)
    ring

@[simp] theorem family_zero (u : unitInterval) : D.family (0,u) = asPath D.leftRow (n+1) u := by
  rw [family,halfGlue_zero,leftFamily,rowFamily_zero]

@[simp] theorem family_one (u : unitInterval) : D.family (1,u) =
    asPath (appendRowEndpoint D.carryTarget.vertices n q) (n+1) u := by
  rw [family,halfGlue_one]
  have hh := correctedCarry_row_eq n D.carryTarget.vertices q
    (fun r => mix p q (upperHalf r)) D.carry 1
    (fun u => D.carry.map_one_left u) D.carryTarget.target u
  have he : upperHalf 1 = 1 := by apply Subtype.ext; norm_num [upperHalf]
  rw [he,mix_one] at hh
  exact hh

end BottomSpliceData
end
end AbelianTargets.FixedSlots
