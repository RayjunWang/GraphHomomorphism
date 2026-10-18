import AbelianTargets.AtlasQuantitativeRecursion
import AbelianTargets.AtlasControlledCellExtension
import Mathlib.Tactic.GCongr

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AbelianTargets
noncomputable section
open scoped NNReal BigOperators
variable {d : ℕ} {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d}

def rankBoundaryRate (U C : Fin d→ℝ≥0) : ℝ≥0 :=
  2*d*(∑ j,C j*U j/2)+1

def nextRankRates (δ U C : Fin d→ℝ≥0) (D J : ℝ≥0) (i : Fin d) (j : Fin d) : ℝ≥0 :=
  max (C j) (if j=i then 3*max (C i*U i) D/δ j
    else 2*ControlledContraction.coneTransverseConstant (C i*U i) D J (rankBoundaryRate U C)/δ j)

def atlasRankRates (δ U : Fin d→ℝ≥0) (D J : ℝ≥0) (i : Fin d) : ℕ→Fin d→ℝ≥0
  | 0 => fun _ => 0
  | n+1 => nextRankRates δ U (atlasRankRates δ U D J i n) D J i

theorem atlasRankRates_step_mono (δ U : Fin d→ℝ≥0) (D J : ℝ≥0) (i : Fin d)
    (n : ℕ) (j : Fin d) : atlasRankRates δ U D J i n j≤atlasRankRates δ U D J i (n+1) j :=
  le_max_left _ _

theorem prismTransverseBound_le_rankBoundaryRate (R : RectangularCell d) (i : Fin d)
    (C U : Fin d→ℝ≥0) (hU : ∀j,(R.transverseWidth j).toNNReal≤U j) :
    LowerCellCarrierMaps.prismTransverseBound R i C≤rankBoundaryRate U C := by
  let s : ℝ≥0 := ∑ j,C j*U j/2
  have hcard : Fintype.card (R.ActiveTransverse i)≤d := by
    have hh := Fintype.card_le_of_injective
      (Subtype.val : R.ActiveTransverse i → Fin d) Subtype.val_injective
    simpa using hh
  have hs : ∑ j : R.ActiveTransverse i,C j.val*(R.transverseWidth j.val).toNNReal/2≤
      (d : ℝ≥0)*s := by
    calc
      _ ≤ ∑ _j : R.ActiveTransverse i,s := Finset.sum_le_sum (fun j _ => by
        calc
          _ ≤ C j.val*U j.val/2 := by gcongr; exact hU j.val
          _ ≤ s := by
            change C j.val*U j.val/2≤∑ k,C k*U k/2
            exact Finset.single_le_sum (f := fun k : Fin d => C k*U k/2)
              (fun _ _ => by positivity) (Finset.mem_univ j.val))
      _ = (Fintype.card (R.ActiveTransverse i) : ℝ≥0)*s := by simp
      _ ≤ (d : ℝ≥0)*s := by gcongr
  unfold LowerCellCarrierMaps.prismTransverseBound rankBoundaryRate
  calc
    _ ≤ 2*((d : ℝ≥0)*s)+1 := by gcongr
    _ = _ := by dsimp [s]; ring

theorem fillingCoordinateRate_le_nextRankRates (R : RectangularCell d) (i : Fin d)
    (C δ U : Fin d→ℝ≥0) (D J : ℝ≥0) (hδ : ∀j,0<δ j)
    (hlower : ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper : ∀j,(R.transverseWidth j).toNNReal≤U j) (j : Fin d)
    (hj : R.lower j<R.upper j) :
    LowerCellCarrierMaps.fillingCoordinateRate R i (C i*(R.transverseWidth i).toNNReal)
      (LowerCellCarrierMaps.prismTransverseBound R i C) D J j≤nextRankRates δ U C D J i j := by
  have hS : C i*(R.transverseWidth i).toNNReal≤C i*U i := by gcongr; exact hupper i
  have hB := prismTransverseBound_le_rankBoundaryRate R i C U hupper
  apply le_trans _ (le_max_right _ _)
  unfold LowerCellCarrierMaps.fillingCoordinateRate
  split_ifs with hji
  · exact div_le_div₀ (by positivity) (by gcongr) (hδ j) (hlower j hj)
  · apply div_le_div₀ (by positivity) _ (hδ j) (hlower j hj)
    unfold ControlledContraction.coneTransverseConstant
    gcongr

theorem exists_actual_quantitative_skeleton_maps (δ U : Fin d→ℝ≥0) (D J : ℝ≥0)
    (hδ : ∀j,0<δ j)
    (hlower : ∀R,R∈T.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper : ∀R,R∈T.cells → ∀j,(R.transverseWidth j).toNNReal≤U j)
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → Nonempty (ControlledContraction (cellLeftPoint m K i R) D J))
    (n : ℕ) : Nonempty (QuantitativeEndpointSkeletonCarrierMaps T m K i n (atlasRankRates δ U D J i n)) := by
  classical
  induction n with
  | zero => exact ⟨QuantitativeEndpointSkeletonCarrierMaps.empty⟩
  | succ n ih =>
    obtain ⟨F⟩ := ih
    let C := atlasRankRates δ U D J i n
    let extend (R : RectangularCell d) (hR : R∈T.cells) (he : R.rank=n) :
        EndpointCellCarrierExtension (F.toSkeletonCarrierMaps.lowerFamily R he) hR :=
      if hi : R.lower i<R.upper i then
        (F.toSkeletonCarrierMaps.lowerFamily R he).controlledCellExtension hR
          (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he) C
          (F.lowerFamily_update_bounds R he) hi (Classical.choice (H R hR hi))
      else (F.toSkeletonCarrierMaps.lowerFamily R he).collapsedCellExtension hR
        (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he)
        (le_antisymm (R.ordered i) (le_of_not_gt hi))
    refine ⟨F.next extend (atlasRankRates_step_mono δ U D J i n) ?_⟩
    intro R hR he j z z' heq
    by_cases hi : R.lower i<R.upper i
    · simp only [extend,dif_pos hi]
      let LF := F.toSkeletonCarrierMaps.lowerFamily R he
      have hC : LF.CoordinateBounds C := F.lowerFamily_update_bounds R he
      have hE := LF.relativeCellExtension_coordinate_bounds hR
        (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he) hi
        (Classical.choice (H R hR hi))
        (LF.prism_path_lipschitz hR hi (C i) (hC i)) (LF.prism_transverse_lipschitz hR C hC)
      have hh := hE j z z' heq
      by_cases hj : R.lower j<R.upper j
      · exact hh.trans (mul_le_mul_of_nonneg_right
          (fillingCoordinateRate_le_nextRankRates R i C δ U D J hδ
            (hlower R hR) (hupper R hR) j hj) (abs_nonneg _))
      · have hz := R.point_eq_of_only_collapsed_coordinate j
          (le_antisymm (R.ordered j) (le_of_not_gt hj)) z z' heq
        rw [hz,dist_self]
        positivity
    · simp only [extend,dif_neg hi]
      exact (F.toSkeletonCarrierMaps.lowerFamily R he).collapsedCellExtension_coordinate_bounds hR
        (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he) _ _ j z z' heq

end
end AbelianTargets
