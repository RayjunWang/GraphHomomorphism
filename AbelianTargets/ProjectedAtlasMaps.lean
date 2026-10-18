import AbelianTargets.AtlasRankRecursion
import AbelianTargets.CarrierProjectionNaturality
import AbelianTargets.UniformCarrierSupportProjection
import AbelianTargets.IntegerCellGluing

/-! Actual global support maps from compatible carrier maps on a rectangular atlas. -/
namespace AbelianTargets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace RectangularCell
theorem rank_lt_succ_dimension {d:ℕ} (R:RectangularCell d) : R.rank<d+1 := by
  have h : R.varyingAxes.card≤Fintype.card (Fin d) := Finset.card_le_univ _
  simpa only [Fintype.card_fin] using Nat.lt_succ_of_le h
end RectangularCell

namespace SkeletonCarrierMaps
variable {d:ℕ} {K₀:Fin d→ℕ} {T:IntegerRectangularTiling d K₀}
variable {W:Type*} [Fintype W] {H:SimpleGraph W} (D:SupportTorsionData H)
variable {K:ℕ} {i:Fin d} (F:SkeletonCarrierMaps T (2*D.power+1) K i (d+1))

def projectedMap (z:RealCoordinates d) : SupportPair H :=
  D.carrierProjection K ((T.pointCell z).lower i) ((T.pointCell z).upper i)
    (F.map (T.pointCell z) ⟨z,rfl⟩ (T.pointCell z).rank_lt_succ_dimension
      ⟨z,(T.pointCell z).relativeInterior_subset (T.mem_relativeInterior_pointCell z)⟩)

theorem cellProjection_include {P Q:RectangularCell d} (hsub:P.closedBox⊆Q.closedBox)
    (p:CellIntervalCarrier (2*D.power+1) K i P) :
    D.carrierProjection K (Q.lower i) (Q.upper i) (cellIntervalInclude i hsub p)=
      D.carrierProjection K (P.lower i) (P.upper i) p :=
  D.carrierProjection_intervalInclusion
    ((RectangularCell.closedBox_subset_iff P Q).mp hsub i).1
    ((RectangularCell.closedBox_subset_iff P Q).mp hsub i).2 p

theorem projectedMap_eq_cell (R:RectangularCell d) (hR:R∈T.cells)
    (z:RealCoordinates d) (hz:z∈R.closedBox) :
    F.projectedMap D z=D.carrierProjection K (R.lower i) (R.upper i)
      (F.map R hR R.rank_lt_succ_dimension ⟨z,hz⟩) := by
  let P := T.pointCell z
  have hP : P∈T.cells := ⟨z,rfl⟩
  have hsub : P.closedBox⊆R.closedBox := T.pointCell_subset_cell hR hz
  let zP : CellClosedDomain P :=
    ⟨z,P.relativeInterior_subset (T.mem_relativeInterior_pointCell z)⟩
  change D.carrierProjection K (P.lower i) (P.upper i)
    (F.map P hP P.rank_lt_succ_dimension zP)=_
  rw [←cellProjection_include D hsub (F.map P hP P.rank_lt_succ_dimension zP),
    F.compatible P R hP hR P.rank_lt_succ_dimension R.rank_lt_succ_dimension hsub zP]

theorem continuousOn_projectedMap_cell (R:RectangularCell d) (hR:R∈T.cells) :
    ContinuousOn (F.projectedMap D) R.closedBox := by
  apply continuousOn_iff_continuous_restrict.mpr
  have hc : Continuous (fun z:CellClosedDomain R =>
      D.carrierProjection K (R.lower i) (R.upper i)
        (F.map R hR R.rank_lt_succ_dimension z)) :=
    (D.continuous_carrierProjection K _ _).comp (F.map R hR R.rank_lt_succ_dimension).continuous
  apply hc.congr
  intro z
  exact (F.projectedMap_eq_cell D R hR z.val z.property).symm

theorem continuous_projectedMap : Continuous (F.projectedMap D) := by
  apply continuous_of_rectangular_cell_cover
    (fun R:T.cells => R.val) T.cells_locallyFinite
  · intro z
    exact ⟨⟨T.pointCell z,⟨z,rfl⟩⟩,
      (T.pointCell z).relativeInterior_subset (T.mem_relativeInterior_pointCell z)⟩
  · intro R
    exact F.continuousOn_projectedMap_cell D R.val R.property

theorem projectedMap_unit_interval_cell (j:Fin d) (z:RealCoordinates d) (n:ℤ)
    (x y:ℝ) (hx:x∈Set.Icc (n:ℝ) ((n:ℝ)+1)) (hy:y∈Set.Icc (n:ℝ) ((n:ℝ)+1)) :
    ∃R:RectangularCell d,∃hR:R∈T.cells,
      ∃hxR:Function.update z j x∈R.closedBox,∃hyR:Function.update z j y∈R.closedBox,
        F.projectedMap D (Function.update z j x)=D.carrierProjection K (R.lower i) (R.upper i)
          (F.map R hR R.rank_lt_succ_dimension ⟨Function.update z j x,hxR⟩) ∧
        F.projectedMap D (Function.update z j y)=D.carrierProjection K (R.lower i) (R.upper i)
          (F.map R hR R.rank_lt_succ_dimension ⟨Function.update z j y,hyR⟩) := by
  let w := Function.update z j ((n:ℝ)+1/2)
  let R := T.pointCell w
  have hR : R∈T.cells := ⟨w,rfl⟩
  have hw : w∈R.closedBox := R.relativeInterior_subset (T.mem_relativeInterior_pointCell w)
  have hxR := R.coordinate_unit_interval z j n hw x hx
  have hyR := R.coordinate_unit_interval z j n hw y hy
  exact ⟨R,hR,hxR,hyR,F.projectedMap_eq_cell D R hR _ hxR,F.projectedMap_eq_cell D R hR _ hyR⟩

theorem projectedMap_close_in_cell (ε δ:ℝ)
    (hmod:∀A B:ℤ,∀p q:IntervalCarriers.Realization (2*D.power+1) K A B,
      dist p q<δ→dist (D.carrierProjection K A B p) (D.carrierProjection K A B q)<ε)
    (R:RectangularCell d) (hR:R∈T.cells) (z z':RealCoordinates d)
    (hz:z∈R.closedBox) (hz':z'∈R.closedBox)
    (hd:dist (F.map R hR R.rank_lt_succ_dimension ⟨z,hz⟩)
      (F.map R hR R.rank_lt_succ_dimension ⟨z',hz'⟩)<δ) :
    dist (F.projectedMap D z) (F.projectedMap D z')<ε := by
  rw [F.projectedMap_eq_cell D R hR z hz,F.projectedMap_eq_cell D R hR z' hz']
  exact hmod _ _ _ _ hd

end SkeletonCarrierMaps
end
end AbelianTargets
