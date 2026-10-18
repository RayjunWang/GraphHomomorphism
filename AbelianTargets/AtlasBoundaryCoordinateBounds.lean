import AbelianTargets.AtlasBoundaryCarrierMaps
import AbelianTargets.IntegerIntervalGluing

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Coordinate estimates survive subdivisions of actual cell boundaries. -/
namespace AbelianTargets
open scoped NNReal
noncomputable section
namespace LowerCellCarrierMaps
variable {d : ℕ} {K₀ : Fin d → ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d} {R : RectangularCell d}

def boundaryCoordinateCurve (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (z : RealCoordinates d) (k : Fin d)
    (hline : ∀ r∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ),Function.update z k r∈R.boundary)
    (r : ℝ) : CellIntervalCarrier m K i R :=
  F.boundaryValue hR ⟨Function.update z k (integerIntervalClamp (R.lower k) (R.upper k) r),
    hline _ (integerIntervalClamp_mem (R.ordered k) r)⟩

theorem boundaryCoordinateCurve_eq (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (z : RealCoordinates d) (k : Fin d)
    (hline : ∀ r∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ),Function.update z k r∈R.boundary)
    (r : ℝ) (hr : r∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ)) :
    F.boundaryCoordinateCurve hR z k hline r=F.boundaryValue hR ⟨Function.update z k r,hline r hr⟩ := by
  apply congrArg (F.boundaryValue hR)
  apply Subtype.ext
  dsimp only [boundaryCoordinateCurve]
  rw [integerIntervalClamp_eq hr]

theorem boundary_coordinate_dist_le (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (k : Fin d) (C : ℝ≥0)
    (hcoord : ∀ (Q : RectangularCell d) (hQ : Q∈T.cells) (hrQ : Q.rank<R.rank)
      (w : RealCoordinates d) (x y : ℝ)
      (hx : Function.update w k x∈Q.closedBox) (hy : Function.update w k y∈Q.closedBox),
      dist (F.map Q hQ hrQ ⟨Function.update w k x,hx⟩)
        (F.map Q hQ hrQ ⟨Function.update w k y,hy⟩)≤C*|x-y|)
    (z : RealCoordinates d)
    (hline : ∀ r∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ),Function.update z k r∈R.boundary)
    (s t : ℝ) (hs : s∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ))
    (ht : t∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ)) :
    dist (F.boundaryValue hR ⟨Function.update z k s,hline s hs⟩)
      (F.boundaryValue hR ⟨Function.update z k t,hline t ht⟩)≤C*|s-t| := by
  let g := F.boundaryCoordinateCurve hR z k hline
  have hunit : ∀ n : ℤ,R.lower k≤n→n+1≤R.upper k→
      ∀ x∈Set.Icc (n : ℝ) ((n : ℝ)+1),∀ y∈Set.Icc (n : ℝ) ((n : ℝ)+1),
        dist (g x) (g y)≤C*|x-y| := by
    intro n hnA hnB x hx y hy
    have hlow : (R.lower k : ℝ)≤n := by exact_mod_cast hnA
    have hhigh : (n : ℝ)+1≤R.upper k := by exact_mod_cast hnB
    have hxR : x∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ) := ⟨hlow.trans hx.1,hx.2.trans hhigh⟩
    have hyR : y∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ) := ⟨hlow.trans hy.1,hy.2.trans hhigh⟩
    have hmid : ((n : ℝ)+1/2)∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ) := by constructor <;> linarith
    let w := Function.update z k ((n : ℝ)+1/2)
    let Q := T.pointCell w
    have hQ : Q∈T.cells := ⟨w,rfl⟩
    have hwR : w∈R.boundary := hline _ hmid
    have hrQ : Q.rank<R.rank := T.pointCell_rank_lt_cell_boundary hR hwR
    have hQR : Q.closedBox⊆R.closedBox := T.pointCell_subset_cell hR hwR.1
    have hwQ : w∈Q.closedBox := Q.relativeInterior_subset (T.mem_relativeInterior_pointCell w)
    have hxQ : Function.update z k x∈Q.closedBox := Q.coordinate_unit_interval z k n hwQ x hx
    have hyQ : Function.update z k y∈Q.closedBox := Q.coordinate_unit_interval z k n hwQ y hy
    change dist (F.boundaryCoordinateCurve hR z k hline x) (F.boundaryCoordinateCurve hR z k hline y)≤_
    rw [F.boundaryCoordinateCurve_eq hR z k hline x hxR,F.boundaryCoordinateCurve_eq hR z k hline y hyR]
    rw [F.boundaryValue_eq hR hQ hrQ hQR _ hxQ,F.boundaryValue_eq hR hQ hrQ hQR _ hyQ]
    rw [(cellIntervalInclude_isometry (m := m) (K := K) i hQR).dist_eq]
    exact hcoord Q hQ hrQ z x y hxQ hyQ
  have hLip := lipschitz_integer_clamped_intervals (R.lower k) (R.upper k) (R.ordered k) g C hunit
  have hh := hLip.dist_le_mul s t
  rw [integerIntervalClamp_eq hs,integerIntervalClamp_eq ht] at hh
  change dist (F.boundaryCoordinateCurve hR z k hline s) (F.boundaryCoordinateCurve hR z k hline t)≤_ at hh
  rw [F.boundaryCoordinateCurve_eq hR z k hline s hs,F.boundaryCoordinateCurve_eq hR z k hline t ht] at hh
  simpa only [Real.dist_eq] using hh

end LowerCellCarrierMaps
end
end AbelianTargets
