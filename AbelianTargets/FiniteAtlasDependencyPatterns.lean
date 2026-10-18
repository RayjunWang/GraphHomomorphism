import AbelianTargets.ContinuousAtlasPatterns

/-! A finite atlas pattern containing every boundary dependency of every
cell through a fixed spatial point. The universe includes all subcells,
even when their boundary is far from the fixed point. -/

namespace AbelianTargets
noncomputable section
open Filter Topology
namespace RectangularCell
variable {d : ℕ}

def dependencyUniverse (K : Fin d→ℕ) (z : RealCoordinates d) : Finset (RectangularCell d) :=
  (finite_bounded_endpoints (fun i=>Int.ceil (z i-(K i:ℝ)))
    (fun i=>Int.floor (z i+(K i:ℝ)))).toFinset

theorem subcell_mem_dependencyUniverse (K : Fin d→ℕ) (z : RealCoordinates d)
    (R Q : RectangularCell d) (hR : HasBoundedSides K R)
    (hz : z∈R.closedBox) (hsub : Q.closedBox⊆R.closedBox) :
    Q∈dependencyUniverse K z := by
  rw [dependencyUniverse,Set.Finite.mem_toFinset]
  intro i
  have hs := (closedBox_subset_iff Q R).mp hsub i
  have hh := hz i
  have hd : (R.upper i:ℝ)-(R.lower i:ℝ)≤(K i:ℝ) := by exact_mod_cast hR i
  have hlo : z i-(K i:ℝ)≤(R.lower i:ℝ) := by linarith
  have hhi : (R.upper i:ℝ)≤z i+(K i:ℝ) := by linarith
  have ha : Int.ceil (z i-(K i:ℝ))≤R.lower i := Int.ceil_le.mpr hlo
  have hb : R.upper i≤Int.floor (z i+(K i:ℝ)) := Int.le_floor.mpr hhi
  exact ⟨ha.trans hs.1,(Q.ordered i).trans (hs.2.trans hb),
    (ha.trans hs.1).trans (Q.ordered i),hs.2.trans hb⟩

end RectangularCell
namespace IntegerRectangularTiling
variable {d : ℕ} {K : Fin d→ℕ}

def dependencyPattern (T : IntegerRectangularTiling d K) (z : RealCoordinates d) :
    Finset (RectangularCell d) := by
  classical
  exact (RectangularCell.dependencyUniverse K z).filter (fun R=>R∈T.cells)

theorem subcell_mem_dependencyPattern (T : IntegerRectangularTiling d K)
    (z : RealCoordinates d) (R Q : RectangularCell d) (hR : R∈T.cells)
    (hQ : Q∈T.cells) (hz : z∈R.closedBox) (hsub : Q.closedBox⊆R.closedBox) :
    Q∈T.dependencyPattern z := by
  classical
  exact Finset.mem_filter.mpr ⟨RectangularCell.subcell_mem_dependencyUniverse
    K z R Q (T.cells_bounded hR) hz hsub,hQ⟩

theorem dependencyPattern_isLocallyConstant {Y : Type*} [TopologicalSpace Y]
    (T : Y→IntegerRectangularTiling d K)
    (hlocal : ∀ R x,∀ᶠ y in 𝓝 x,R∈(T y).tiles ↔ R∈(T x).tiles)
    (z : RealCoordinates d) : IsLocallyConstant (fun x=>(T x).dependencyPattern z) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [finite_cells_eventually_eq T hlocal (RectangularCell.dependencyUniverse K z) x]
    with y hy
  exact Finset.filter_congr hy

theorem dependencyPattern_finite_range {Y : Type*} (T : Y→IntegerRectangularTiling d K)
    (z : RealCoordinates d) : (Set.range (fun x=>(T x).dependencyPattern z)).Finite := by
  classical
  apply (RectangularCell.dependencyUniverse K z).powerset.finite_toSet.subset
  rintro _ ⟨x,rfl⟩
  exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)

theorem dependencyPattern_function_isLocallyConstant {Y Z : Type*} [TopologicalSpace Y]
    (T : Y→IntegerRectangularTiling d K)
    (hlocal : ∀ R x,∀ᶠ y in 𝓝 x,R∈(T y).tiles ↔ R∈(T x).tiles)
    (z : RealCoordinates d) (f : Finset (RectangularCell d)→Z) :
    IsLocallyConstant (fun x=>f ((T x).dependencyPattern z)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [(dependencyPattern_isLocallyConstant T hlocal z).eventually_eq x] with y hy
  exact congrArg f hy

theorem dependencyPattern_function_finite_range {Y Z : Type*}
    (T : Y→IntegerRectangularTiling d K) (z : RealCoordinates d)
    (f : Finset (RectangularCell d)→Z) :
    (Set.range (fun x=>f ((T x).dependencyPattern z))).Finite := by
  exact ((dependencyPattern_finite_range T z).image f).subset
    (by rintro _ ⟨x,rfl⟩; exact ⟨(T x).dependencyPattern z,⟨x,rfl⟩,rfl⟩)

end IntegerRectangularTiling
end
end AbelianTargets
