import AbelianTargets.AtlasBoundaryCarrierMaps

/-! Rank recursion for actual atlas cells and literal interval carriers.
The local extension operator remains an explicit input; this module proves
the global compatibility bookkeeping and never assumes a global orbit map. -/

namespace AbelianTargets
noncomputable section
namespace IntegerRectangularTiling
variable {d : ℕ} {K₀ : Fin d → ℕ} (T : IntegerRectangularTiling d K₀)

theorem rank_lt_of_cells_subset_ne {P Q : RectangularCell d}
    (hP : P ∈ T.cells) (hQ : Q ∈ T.cells) (hsub : P.closedBox ⊆ Q.closedBox)
    (hne : P ≠ Q) : P.rank < Q.rank := by
  obtain ⟨z,hzP⟩ := P.relativeInterior_nonempty
  by_cases hzQ : z ∈ Q.relativeInterior
  · exact (hne (T.relativeInterior_unique hP hQ ⟨z,hzP,hzQ⟩)).elim
  · exact P.rank_lt_of_relativeInterior_on_boundary Q hsub hzP
      ⟨hsub (P.relativeInterior_subset hzP),hzQ⟩

theorem rank_le_of_cells_subset {P Q : RectangularCell d}
    (hP : P ∈ T.cells) (hQ : Q ∈ T.cells) (hsub : P.closedBox ⊆ Q.closedBox) : P.rank ≤ Q.rank := by
  by_cases he : P=Q
  · subst P; exact le_rfl
  · exact (T.rank_lt_of_cells_subset_ne hP hQ hsub he).le

end IntegerRectangularTiling

variable {d : ℕ} {K₀ : Fin d → ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d}

structure CellCarrierExtension {R : RectangularCell d}
    (F : LowerCellCarrierMaps T m K i R) (hR : R ∈ T.cells) where
  map : C(CellClosedDomain R,CellIntervalCarrier m K i R)
  boundary : ∀ z : CellBoundaryDomain R,map ⟨z.val,z.property.1⟩=F.boundaryValue hR z

structure SkeletonCarrierMaps (T : IntegerRectangularTiling d K₀) (m K : ℕ) (i : Fin d) (n : ℕ) where
  map : ∀ R : RectangularCell d,R ∈ T.cells → R.rank < n →
    C(CellClosedDomain R,CellIntervalCarrier m K i R)
  compatible : ∀ (P Q : RectangularCell d) (hP : P ∈ T.cells) (hQ : Q ∈ T.cells)
    (hrP : P.rank < n) (hrQ : Q.rank < n) (hsub : P.closedBox ⊆ Q.closedBox)
    (z : CellClosedDomain P),
    cellIntervalInclude i hsub (map P hP hrP z)=map Q hQ hrQ ⟨z.val,hsub z.property⟩

namespace SkeletonCarrierMaps
variable {n : ℕ}

def empty : SkeletonCarrierMaps T m K i 0 where
  map R hR hr := (Nat.not_lt_zero R.rank hr).elim
  compatible P Q hP hQ hrP hrQ hs z := (Nat.not_lt_zero P.rank hrP).elim

def lowerFamily (F : SkeletonCarrierMaps T m K i n) (R : RectangularCell d)
    (he : R.rank=n) : LowerCellCarrierMaps T m K i R where
  map Q hQ hr := F.map Q hQ (by omega)
  compatible P Q hP hQ hrP hrQ hs z := F.compatible P Q hP hQ (by omega) (by omega) hs z

variable (extend : ∀ (R : RectangularCell d) (hR : R ∈ T.cells)
  (F : LowerCellCarrierMaps T m K i R),CellCarrierExtension F hR)

def nextMap (F : SkeletonCarrierMaps T m K i n) (R : RectangularCell d)
    (hR : R ∈ T.cells) (hr : R.rank < n+1) : C(CellClosedDomain R,CellIntervalCarrier m K i R) :=
  if h : R.rank < n then F.map R hR h else (extend R hR (F.lowerFamily R (by omega))).map

theorem nextMap_compatible (F : SkeletonCarrierMaps T m K i n)
    (P Q : RectangularCell d) (hP : P ∈ T.cells) (hQ : Q ∈ T.cells)
    (hrP : P.rank < n+1) (hrQ : Q.rank < n+1) (hs : P.closedBox ⊆ Q.closedBox)
    (z : CellClosedDomain P) :
    cellIntervalInclude i hs (F.nextMap extend P hP hrP z)=
      F.nextMap extend Q hQ hrQ ⟨z.val,hs z.property⟩ := by
  by_cases hq : Q.rank < n
  · have hp : P.rank < n := (T.rank_le_of_cells_subset hP hQ hs).trans_lt hq
    simp only [nextMap,dif_pos hp,dif_pos hq]
    exact F.compatible P Q hP hQ hp hq hs z
  · have heq : Q.rank=n := by omega
    by_cases hp : P.rank < n
    · have hb : z.val ∈ Q.boundary := T.contained_cell_closed_subset_boundary hQ hP hs
        (by omega) z.property
      simp only [nextMap,dif_pos hp,dif_neg hq]
      rw [(extend Q hQ (F.lowerFamily Q heq)).boundary ⟨z.val,hb⟩]
      exact ((F.lowerFamily Q heq).boundaryValue_eq hQ hP (by omega) hs ⟨z.val,hb⟩ z.property).symm
    · have he : P=Q := by
        by_contra hne
        have hh := T.rank_lt_of_cells_subset_ne hP hQ hs hne
        omega
      subst P
      exact IntervalCarriers.intervalInclusion_self _

def next (F : SkeletonCarrierMaps T m K i n) : SkeletonCarrierMaps T m K i (n+1) where
  map := F.nextMap extend
  compatible := F.nextMap_compatible extend

def build : (n : ℕ) → SkeletonCarrierMaps T m K i n
  | 0 => empty
  | n+1 => (build n).next extend

end SkeletonCarrierMaps

theorem exists_compatible_cellCarrierMaps
    (extend : ∀ (R : RectangularCell d) (hR : R ∈ T.cells)
      (F : LowerCellCarrierMaps T m K i R),CellCarrierExtension F hR) :
    Nonempty (SkeletonCarrierMaps T m K i (d+1)) :=
  ⟨SkeletonCarrierMaps.build extend (d+1)⟩

end
end AbelianTargets
