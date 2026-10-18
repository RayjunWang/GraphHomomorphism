import AbelianTargets.AtlasRelativeCellExtension

namespace AbelianTargets
noncomputable section
variable {d : ℕ} {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d}

structure EndpointSkeletonCarrierMaps (T : IntegerRectangularTiling d K₀)
    (m K : ℕ) (i : Fin d) (n : ℕ) extends SkeletonCarrierMaps T m K i n where
  endpoints : ∀ (R : RectangularCell d) (hR : R∈T.cells) (hr : R.rank<n)
    (z : CellClosedDomain R),
    (z.val i=(R.lower i : ℝ) → map R hR hr z=cellLeftPoint m K i R) ∧
    (z.val i=(R.upper i : ℝ) → map R hR hr z=cellRightPoint m K i R)

namespace EndpointSkeletonCarrierMaps
variable {n : ℕ}

def empty : EndpointSkeletonCarrierMaps T m K i 0 where
  toSkeletonCarrierMaps := SkeletonCarrierMaps.empty
  endpoints R hR hr z := (Nat.not_lt_zero _ hr).elim

theorem lowerFamily_endpoints (F : EndpointSkeletonCarrierMaps T m K i n)
    (R : RectangularCell d) (he : R.rank=n) :
    (F.toSkeletonCarrierMaps.lowerFamily R he).EndpointValues := by
  intro Q hQ hr z
  exact F.endpoints Q hQ (by omega) z

variable (F : EndpointSkeletonCarrierMaps T m K i n)
variable (extend : ∀ (R : RectangularCell d) (hR : R∈T.cells) (he : R.rank=n),
  EndpointCellCarrierExtension (F.toSkeletonCarrierMaps.lowerFamily R he) hR)

def nextMap (R : RectangularCell d) (hR : R∈T.cells) (hr : R.rank<n+1) :
    C(CellClosedDomain R,CellIntervalCarrier m K i R) :=
  if h : R.rank<n then F.map R hR h else (extend R hR (by omega)).map

theorem nextMap_compatible (P Q : RectangularCell d) (hP : P∈T.cells) (hQ : Q∈T.cells)
    (hrP : P.rank<n+1) (hrQ : Q.rank<n+1) (hs : P.closedBox⊆Q.closedBox)
    (z : CellClosedDomain P) :
    cellIntervalInclude i hs (F.nextMap extend P hP hrP z)=
      F.nextMap extend Q hQ hrQ ⟨z.val,hs z.property⟩ := by
  by_cases hq : Q.rank<n
  · have hp : P.rank<n := (T.rank_le_of_cells_subset hP hQ hs).trans_lt hq
    simp only [nextMap,dif_pos hp,dif_pos hq]
    exact F.compatible P Q hP hQ hp hq hs z
  · have heq : Q.rank=n := by omega
    by_cases hp : P.rank<n
    · have hb : z.val∈Q.boundary := T.contained_cell_closed_subset_boundary hQ hP hs (by omega) z.property
      simp only [nextMap,dif_pos hp,dif_neg hq]
      rw [(extend Q hQ heq).boundary ⟨z.val,hb⟩]
      exact ((F.toSkeletonCarrierMaps.lowerFamily Q heq).boundaryValue_eq hQ hP
        (by omega) hs ⟨z.val,hb⟩ z.property).symm
    · have he : P=Q := by
        by_contra hne
        have hh := T.rank_lt_of_cells_subset_ne hP hQ hs hne
        omega
      subst P
      exact IntervalCarriers.intervalInclusion_self _

theorem nextMap_endpoints (R : RectangularCell d) (hR : R∈T.cells) (hr : R.rank<n+1)
    (z : CellClosedDomain R) :
    (z.val i=(R.lower i : ℝ) → F.nextMap extend R hR hr z=cellLeftPoint m K i R) ∧
    (z.val i=(R.upper i : ℝ) → F.nextMap extend R hR hr z=cellRightPoint m K i R) := by
  by_cases h : R.rank<n
  · simp only [nextMap,dif_pos h]
    exact F.endpoints R hR h z
  · simp only [nextMap,dif_neg h]
    exact ⟨(extend R hR (by omega)).source z,(extend R hR (by omega)).target z⟩

def next : EndpointSkeletonCarrierMaps T m K i (n+1) where
  map := F.nextMap extend
  compatible := F.nextMap_compatible extend
  endpoints := F.nextMap_endpoints extend

end EndpointSkeletonCarrierMaps
end
end AbelianTargets
