import AbelianTargets.IntegerPrismChart

/-! The actual relative cone filling on arbitrary integer rectangular
strata, including degenerate transverse coordinates. -/

namespace AbelianTargets
noncomputable section
open scoped unitInterval NNReal
variable {d : ℕ} {Z : Type*} [MetricSpace Z]

def prismBoundaryPoint (R : RectangularCell d) (i : Fin d)
    (v : ConeSphere (R.ActiveTransverse i → ℝ)) (r : unitInterval) : CellBoundaryDomain R :=
  ⟨(R.prismPoint i r ⟨v.val,v.property.le⟩).val,R.prismSphere_mem_boundary i r v⟩

theorem continuous_prismBoundaryPoint (R : RectangularCell d) (i : Fin d) :
    Continuous (fun z : ConeSphere (R.ActiveTransverse i → ℝ) × unitInterval =>
      prismBoundaryPoint R i z.1 z.2) := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun v : ConeSphere (R.ActiveTransverse i → ℝ) =>
      (⟨v.val,v.property.le⟩ : ConeBall (R.ActiveTransverse i → ℝ))) := continuous_subtype_val.subtype_mk _
  exact continuous_subtype_val.comp ((R.continuous_prismPoint i).comp
    (continuous_snd.prodMk (hc.comp continuous_fst)))

structure PrismBoundaryData (R : RectangularCell d) (i : Fin d) (p q : Z) (S B : ℝ≥0) where
  map : C(CellBoundaryDomain R,Z)
  source : ∀ z : CellBoundaryDomain R,z.val i=(R.lower i : ℝ) → map z=p
  target : ∀ z : CellBoundaryDomain R,z.val i=(R.upper i : ℝ) → map z=q
  path_lipschitz : ∀ v : ConeSphere (R.ActiveTransverse i → ℝ),
    LipschitzWith S (fun r => map (prismBoundaryPoint R i v r))
  transverse : ∀ r : unitInterval,LipschitzWith B
    (fun v : ConeSphere (R.ActiveTransverse i → ℝ) => map (prismBoundaryPoint R i v r))

namespace PrismBoundaryData
variable {R : RectangularCell d} {i : Fin d} {p q : Z} {S B : ℝ≥0}

def path (F : PrismBoundaryData R i p q S B) (v : ConeSphere (R.ActiveTransverse i → ℝ)) : Path p q where
  toFun r := F.map (prismBoundaryPoint R i v r)
  continuous_toFun := F.map.continuous.comp ((continuous_prismBoundaryPoint R i).comp
    (continuous_const.prodMk continuous_id))
  source' := F.source _ (by simp [prismBoundaryPoint,R.prismPoint_first])
  target' := F.target _ (by
    change (R.prismPoint i 1 ⟨v.val,v.property.le⟩).val i=(R.upper i : ℝ)
    rw [R.prismPoint_first]
    simp [RectangularCell.transverseWidth])

def pathFamily (F : PrismBoundaryData R i p q S B) :
    ControlledContraction.BoundaryPathFamily (E := R.ActiveTransverse i → ℝ) p q S B where
  path := F.path
  path_lipschitz := F.path_lipschitz
  transverse := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    apply (ContinuousMap.dist_le (mul_nonneg B.property dist_nonneg)).mpr
    intro r
    exact (F.transverse r).dist_le_mul v w

variable {D J : ℝ≥0} (H : ControlledContraction p D J)

def fill (F : PrismBoundaryData R i p q S B) (hi : R.lower i < R.upper i)
    (z : CellClosedDomain R) : Z :=
  H.coneValue F.pathFamily (R.normalizeTransverse i z) (R.firstIntervalParameter i hi z)

theorem continuous_fill (F : PrismBoundaryData R i p q S B) (hi : R.lower i < R.upper i) :
    Continuous (F.fill H hi) :=
  (H.continuous_coneValue F.pathFamily).comp
    ((R.continuous_normalizeTransverse i).prodMk (R.continuous_firstIntervalParameter i hi))

theorem fill_source (F : PrismBoundaryData R i p q S B) (hi : R.lower i < R.upper i)
    (z : CellClosedDomain R) (hz : z.val i=(R.lower i : ℝ)) : F.fill H hi z=p := by
  rw [fill,R.firstIntervalParameter_zero i hi z hz,H.coneValue_source]

theorem fill_target (F : PrismBoundaryData R i p q S B) (hi : R.lower i < R.upper i)
    (z : CellClosedDomain R) (hz : z.val i=(R.upper i : ℝ)) : F.fill H hi z=q := by
  rw [fill,R.firstIntervalParameter_one i hi z hz,H.coneValue_target]

theorem fill_boundary (F : PrismBoundaryData R i p q S B) (hi : R.lower i < R.upper i)
    (z : CellBoundaryDomain R) : F.fill H hi ⟨z.val,z.property.1⟩=F.map z := by
  by_cases hlo : z.val i=(R.lower i : ℝ)
  · rw [F.fill_source H hi _ hlo,F.source z hlo]
  · by_cases hhi : z.val i=(R.upper i : ℝ)
    · rw [F.fill_target H hi _ hhi,F.target z hhi]
    · let v : ConeSphere (R.ActiveTransverse i → ℝ) :=
        ⟨(R.normalizeTransverse i ⟨z.val,z.property.1⟩).val,R.normalizeTransverse_boundary i z hlo hhi⟩
      let r := R.firstIntervalParameter i hi ⟨z.val,z.property.1⟩
      have he : prismBoundaryPoint R i v r=z := by
        apply Subtype.ext
        exact congrArg (fun w : CellClosedDomain R => w.val)
          (R.prismPoint_inverse i hi ⟨z.val,z.property.1⟩)
      change H.coneValue F.pathFamily ⟨v.val,by rw [v.property]⟩ r=F.map z
      rw [H.coneValue_boundary]
      change F.map (prismBoundaryPoint R i v r)=F.map z
      rw [he]

def continuousMap (F : PrismBoundaryData R i p q S B) (hi : R.lower i < R.upper i) :
    C(CellClosedDomain R,Z) := ⟨F.fill H hi,F.continuous_fill H hi⟩

end PrismBoundaryData
end
end AbelianTargets
