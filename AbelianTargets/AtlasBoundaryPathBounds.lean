import AbelianTargets.AtlasBoundaryCoordinateBounds
import AbelianTargets.IntegerPrismFilling

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! The subdivided cell boundary retains its controlled first path variable. -/
namespace AbelianTargets
open scoped NNReal unitInterval
noncomputable section

theorem prismBoundaryPoint_first_update {d : ℕ} (R : RectangularCell d) (i : Fin d)
    (v : ConeSphere (R.ActiveTransverse i → ℝ)) (r : I) :
    (prismBoundaryPoint R i v r).val=Function.update (prismBoundaryPoint R i v 0).val i
      ((R.lower i : ℝ)+R.transverseWidth i*r) := by
  funext j
  by_cases hji : j=i
  · subst j
    simp [prismBoundaryPoint,RectangularCell.prismPoint,RectangularCell.prismCoordinates]
  · simp only [prismBoundaryPoint,RectangularCell.prismPoint,RectangularCell.prismCoordinates,
      dif_neg hji,Function.update_of_ne hji]

theorem prism_first_boundary_line {d : ℕ} (R : RectangularCell d) (i : Fin d)
    (hi : R.lower i<R.upper i) (v : ConeSphere (R.ActiveTransverse i → ℝ)) :
    ∀ s∈Set.Icc (R.lower i : ℝ) (R.upper i : ℝ),
      Function.update (prismBoundaryPoint R i v 0).val i s∈R.boundary := by
  intro s hs
  have hw : 0<R.transverseWidth i := sub_pos.mpr (by exact_mod_cast hi)
  let r : I := ⟨(s-(R.lower i : ℝ))/R.transverseWidth i,by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hs.1) hw.le
    · apply (div_le_iff₀ hw).mpr
      dsimp [RectangularCell.transverseWidth]
      linarith [hs.2]⟩
  have he : (R.lower i : ℝ)+R.transverseWidth i*r=s := by
    dsimp [r]; field_simp; ring
  have hp := (prismBoundaryPoint R i v r).property
  rw [prismBoundaryPoint_first_update,he] at hp
  exact hp

namespace LowerCellCarrierMaps
variable {d : ℕ} {K₀ : Fin d → ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d} {R : RectangularCell d}

theorem prism_path_lipschitz (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (hi : R.lower i<R.upper i) (C : ℝ≥0)
    (hcoord : ∀ (Q : RectangularCell d) (hQ : Q∈T.cells) (hrQ : Q.rank<R.rank)
      (w : RealCoordinates d) (x y : ℝ)
      (hx : Function.update w i x∈Q.closedBox) (hy : Function.update w i y∈Q.closedBox),
      dist (F.map Q hQ hrQ ⟨Function.update w i x,hx⟩)
        (F.map Q hQ hrQ ⟨Function.update w i y,hy⟩)≤C*|x-y|)
    (v : ConeSphere (R.ActiveTransverse i → ℝ)) :
    LipschitzWith (C*(R.transverseWidth i).toNNReal)
      (fun r : I => F.boundaryValue hR (prismBoundaryPoint R i v r)) := by
  have hw : 0<R.transverseWidth i := sub_pos.mpr (by exact_mod_cast hi)
  let z := (prismBoundaryPoint R i v 0).val
  have hline := prism_first_boundary_line R i hi v
  let x : I→ℝ := fun r => (R.lower i : ℝ)+R.transverseWidth i*r
  have hx : ∀ r : I,x r∈Set.Icc (R.lower i : ℝ) (R.upper i : ℝ) := by
    intro r
    have hr := (prismBoundaryPoint R i v r).property.1 i
    simpa only [prismBoundaryPoint,RectangularCell.prismPoint_first] using hr
  have hp : ∀ r : I,prismBoundaryPoint R i v r=⟨Function.update z i (x r),hline _ (hx r)⟩ := by
    intro r; apply Subtype.ext
    exact prismBoundaryPoint_first_update R i v r
  apply LipschitzWith.of_dist_le_mul
  intro r s
  have hh := F.boundary_coordinate_dist_le hR i C hcoord z hline (x r) (x s) (hx r) (hx s)
  rw [←hp r,←hp s] at hh
  have he : |x r-x s|=R.transverseWidth i*dist r s := by
    have he' : x r-x s=R.transverseWidth i*((r : ℝ)-(s : ℝ)) := by dsimp [x]; ring
    rw [he',abs_mul,abs_of_pos hw]
    rfl
  rw [he] at hh
  simpa only [NNReal.coe_mul,Real.coe_toNNReal _ hw.le,mul_assoc] using hh

end LowerCellCarrierMaps
end
end AbelianTargets
