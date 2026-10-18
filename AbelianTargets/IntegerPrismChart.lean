import AbelianTargets.AtlasRankRecursion
import AbelianTargets.RectangularCone

/-! Literal active-coordinate prism charts for possibly degenerate atlas
cells. The first coordinate retains its own interval parameter. -/

namespace AbelianTargets
noncomputable section
open scoped unitInterval
namespace RectangularCell
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

abbrev ActiveTransverse (R : RectangularCell d) (i : Fin d) :=
  {j : Fin d // j ≠ i ∧ R.lower j < R.upper j}

instance (R : RectangularCell d) (i : Fin d) : Fintype (R.ActiveTransverse i) := Fintype.ofFinite _

def transverseWidth (R : RectangularCell d) (j : Fin d) : ℝ :=
  (R.upper j : ℝ)-(R.lower j : ℝ)

theorem transverseWidth_pos (R : RectangularCell d) (i : Fin d) (j : R.ActiveTransverse i) :
    0 < R.transverseWidth j.val := by
  exact sub_pos.mpr (by exact_mod_cast j.property.2)

def prismCoordinates (R : RectangularCell d) (i : Fin d)
    (r : unitInterval) (v : ConeBall (R.ActiveTransverse i → ℝ)) : RealCoordinates d :=
  fun j => if hji : j=i then (R.lower j : ℝ)+R.transverseWidth j*r
    else if hpos : R.lower j < R.upper j then
      ((R.lower j : ℝ)+(R.upper j : ℝ))/2+R.transverseWidth j/2*v.val ⟨j,hji,hpos⟩
    else (R.lower j : ℝ)

theorem prismCoordinates_mem (R : RectangularCell d) (i : Fin d)
    (r : unitInterval) (v : ConeBall (R.ActiveTransverse i → ℝ)) :
    R.prismCoordinates i r v ∈ R.closedBox := by
  intro j
  have ho : (R.lower j : ℝ) ≤ (R.upper j : ℝ) := by exact_mod_cast R.ordered j
  have hw : 0 ≤ R.transverseWidth j := sub_nonneg.mpr ho
  by_cases hji : j=i
  · simp only [prismCoordinates,dif_pos hji]
    have h₀ := mul_nonneg hw r.property.1
    have h₁ := mul_le_mul_of_nonneg_left r.property.2 hw
    dsimp [transverseWidth] at *
    constructor <;> linarith
  · by_cases hpos : R.lower j < R.upper j
    · simp only [prismCoordinates,dif_neg hji,dif_pos hpos]
      have hv := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp v.property ⟨j,hji,hpos⟩
      rw [Real.norm_eq_abs,abs_le] at hv
      have h₀ := mul_le_mul_of_nonneg_left hv.1 (show 0 ≤ R.transverseWidth j/2 by positivity)
      have h₁ := mul_le_mul_of_nonneg_left hv.2 (show 0 ≤ R.transverseWidth j/2 by positivity)
      dsimp [transverseWidth] at *
      constructor <;> linarith
    · simp only [prismCoordinates,dif_neg hji,dif_neg hpos]
      exact ⟨le_rfl,ho⟩

def prismPoint (R : RectangularCell d) (i : Fin d)
    (r : unitInterval) (v : ConeBall (R.ActiveTransverse i → ℝ)) : CellClosedDomain R :=
  ⟨R.prismCoordinates i r v,R.prismCoordinates_mem i r v⟩

theorem continuous_prismPoint (R : RectangularCell d) (i : Fin d) :
    Continuous (fun z : unitInterval × ConeBall (R.ActiveTransverse i → ℝ) => R.prismPoint i z.1 z.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  by_cases hji : j=i
  · simp only [prismPoint,prismCoordinates,dif_pos hji]
    fun_prop
  · by_cases hpos : R.lower j < R.upper j
    · simp only [prismPoint,prismCoordinates,dif_neg hji,dif_pos hpos]
      exact continuous_const.add (continuous_const.mul
        ((continuous_apply (⟨j,hji,hpos⟩ : R.ActiveTransverse i)).comp
          (continuous_subtype_val.comp continuous_snd)))
    · simp only [prismPoint,prismCoordinates,dif_neg hji,dif_neg hpos]
      exact continuous_const

def normalizeTransverse (R : RectangularCell d) (i : Fin d) (z : CellClosedDomain R) :
    ConeBall (R.ActiveTransverse i → ℝ) :=
  ⟨fun j => (2*z.val j.val-(R.lower j.val : ℝ)-(R.upper j.val : ℝ))/R.transverseWidth j.val,by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro j
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (R.transverseWidth_pos i j)]
    apply (div_le_iff₀ (R.transverseWidth_pos i j)).mpr
    rw [one_mul,abs_le]
    have hz := z.property j.val
    dsimp [transverseWidth]
    constructor <;> linarith⟩

theorem continuous_normalizeTransverse (R : RectangularCell d) (i : Fin d) :
    Continuous (R.normalizeTransverse i) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact ((continuous_const.mul ((continuous_apply j.val).comp continuous_subtype_val)).sub
    continuous_const |>.sub continuous_const).div_const _

def firstIntervalParameter (R : RectangularCell d) (i : Fin d)
    (hi : R.lower i < R.upper i) (z : CellClosedDomain R) : unitInterval :=
  ⟨(z.val i-(R.lower i : ℝ))/R.transverseWidth i,by
    have hw : 0 < R.transverseWidth i := sub_pos.mpr (by exact_mod_cast hi)
    constructor
    · exact div_nonneg (sub_nonneg.mpr (z.property i).1) hw.le
    · apply (div_le_iff₀ hw).mpr
      have hz := (z.property i).2
      dsimp [transverseWidth]
      linarith⟩

theorem continuous_firstIntervalParameter (R : RectangularCell d) (i : Fin d)
    (hi : R.lower i < R.upper i) : Continuous (R.firstIntervalParameter i hi) := by
  apply Continuous.subtype_mk
  exact (((continuous_apply i).comp continuous_subtype_val).sub continuous_const).div_const _

theorem prismPoint_inverse (R : RectangularCell d) (i : Fin d)
    (hi : R.lower i < R.upper i) (z : CellClosedDomain R) :
    R.prismPoint i (R.firstIntervalParameter i hi z) (R.normalizeTransverse i z)=z := by
  apply Subtype.ext
  funext j
  by_cases hji : j=i
  · subst j
    simp [prismPoint,prismCoordinates,firstIntervalParameter]
    have hw : R.transverseWidth i ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hi))
    field_simp
    ring
  · by_cases hpos : R.lower j < R.upper j
    · simp only [prismPoint,prismCoordinates,dif_neg hji,dif_pos hpos,normalizeTransverse]
      have hw : R.transverseWidth j ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hpos))
      dsimp [transverseWidth] at *
      field_simp
      ring
    · simp only [prismPoint,prismCoordinates,dif_neg hji,dif_neg hpos]
      have he : R.lower j=R.upper j := le_antisymm (R.ordered j) (le_of_not_gt hpos)
      have hz := z.property j
      exact le_antisymm hz.1 (by simpa only [← he] using hz.2)

theorem normalizeTransverse_prismPoint (R : RectangularCell d) (i : Fin d)
    (r : unitInterval) (v : ConeBall (R.ActiveTransverse i → ℝ)) :
    R.normalizeTransverse i (R.prismPoint i r v)=v := by
  apply Subtype.ext
  funext j
  have hw := R.transverseWidth_pos i j
  simp only [normalizeTransverse,prismPoint,prismCoordinates,dif_neg j.property.1,dif_pos j.property.2]
  dsimp [transverseWidth] at *
  field_simp
  ring

theorem prismSphere_mem_boundary (R : RectangularCell d) (i : Fin d)
    (r : unitInterval) (v : ConeSphere (R.ActiveTransverse i → ℝ)) :
    (R.prismPoint i r ⟨v.val,v.property.le⟩).val ∈ R.boundary := by
  refine ⟨(R.prismPoint i r ⟨v.val,v.property.le⟩).property,?_⟩
  intro hrel
  have hnorm : ‖v.val‖ < 1 := (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr (by
    intro j
    have hz := hrel j.val
    simp only [relativeInterior,ne_of_lt j.property.2,if_false] at hz
    simp only [prismPoint,prismCoordinates,dif_neg j.property.1,dif_pos j.property.2] at hz
    rw [Real.norm_eq_abs,abs_lt]
    have hw := R.transverseWidth_pos i j
    dsimp [transverseWidth] at *
    have hlow : -(R.transverseWidth j.val) < R.transverseWidth j.val*v.val j := by
      dsimp [transverseWidth]
      linarith
    have hup : R.transverseWidth j.val*v.val j < R.transverseWidth j.val := by
      dsimp [transverseWidth]
      linarith
    constructor
    · apply lt_of_mul_lt_mul_left ?_ hw.le
      simpa only [mul_neg,mul_one] using hlow
    · apply lt_of_mul_lt_mul_left ?_ hw.le
      simpa only [mul_one] using hup)
  rw [v.property] at hnorm
  exact (lt_irrefl _) hnorm

theorem prismPoint_first (R : RectangularCell d) (i : Fin d)
    (r : unitInterval) (v : ConeBall (R.ActiveTransverse i → ℝ)) :
    (R.prismPoint i r v).val i=(R.lower i : ℝ)+R.transverseWidth i*r := by
  simp [prismPoint,prismCoordinates]

theorem firstIntervalParameter_zero (R : RectangularCell d) (i : Fin d)
    (hi : R.lower i < R.upper i) (z : CellClosedDomain R)
    (hz : z.val i=(R.lower i : ℝ)) : R.firstIntervalParameter i hi z=0 := by
  apply Subtype.ext
  simp [firstIntervalParameter,hz]

theorem firstIntervalParameter_one (R : RectangularCell d) (i : Fin d)
    (hi : R.lower i < R.upper i) (z : CellClosedDomain R)
    (hz : z.val i=(R.upper i : ℝ)) : R.firstIntervalParameter i hi z=1 := by
  apply Subtype.ext
  have hw : R.transverseWidth i ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hi))
  change (z.val i-(R.lower i : ℝ))/R.transverseWidth i=1
  rw [hz]
  exact div_self hw

theorem normalizeTransverse_boundary (R : RectangularCell d) (i : Fin d)
    (z : CellBoundaryDomain R)
    (hlo : z.val i ≠ (R.lower i : ℝ)) (hhi : z.val i ≠ (R.upper i : ℝ)) :
    ‖(R.normalizeTransverse i ⟨z.val,z.property.1⟩).val‖=1 := by
  obtain ⟨j,hj,hend⟩ := R.boundary_has_endpoint z.property
  have hji : j ≠ i := by
    intro he
    subst j
    rcases hend with he | he
    · exact hlo he
    · exact hhi he
  let jt : R.ActiveTransverse i := ⟨j,hji,hj⟩
  let v := R.normalizeTransverse i ⟨z.val,z.property.1⟩
  have hw := R.transverseWidth_pos i jt
  have hwidth : (R.upper j : ℝ) - (R.lower j : ℝ) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hj))
  have hv : v.val jt=-1 ∨ v.val jt=1 := by
    rcases hend with he | he
    · left
      dsimp [v,normalizeTransverse,jt]
      rw [he]
      dsimp [transverseWidth]
      field_simp [hwidth]
      ring
    · right
      dsimp [v,normalizeTransverse,jt]
      rw [he]
      dsimp [transverseWidth]
      field_simp [hwidth]
      ring
  apply le_antisymm v.property
  have hle := (pi_norm_le_iff_of_nonneg (norm_nonneg v.val)).mp le_rfl jt
  rcases hv with hv | hv <;> simpa [hv] using hle

end RectangularCell
end
end AbelianTargets
