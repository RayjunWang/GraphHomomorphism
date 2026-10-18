import AbelianTargets.IntegerPrismChart
import AbelianTargets.RectangularTranslation

set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets.RectangularCell
noncomputable section
open scoped unitInterval
variable {d : ℕ}

def activeTranslationEquiv (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d) :
    R.ActiveTransverse i ≃ (R.translate a).ActiveTransverse i where
  toFun j := ⟨j.val,j.property.1,by simpa [translate] using j.property.2⟩
  invFun j := ⟨j.val,j.property.1,by simpa [translate] using j.property.2⟩
  left_inv j := rfl
  right_inv j := rfl

def activeFunctionTranslation (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d) :
    (R.ActiveTransverse i→ℝ) ≃ᵢ ((R.translate a).ActiveTransverse i→ℝ) :=
  IsometryEquiv.piCongrLeft' (Y := fun _=>ℝ) (R.activeTranslationEquiv a i)

theorem activeFunctionTranslation_norm (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d)
    (v : R.ActiveTransverse i→ℝ) : ‖R.activeFunctionTranslation a i v‖=‖v‖ := by
  have hzero : R.activeFunctionTranslation a i 0=0 := rfl
  simpa only [hzero,dist_zero_right] using (R.activeFunctionTranslation a i).dist_eq v 0

def activeLinearTranslation (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d) :
    (R.ActiveTransverse i→ℝ) ≃ₗᵢ[ℝ] ((R.translate a).ActiveTransverse i→ℝ) where
  toLinearEquiv := LinearEquiv.piCongrLeft' ℝ (fun _=>ℝ) (R.activeTranslationEquiv a i)
  norm_map' v := R.activeFunctionTranslation_norm a i v

def translateConeBall (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d)
    (v : ConeBall (R.ActiveTransverse i→ℝ)) : ConeBall ((R.translate a).ActiveTransverse i→ℝ) :=
  ⟨R.activeFunctionTranslation a i v.val,by rw [R.activeFunctionTranslation_norm];exact v.property⟩

def translateConeSphere (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d)
    (v : ConeSphere (R.ActiveTransverse i→ℝ)) : ConeSphere ((R.translate a).ActiveTransverse i→ℝ) :=
  ⟨R.activeFunctionTranslation a i v.val,by rw [R.activeFunctionTranslation_norm];exact v.property⟩

@[simp] theorem transverseWidth_translate (R : RectangularCell d) (a : Fin d→ℤ) (j : Fin d) :
    (R.translate a).transverseWidth j=R.transverseWidth j := by
  simp [transverseWidth,translate]

theorem prismCoordinates_translate (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d)
    (r : I) (v : ConeBall (R.ActiveTransverse i→ℝ)) :
    (R.translate a).prismCoordinates i r (R.translateConeBall a i v)=
      translateCoordinates a (R.prismCoordinates i r v) := by
  funext j
  change (R.translate a).prismCoordinates i r (R.translateConeBall a i v) j=
    R.prismCoordinates i r v j+(a j : ℝ)
  by_cases hji : j=i
  · subst j
    simp only [prismCoordinates,dif_pos rfl,transverseWidth_translate]
    dsimp [translate]
    push_cast
    ring
  · by_cases hpos : R.lower j<R.upper j
    · have hpos' : (R.translate a).lower j<(R.translate a).upper j := by simpa [translate] using hpos
      simp only [prismCoordinates,dif_neg hji,dif_pos hpos,dif_pos hpos',transverseWidth_translate]
      change (((R.lower j+a j : ℤ) : ℝ)+((R.upper j+a j : ℤ) : ℝ))/2+
        R.transverseWidth j/2*v.val ⟨j,hji,hpos⟩=
        ((R.lower j : ℝ)+(R.upper j : ℝ))/2+R.transverseWidth j/2*v.val ⟨j,hji,hpos⟩+(a j : ℝ)
      push_cast
      ring
    · have hpos' : ¬(R.translate a).lower j<(R.translate a).upper j := by simpa [translate] using hpos
      simp [prismCoordinates,hji,hpos,hpos',translate,translateCoordinates]

def translateClosedPoint (R : RectangularCell d) (a : Fin d→ℤ) (z : CellClosedDomain R) :
    CellClosedDomain (R.translate a) :=
  ⟨translateCoordinates a z.val,(R.mem_closedBox_translateCoordinates a z.val).mpr z.property⟩

def translateBoundaryPoint (R : RectangularCell d) (a : Fin d→ℤ) (z : CellBoundaryDomain R) :
    CellBoundaryDomain (R.translate a) :=
  ⟨translateCoordinates a z.val,
    (R.mem_closedBox_translateCoordinates a z.val).mpr z.property.1,
    fun h => z.property.2 ((R.mem_relativeInterior_translate a z.val).mp h)⟩

theorem prismPoint_translate (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d)
    (r : I) (v : ConeBall (R.ActiveTransverse i→ℝ)) :
    (R.translate a).prismPoint i r (R.translateConeBall a i v)=
      R.translateClosedPoint a (R.prismPoint i r v) :=
  Subtype.ext (R.prismCoordinates_translate a i r v)

theorem normalizeTransverse_translate (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d)
    (z : CellClosedDomain R) :
    (R.translate a).normalizeTransverse i (R.translateClosedPoint a z)=
      R.translateConeBall a i (R.normalizeTransverse i z) := by
  apply Subtype.ext
  funext j
  simp only [normalizeTransverse,transverseWidth_translate]
  change (2*(z.val j.val+(a j.val : ℝ))-((R.lower j.val+a j.val : ℤ) : ℝ)-
      ((R.upper j.val+a j.val : ℤ) : ℝ))/R.transverseWidth j.val=
      (2*z.val j.val-(R.lower j.val : ℝ)-(R.upper j.val : ℝ))/R.transverseWidth j.val
  push_cast
  ring

theorem firstIntervalParameter_translate (R : RectangularCell d) (a : Fin d→ℤ) (i : Fin d)
    (hi : R.lower i<R.upper i) (z : CellClosedDomain R) :
    (R.translate a).firstIntervalParameter i (by simpa [translate] using hi) (R.translateClosedPoint a z)=
      R.firstIntervalParameter i hi z := by
  apply Subtype.ext
  simp only [firstIntervalParameter,transverseWidth_translate]
  change (z.val i+(a i : ℝ)-((R.lower i+a i : ℤ) : ℝ))/R.transverseWidth i=
    (z.val i-(R.lower i : ℝ))/R.transverseWidth i
  push_cast
  ring

end
end AbelianTargets.RectangularCell
