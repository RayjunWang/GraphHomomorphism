import AbelianTargets.RectangularBoundaryStrata

/-! # Literal translation covariance of integer boundary strata -/

namespace AbelianTargets

noncomputable section

def translateCoordinates {d : ℕ} (a : Fin d → ℤ) (x : RealCoordinates d) : RealCoordinates d :=
  fun i => x i+(a i : ℝ)

@[simp] theorem translateCoordinates_neg_cancel {d : ℕ} (a : Fin d → ℤ) (x : RealCoordinates d) :
    translateCoordinates (-a) (translateCoordinates a x)=x := by
  funext i; simp [translateCoordinates]

@[simp] theorem translateCoordinates_cancel_neg {d : ℕ} (a : Fin d → ℤ) (x : RealCoordinates d) :
    translateCoordinates a (translateCoordinates (-a) x)=x := by
  funext i; simp [translateCoordinates]

namespace RectangularCell

variable {d : ℕ}

theorem mem_closedBox_translateCoordinates (R : RectangularCell d) (a : Fin d → ℤ)
    (x : RealCoordinates d) :
    translateCoordinates a x ∈ (R.translate a).closedBox ↔ x ∈ R.closedBox :=
  R.mem_closedBox_translate a x

@[simp] theorem translate_neg_cancel (R : RectangularCell d) (a : Fin d → ℤ) :
    (R.translate a).translate (-a)=R := by
  apply endpoint_pair_injective
  apply Prod.ext <;> funext i <;> simp [translate]

@[simp] theorem translate_cancel_neg (R : RectangularCell d) (a : Fin d → ℤ) :
    (R.translate (-a)).translate a=R := by
  apply endpoint_pair_injective
  apply Prod.ext <;> funext i <;> simp [translate]

theorem translate_injective (a : Fin d → ℤ) : Function.Injective (fun R : RectangularCell d => R.translate a) := by
  intro R Q h
  have hh := congrArg (fun S => S.translate (-a)) h
  simpa only [translate_neg_cancel] using hh

theorem mem_relativeInterior_translate (R : RectangularCell d) (a : Fin d → ℤ)
    (x : RealCoordinates d) :
    translateCoordinates a x ∈ (R.translate a).relativeInterior ↔ x ∈ R.relativeInterior := by
  simp [relativeInterior,translate,translateCoordinates]

theorem faceAt_translate (R : RectangularCell d) (a : Fin d → ℤ) (x : RealCoordinates d) :
    (R.translate a).faceAt (translateCoordinates a x)=(R.faceAt x).translate a := by
  apply endpoint_pair_injective
  apply Prod.ext <;> funext i
  · simp only [faceAt,translate,translateCoordinates,Int.cast_add,add_left_inj]
    split_ifs <;> rfl
  · simp only [faceAt,translate,translateCoordinates,Int.cast_add,add_left_inj]
    split_ifs <;> rfl

end RectangularCell

namespace IntegerRectangularTiling

variable {d : ℕ} {K : Fin d → ℕ}

def translate (T : IntegerRectangularTiling d K) (a : Fin d → ℤ) : IntegerRectangularTiling d K where
  tiles := (fun R => R.translate a) '' T.tiles
  positive := by
    rintro R ⟨Q,hQ,rfl⟩ i
    dsimp [RectangularCell.translate]
    have h := T.positive Q hQ i
    omega
  cover := by
    intro z
    obtain ⟨R,hR,hz⟩ := T.cover (translateCoordinates (-a) z)
    refine ⟨R.translate a,⟨R,hR,rfl⟩,?_⟩
    have hh := (R.mem_closedBox_translate a (translateCoordinates (-a) z)).mpr hz
    change translateCoordinates a (translateCoordinates (-a) z) ∈ (R.translate a).closedBox at hh
    simpa only [translateCoordinates_cancel_neg] using hh
  interior_unique := by
    rintro R ⟨P,hP,rfl⟩ Q ⟨U,hU,rfl⟩ ⟨z,hzP,hzU⟩
    have hp : translateCoordinates (-a) z ∈ P.relativeInterior := by
      apply (P.mem_relativeInterior_translate a _).mp
      simpa only [translateCoordinates_cancel_neg] using hzP
    have hu : translateCoordinates (-a) z ∈ U.relativeInterior := by
      apply (U.mem_relativeInterior_translate a _).mp
      simpa only [translateCoordinates_cancel_neg] using hzU
    rw [T.interior_unique P hP U hU ⟨_,hp,hu⟩]
  bounded := by
    rintro R ⟨Q,hQ,rfl⟩ i
    have h := T.bounded Q hQ i
    dsimp [RectangularCell.translate]
    omega

theorem pointCell_translate (T : IntegerRectangularTiling d K) (a : Fin d → ℤ)
    (x : RealCoordinates d) :
    (T.translate a).pointCell (translateCoordinates a x)=(T.pointCell x).translate a := by
  apply RectangularCell.closedBox_injective
  ext z
  change z ∈ ((T.translate a).pointCell (translateCoordinates a x)).closedBox ↔
    z ∈ ((T.pointCell x).translate a).closedBox
  let w := translateCoordinates (-a) z
  have hzw : translateCoordinates a w=z := translateCoordinates_cancel_neg a z
  rw [←hzw,(T.pointCell x).mem_closedBox_translateCoordinates a w]
  rw [(T.translate a).mem_pointCell,T.mem_pointCell]
  constructor
  · intro h R hR hxR
    have ht : R.translate a ∈ (T.translate a).tiles := ⟨R,hR,rfl⟩
    have hx : translateCoordinates a x ∈ (R.translate a).closedBox :=
      (R.mem_closedBox_translate a x).mpr hxR
    have hh := h (R.translate a) ht hx
    rw [RectangularCell.faceAt_translate] at hh
    exact ((R.faceAt x).mem_closedBox_translate a w).mp hh
  · rintro h R ⟨Q,hQ,rfl⟩ hxR
    have hx : x ∈ Q.closedBox := (Q.mem_closedBox_translate a x).mp hxR
    rw [RectangularCell.faceAt_translate]
    exact ((Q.faceAt x).mem_closedBox_translate a w).mpr (h Q hQ hx)

end IntegerRectangularTiling

end

end AbelianTargets
