import AbelianTargets.IntegerPrismFilling

namespace AbelianTargets
noncomputable section
open scoped unitInterval NNReal
variable {d : ℕ}

namespace RectangularCell

theorem normalizeTransverse_eq_of_except_first (R : RectangularCell d) (i : Fin d)
    (z z' : CellClosedDomain R) (heq : ∀ j,j≠i → z.val j=z'.val j) :
    R.normalizeTransverse i z=R.normalizeTransverse i z' := by
  apply Subtype.ext
  funext j
  simp only [normalizeTransverse,heq j.val j.property.1]

theorem firstIntervalParameter_dist (R : RectangularCell d) (i : Fin d)
    (hi : R.lower i<R.upper i) (z z' : CellClosedDomain R) :
    dist (R.firstIntervalParameter i hi z) (R.firstIntervalParameter i hi z')=
      |z.val i-z'.val i|/R.transverseWidth i := by
  have hw : 0<R.transverseWidth i := sub_pos.mpr (by exact_mod_cast hi)
  rw [Subtype.dist_eq,Real.dist_eq]
  change |(z.val i-(R.lower i : ℝ))/R.transverseWidth i-
      (z'.val i-(R.lower i : ℝ))/R.transverseWidth i|=_
  rw [←sub_div,show z.val i-(R.lower i : ℝ)-(z'.val i-(R.lower i : ℝ))=
    z.val i-z'.val i by ring,abs_div,abs_of_pos hw]

theorem firstIntervalParameter_eq (R : RectangularCell d) (i : Fin d)
    (hi : R.lower i<R.upper i) (z z' : CellClosedDomain R) (heq : z.val i=z'.val i) :
    R.firstIntervalParameter i hi z=R.firstIntervalParameter i hi z' := by
  apply Subtype.ext
  simp only [firstIntervalParameter,heq]

theorem normalizeTransverse_coordinate_dist_le (R : RectangularCell d) (i j : Fin d)
    (hj : R.lower j<R.upper j) (z z' : CellClosedDomain R)
    (heq : ∀ k,k≠j → z.val k=z'.val k) :
    dist (R.normalizeTransverse i z) (R.normalizeTransverse i z')≤
      (2/R.transverseWidth j)*|z.val j-z'.val j| := by
  have hw : 0<R.transverseWidth j := sub_pos.mpr (by exact_mod_cast hj)
  rw [Subtype.dist_eq]
  apply (dist_pi_le_iff (by positivity)).mpr
  intro k
  by_cases hkj : k.val=j
  · change |(2*z.val k.val-(R.lower k.val : ℝ)-(R.upper k.val : ℝ))/R.transverseWidth k.val-
      (2*z'.val k.val-(R.lower k.val : ℝ)-(R.upper k.val : ℝ))/R.transverseWidth k.val|≤_
    rw [hkj]
    have hsub : (2*z.val j-(R.lower j : ℝ)-(R.upper j : ℝ))/R.transverseWidth j-
        (2*z'.val j-(R.lower j : ℝ)-(R.upper j : ℝ))/R.transverseWidth j=
        (2/R.transverseWidth j)*(z.val j-z'.val j) := by ring
    rw [hsub,abs_mul,abs_of_pos (by positivity : 0<2/R.transverseWidth j)]
  · change dist ((2*z.val k.val-(R.lower k.val : ℝ)-(R.upper k.val : ℝ))/R.transverseWidth k.val)
      ((2*z'.val k.val-(R.lower k.val : ℝ)-(R.upper k.val : ℝ))/R.transverseWidth k.val)≤_
    rw [heq k.val hkj,dist_self]
    positivity

theorem point_eq_of_only_collapsed_coordinate (R : RectangularCell d) (j : Fin d)
    (hj : R.lower j=R.upper j) (z z' : CellClosedDomain R)
    (heq : ∀ k,k≠j → z.val k=z'.val k) : z=z' := by
  apply Subtype.ext
  funext k
  by_cases hkj : k=j
  · subst k
    have hz : z.val j=(R.lower j : ℝ) := le_antisymm
      (by simpa [hj] using (z.property j).2) (z.property j).1
    have hz' : z'.val j=(R.lower j : ℝ) := le_antisymm
      (by simpa [hj] using (z'.property j).2) (z'.property j).1
    exact hz.trans hz'.symm
  · exact heq k hkj

end RectangularCell

namespace PrismBoundaryData
variable {Z : Type*} [MetricSpace Z] {R : RectangularCell d} {i : Fin d}
variable {p q : Z} {S B D J : ℝ≥0} (F : PrismBoundaryData R i p q S B)
variable (H : ControlledContraction p D J)

theorem fill_first_dist_le (hi : R.lower i<R.upper i) (z z' : CellClosedDomain R)
    (heq : ∀ j,j≠i → z.val j=z'.val j) :
    dist (F.fill H hi z) (F.fill H hi z')≤
      (3*max S D : ℝ≥0)/R.transverseWidth i*|z.val i-z'.val i| := by
  unfold fill
  rw [R.normalizeTransverse_eq_of_except_first i z z' heq]
  have h := (H.coneValue_path_lipschitz F.pathFamily (R.normalizeTransverse i z')).dist_le_mul
    (R.firstIntervalParameter i hi z) (R.firstIntervalParameter i hi z')
  rw [R.firstIntervalParameter_dist i hi z z'] at h
  simpa only [div_mul_eq_mul_div,mul_div_assoc] using h

theorem fill_transverse_dist_le (hi : R.lower i<R.upper i) (j : Fin d)
    (hji : j≠i) (hj : R.lower j<R.upper j) (z z' : CellClosedDomain R)
    (heq : ∀ k,k≠j → z.val k=z'.val k) :
    dist (F.fill H hi z) (F.fill H hi z')≤
      2*(ControlledContraction.coneTransverseConstant S D J B : ℝ)/R.transverseWidth j*
        |z.val j-z'.val j| := by
  unfold fill
  rw [R.firstIntervalParameter_eq i hi z z' (heq i hji.symm)]
  have h := (H.coneValue_transverse_lipschitz F.pathFamily
    (R.firstIntervalParameter i hi z')).dist_le_mul (R.normalizeTransverse i z) (R.normalizeTransverse i z')
  calc
    _≤(ControlledContraction.coneTransverseConstant S D J B : ℝ)*
      dist (R.normalizeTransverse i z) (R.normalizeTransverse i z') := h
    _≤(ControlledContraction.coneTransverseConstant S D J B : ℝ)*
      ((2/R.transverseWidth j)*|z.val j-z'.val j|) := mul_le_mul_of_nonneg_left
        (R.normalizeTransverse_coordinate_dist_le i j hj z z' heq)
        (ControlledContraction.coneTransverseConstant S D J B).property
    _=_ := by ring

end PrismBoundaryData
end
end AbelianTargets
