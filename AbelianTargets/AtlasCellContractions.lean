import AbelianTargets.AtlasCarrierEndpoints
import AbelianTargets.UniformCarrierContraction

set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets
noncomputable section
open scoped NNReal
variable {d : ℕ}

private theorem carrier_metric_heq (m K : ℕ) (A B C D : ℤ) (hA : A=C) (hB : B=D) :
    HEq (IntervalCarriers.instMetricSpaceRealization m K A B)
      (IntervalCarriers.instMetricSpaceRealization m K C D) := by
  subst C
  subst D
  rfl

private theorem carrier_point_heq (m K : ℕ) (A B C D : ℤ) (hA : A=C) (hB : B=D)
    (v : IntervalCarriers.CarrierVertex K A B) (w : IntervalCarriers.CarrierVertex K C D)
    (hvw : v.val=w.val) :
    HEq (IntervalCarriers.point (m := m) v) (IntervalCarriers.point (m := m) w) := by
  subst C
  subst D
  have he : v=w := Subtype.ext hvw
  subst w
  rfl

/-- The logarithmic carrier speed and one common finite joint constant
serve every actual atlas cell, independently of its horizontal position. -/
theorem exists_atlasCellContractions {K₀ : Fin d→ℕ}
    (T₀ : IntegerRectangularTiling d K₀) (m : ℕ) (hm : 2≤m) (K : ℕ) (i : Fin d)
    (hlog : Nat.log m (K₀ i)≤K) :
    ∃ J : ℝ≥0,∀ (R : RectangularCell d),R∈T₀.cells → R.lower i<R.upper i →
      Nonempty (ControlledContraction (cellLeftPoint m K i R)
        (IntervalCarriers.uniformCarrierSpeed m K) J) := by
  obtain ⟨J,hJ⟩ := IntervalCarriers.exists_translated_uniformCarrierContractions m hm K (K₀ i) hlog
  refine ⟨J,?_⟩
  intro R hR hi
  let n := (R.upper i-R.lower i).toNat
  have hw : (n : ℤ)=R.upper i-R.lower i := Int.toNat_of_nonneg (sub_nonneg.mpr (R.ordered i))
  have hn : 0<n := by omega
  have hnK : n≤K₀ i := by
    have hb := T₀.cells_bounded hR i
    omega
  obtain ⟨H⟩ := hJ (R.lower i) n hn hnK
  have hb : (n : ℤ)+R.lower i=R.upper i := by omega
  have hp :
      (IntervalCarriers.realizationTranslationEquiv (m := m) (K := K) (A := 0) (B := n) (R.lower i))
        (IntervalCarriers.point (IntervalCarriers.carrierBase K n))=
      IntervalCarriers.point (⟨((0 : ℤ)+R.lower i,0),IntervalCarriers.mem_carrierVertices.mpr
        ⟨le_rfl,by omega,Nat.zero_le K⟩⟩ :
          IntervalCarriers.CarrierVertex K (0+R.lower i) ((n : ℤ)+R.lower i)) := by
    apply Subtype.ext
    change Probability.push _ (Probability.dirac _)=Probability.dirac _
    rw [Probability.push_dirac]
    congr 1
  rw [hp] at H
  simp only [zero_add,hb] at H
  convert Nonempty.intro H using 2
  all_goals simp [CellIntervalCarrier,zero_add,hb,cellLeftPoint,cellBottomPoint,cellBottomVertex]
  · exact carrier_metric_heq m K _ _ _ _ (by simp) hb.symm
  · exact carrier_point_heq m K _ _ _ _ (by simp) hb.symm _ _ rfl

end
end AbelianTargets
