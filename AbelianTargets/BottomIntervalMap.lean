import AbelianTargets.FiniteIntervalGluing
import AbelianTargets.JointCarrierRows

/-! The literal affine bottom interval in barycentric carrier coordinates. -/

namespace AbelianTargets.IntervalCarriers
noncomputable section

def bottomMass (K R n : ℕ) : CarrierVertex K 0 R → ℝ :=
  vertexMass (carrierBase K R) ((n : ℤ),0)

def bottomMap (K R : ℕ) (u : ℝ) : CarrierVertex K 0 R → ℝ :=
  FixedSlots.intervalGlue
    (fun n z => FixedSlots.mix (bottomMass K R n) (bottomMass K R (n+1)) z.1)
    (R-1) (u,0)

theorem bottomMap_on_unit (K R n : ℕ) (hn : n < R) (s : unitInterval) :
    bottomMap K R ((n : ℝ)+s) =
      FixedSlots.mix (bottomMass K R n) (bottomMass K R (n+1)) s := by
  apply FixedSlots.intervalGlue_on_unit _ (R-1) n (by omega)
  intro i hi u
  simp only [FixedSlots.mix_zero,FixedSlots.mix_one]

theorem bottomMass_eq (K R n : ℕ) (hn : n ≤ R) :
    bottomMass K R n = (Probability.dirac (bottomVertex K R n hn)).mass := by
  unfold bottomMass vertexMass
  have he : liftVertex (carrierBase K R) ((n : ℤ),0) = bottomVertex K R n hn := by
    apply Subtype.ext
    exact liftVertex_val _ _ (bottomVertex K R n hn).property
  rw [he]

theorem bottomMap_zero (K R : ℕ) : bottomMap K R 0 = bottomMass K R 0 := by
  rw [bottomMap,FixedSlots.intervalGlue_zero]
  exact FixedSlots.mix_zero _ _

theorem bottomMap_right (K R : ℕ) (hR : 0 < R) : bottomMap K R R = bottomMass K R R := by
  have he : ((R-1 : ℕ) : ℝ)+1 = (R : ℝ) := by
    have hh : R-1+1=R := by omega
    exact_mod_cast hh
  unfold bottomMap
  rw [← he,FixedSlots.intervalGlue_right]
  simpa only [show R-1+1=R by omega] using FixedSlots.mix_one (bottomMass K R (R-1)) _

theorem bottomMap_continuous (K R : ℕ) : Continuous (bottomMap K R) := by
  apply (FixedSlots.intervalGlue_continuous _ (R-1) ?_ ?_).comp
    (continuous_id.prodMk (continuous_const (y := (0 : unitInterval))))
  · intro i hi
    exact (FixedSlots.mix_lipschitz _ _ 1 (Probability.dist_le_one _ _)).continuous.comp continuous_fst
  · intro i hi u
    simp only [FixedSlots.mix_zero,FixedSlots.mix_one]

end
end AbelianTargets.IntervalCarriers
