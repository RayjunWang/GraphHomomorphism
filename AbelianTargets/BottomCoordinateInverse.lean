import AbelianTargets.BottomIntervalMap
import AbelianTargets.ProbabilityTwoVertices

/-! The actual affine bottom interval is inverted by its barycentric
horizontal coordinate, on every singleton and unit bottom edge. -/

namespace AbelianTargets.IntervalCarriers
noncomputable section
open scoped BigOperators NNReal unitInterval

def bottomCoordinate (K R : ℕ) (p : Probability (CarrierVertex K 0 R)) : ℝ :=
  p.weightedCoordinate (fun v => (v.val.1 : ℝ))

theorem bottomCoordinate_lipschitz (K R : ℕ) :
    LipschitzWith (Probability.weightedCoordinateConstant (fun v : CarrierVertex K 0 R =>
      (v.val.1 : ℝ))) (bottomCoordinate K R) :=
  Probability.weightedCoordinate_lipschitz _

theorem bottomCoordinate_bounds (K R : ℕ) (p : Probability (CarrierVertex K 0 R)) :
    0 ≤ bottomCoordinate K R p ∧ bottomCoordinate K R p ≤ R := by
  constructor
  · apply Finset.sum_nonneg
    intro v hv
    apply mul_nonneg (p.nonneg v)
    change (0 : ℝ) ≤ (v.val.1 : ℝ)
    exact_mod_cast (mem_carrierVertices.mp v.property).1
  · calc
      _ ≤ ∑ v,p.mass v*(R : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        apply mul_le_mul_of_nonneg_left _ (p.nonneg v)
        change (v.val.1 : ℝ) ≤ (R : ℝ)
        exact_mod_cast (mem_carrierVertices.mp v.property).2.1
      _ = (∑ v,p.mass v)*(R : ℝ) := (Finset.sum_mul _ _ _).symm
      _ = _ := by rw [p.sum_one,one_mul]

theorem bottomVertices_ne (K R n : ℕ) (hn : n < R) :
    bottomVertex K R n hn.le ≠ bottomVertex K R (n+1) (by omega) := by
  intro he
  have h := congrArg (fun v : CarrierVertex K 0 R => v.val.1) he
  dsimp [bottomVertex] at h
  omega

theorem bottomCoordinate_unit_edge (K R n : ℕ) (hn : n < R)
    (p : Probability (CarrierVertex K 0 R))
    (hp : p.SupportedOn ({bottomVertex K R n hn.le,
      bottomVertex K R (n+1) (by omega)} : Set _)) :
    bottomCoordinate K R p=(n : ℝ)+p.mass (bottomVertex K R (n+1) (by omega)) := by
  exact p.weighted_unit_edge _ _ (bottomVertices_ne K R n hn) hp _
    (by simp [bottomVertex])

theorem bottomMap_inverse_unit_edge (K R n : ℕ) (hn : n < R)
    (p : Probability (CarrierVertex K 0 R))
    (hp : p.SupportedOn ({bottomVertex K R n hn.le,
      bottomVertex K R (n+1) (by omega)} : Set _)) :
    bottomMap K R (bottomCoordinate K R p)=p.mass := by
  let s : unitInterval := ⟨p.mass (bottomVertex K R (n+1) (by omega)),
    p.nonneg _,p.mass_le_one _⟩
  have he := p.eq_mix_dirac_of_pair _ _ (bottomVertices_ne K R n hn) hp
  rw [bottomCoordinate_unit_edge K R n hn p hp]
  change bottomMap K R ((n : ℝ)+s)=p.mass
  rw [bottomMap_on_unit K R n hn s,bottomMass_eq K R n hn.le,
    bottomMass_eq K R (n+1) (by omega)]
  exact (congrArg Probability.mass he).symm

theorem bottomMap_at_integer (K R n : ℕ) (hn : n ≤ R) :
    bottomMap K R n=(Probability.dirac (bottomVertex K R n hn)).mass := by
  by_cases hlt : n < R
  · have h := bottomMap_on_unit K R n hlt 0
    simpa [bottomMass_eq K R n hn] using h
  · have he : n=R := by omega
    subst n
    by_cases hR : 0 < R
    · rw [bottomMap_right K R hR,bottomMass_eq K R R hn]
    · have he : R=0 := by omega
      subst R
      simpa using (bottomMap_zero K 0).trans (bottomMass_eq K 0 0 hn)

theorem bottomMap_inverse_singleton (K R n : ℕ) (hn : n ≤ R)
    (p : Probability (CarrierVertex K 0 R))
    (hp : p.SupportedOn ({bottomVertex K R n hn} : Set _)) :
    bottomMap K R (bottomCoordinate K R p)=p.mass := by
  have hc : bottomCoordinate K R p=(n : ℝ) :=
    p.weighted_singleton _ hp _
  rw [hc,bottomMap_at_integer K R n hn,p.eq_dirac_of_singleton _ hp]

def BottomSupported (K R : ℕ) (p : Probability (CarrierVertex K 0 R)) : Prop :=
  (∃ n : ℕ,∃ hn : n ≤ R,p.SupportedOn ({bottomVertex K R n hn} : Set _)) ∨
    ∃ n : ℕ,∃ hn : n < R,p.SupportedOn ({bottomVertex K R n hn.le,
      bottomVertex K R (n+1) (by omega)} : Set _)

theorem bottomMap_inverse (K R : ℕ) (p : Probability (CarrierVertex K 0 R))
    (hp : BottomSupported K R p) : bottomMap K R (bottomCoordinate K R p)=p.mass := by
  rcases hp with ⟨n,hn,hp⟩ | ⟨n,hn,hp⟩
  · exact bottomMap_inverse_singleton K R n hn p hp
  · exact bottomMap_inverse_unit_edge K R n hn p hp

end
end AbelianTargets.IntervalCarriers
