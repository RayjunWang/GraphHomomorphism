import AbelianTargets.CarrierGeometry

/-! Exact barycentric coordinates on an edge, used to invert the literal
height-zero carrier parametrization. -/

namespace AbelianTargets.Probability
noncomputable section
open scoped BigOperators unitInterval NNReal
variable {V : Type*} [Fintype V]

def weightedCoordinate (c : V → ℝ) (p : Probability V) : ℝ := ∑ u,p.mass u*c u

def weightedCoordinateConstant (c : V → ℝ) : ℝ≥0 :=
  ⟨∑ u,|c u|,Finset.sum_nonneg (fun u _ => abs_nonneg _)⟩

theorem weightedCoordinate_lipschitz (c : V → ℝ) :
    LipschitzWith (weightedCoordinateConstant c) (weightedCoordinate c) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change |(∑ u,p.mass u*c u)-(∑ u,q.mass u*c u)| ≤ (∑ u,|c u|)*dist p q
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ u,|p.mass u*c u-q.mass u*c u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u,|c u| * dist p q := by
      apply Finset.sum_le_sum
      intro u hu
      rw [← sub_mul,abs_mul,mul_comm]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact dist_le_pi_dist p.mass q.mass u
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem mass_pair_sum (p : Probability V) (v w : V) (hne : v ≠ w)
    (hp : p.SupportedOn ({v,w} : Set V)) : p.mass v+p.mass w=1 := by
  classical
  have hsum : ∑ u ∈ ({v,w} : Finset V),p.mass u = ∑ u,p.mass u := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u hu hn
    apply (supportedOn_iff_zero.mp hp) u
    simpa using hn
  simpa [hne] using hsum.trans p.sum_one

theorem eq_mix_dirac_of_pair (p : Probability V) (v w : V) (hne : v ≠ w)
    (hp : p.SupportedOn ({v,w} : Set V)) :
    p = mix (dirac v) (dirac w) ⟨p.mass w,p.nonneg w,p.mass_le_one w⟩ := by
  classical
  have hs := p.mass_pair_sum v w hne hp
  ext u
  by_cases huv : u=v
  · subst u
    simp [mix_mass,dirac_mass,hne]
    linarith
  · by_cases huw : u=w
    · subst u
      simp [mix_mass,dirac_mass,hne.symm]
    · have hz : p.mass u=0 := (supportedOn_iff_zero.mp hp) u (by simp [huv,huw])
      simp [mix_mass,dirac_mass,huv,huw,hz]

theorem eq_dirac_of_singleton (p : Probability V) (v : V)
    (hp : p.SupportedOn ({v} : Set V)) : p=dirac v := by
  classical
  have hs : p.mass v=1 := by
    have hsum : ∑ u ∈ ({v} : Finset V),p.mass u = ∑ u,p.mass u := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro u hu hn
      apply (supportedOn_iff_zero.mp hp) u
      simpa using hn
    simpa using hsum.trans p.sum_one
  ext u
  by_cases hu : u=v
  · subst u
    simp [dirac_mass,hs]
  · have hz := (supportedOn_iff_zero.mp hp) u (by simp [hu])
    simp [dirac_mass,hu,hz]

theorem weighted_pair_sum (p : Probability V) (v w : V) (hne : v ≠ w)
    (hp : p.SupportedOn ({v,w} : Set V)) (c : V → ℝ) :
    ∑ u,p.mass u*c u=p.mass v*c v+p.mass w*c w := by
  classical
  have hsum : ∑ u ∈ ({v,w} : Finset V),p.mass u*c u = ∑ u,p.mass u*c u := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u hu hn
    have hz := (supportedOn_iff_zero.mp hp) u (by simpa using hn)
    simp [hz]
  simpa [hne] using hsum.symm

theorem weighted_unit_edge (p : Probability V) (v w : V) (hne : v ≠ w)
    (hp : p.SupportedOn ({v,w} : Set V)) (c : V → ℝ) (hstep : c w=c v+1) :
    ∑ u,p.mass u*c u=c v+p.mass w := by
  rw [p.weighted_pair_sum v w hne hp c,hstep]
  have hs := p.mass_pair_sum v w hne hp
  calc
    _ = (p.mass v+p.mass w)*c v+p.mass w := by ring
    _ = _ := by rw [hs]; ring

theorem weighted_singleton (p : Probability V) (v : V)
    (hp : p.SupportedOn ({v} : Set V)) (c : V → ℝ) : ∑ u,p.mass u*c u=c v := by
  classical
  rw [p.eq_dirac_of_singleton v hp]
  simp [dirac_mass]

end
end AbelianTargets.Probability
