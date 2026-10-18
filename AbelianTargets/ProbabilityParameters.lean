import AbelianTargets.ProbabilityTwoVertices
import AbelianTargets.SegmentedOddPath

/-! Affine unit-interval coordinates on literal probability faces. -/

namespace AbelianTargets.Probability
noncomputable section
open scoped BigOperators unitInterval
variable {V : Type*} [Fintype V]

def parameter (c : V → unitInterval) (p : Probability V) : unitInterval :=
  ⟨∑ v,p.mass v*(c v : ℝ),by
    constructor
    · exact Finset.sum_nonneg (fun v _ => mul_nonneg (p.nonneg v) (c v).property.1)
    · calc
        _ ≤ ∑ v,p.mass v*1 := Finset.sum_le_sum
          (fun v _ => mul_le_mul_of_nonneg_left (c v).property.2 (p.nonneg v))
        _ = 1 := by simpa using p.sum_one⟩

theorem continuous_parameter (c : V → unitInterval) : Continuous (parameter c) := by
  apply Continuous.subtype_mk
  exact continuous_finset_sum _ (fun v _ => (continuous_mass_apply v).mul continuous_const)

@[simp] theorem parameter_dirac (c : V → unitInterval) (v : V) :
    parameter c (dirac v)=c v := by
  classical
  apply Subtype.ext
  simp [parameter,dirac_mass]

theorem parameter_mix (c : V → unitInterval) (p q : Probability V) (r : unitInterval) :
    parameter c (mix p q r)=intervalMix (parameter c p) (parameter c q) r := by
  apply Subtype.ext
  change (∑ v,((1-(r : ℝ))*p.mass v+(r : ℝ)*q.mass v)*(c v : ℝ)) = _
  simp only [add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
  rfl

theorem parameter_eq_on_support {c d : V → unitInterval} (p : Probability V)
    (s : Set V) (hp : p.SupportedOn s) (h : ∀ v∈s,c v=d v) : parameter c p=parameter d p := by
  classical
  apply Subtype.ext
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hs : v∈s
  · rw [h v hs]
  · simp [(supportedOn_iff_zero.mp hp) v hs]

theorem parameter_const (p : Probability V) (r : unitInterval) :
    parameter (fun _ => r) p=r := by
  apply Subtype.ext
  change (∑ v,p.mass v*(r : ℝ))=(r : ℝ)
  rw [← Finset.sum_mul,p.sum_one,one_mul]

end
end AbelianTargets.Probability
