import AbelianTargets.ProbabilityParameters
import AbelianTargets.SimplexMetricGluing
import AbelianTargets.SimplicialChartGluing

/-! Affine chart coordinates have a bound depending only on face dimension. -/
namespace AbelianTargets.Probability
open scoped BigOperators NNReal unitInterval
noncomputable section
variable {V : Type*} [Fintype V]

theorem parameter_dist_le_of_supported (c : V → I) (s : Finset V) (p q : Probability V)
    (hp : p.SupportedOn (s : Set V)) (hq : q.SupportedOn (s : Set V)) :
    dist (parameter c p) (parameter c q)≤(s.card : ℝ)*dist p q := by
  classical
  have he : (∑ v,(p.mass v-q.mass v)*(c v : ℝ))=∑ v∈s,(p.mass v-q.mass v)*(c v : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro v hv hvs
    rw [(supportedOn_iff_zero.mp hp) v hvs,(supportedOn_iff_zero.mp hq) v hvs]
    ring
  change |(∑ v,p.mass v*(c v : ℝ))-(∑ v,q.mass v*(c v : ℝ))|≤_
  rw [←Finset.sum_sub_distrib]
  simp_rw [←sub_mul]
  rw [he]
  calc
    _ ≤ ∑ v∈s,|(p.mass v-q.mass v)*(c v : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v∈s,dist p q := Finset.sum_le_sum (fun v hv => by
      rw [abs_mul,abs_of_nonneg (c v).property.1]
      have hd : |p.mass v-q.mass v|≤dist p q := by
        simpa only [Real.dist_eq] using mass_dist_le p q v
      calc
        _ ≤ |p.mass v-q.mass v| * 1 := mul_le_mul_of_nonneg_left (c v).property.2 (abs_nonneg _)
        _ ≤ dist p q := by simpa using hd)
    _ = _ := by simp

theorem parameter_face_lipschitz (c : V → I) (s : Finset V) :
    LipschitzWith (s.card : ℝ≥0) (fun p : ProbabilityFace s => parameter c p.1) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  exact parameter_dist_le_of_supported c s p.1 q.1 p.2 q.2

end
end AbelianTargets.Probability
