import AbelianTargets.ParameterFaceBounds
import AbelianTargets.EquivariantCellCharts

/-! A common modulus for all torsion charts, independent of the vertex set. -/
universe v
namespace AbelianTargets
noncomputable section
open scoped unitInterval
attribute [local instance] Classical.propDecidable

namespace SupportPair
theorem paritySwap_dist {W : Type*} [Fintype W] (H : SimpleGraph W) (r : ℤ)
    (p q : SupportPair H) : dist (paritySwap H r p) (paritySwap H r q)=dist p q := by
  unfold paritySwap
  split_ifs
  · rfl
  · exact (isometry_swap H).dist_eq _ _
end SupportPair

namespace Probability
def unitIndicator {V:Type*} (v:V) (w:V) : I := if w=v then 1 else 0
theorem parameter_indicator {V : Type*} [Fintype V] (p : Probability V) (v : V) :
    parameter (unitIndicator v) p=
      ⟨p.mass v,p.nonneg v,p.mass_le_one v⟩ := by
  classical
  apply Subtype.ext
  unfold unitIndicator
  change (∑w,p.mass w*↑(if w=v then (1:I) else 0))=p.mass v
  calc
    _ = ∑w,if w=v then p.mass w else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      by_cases h:w=v <;> simp [h]
    _ = _ := by simp
end Probability

namespace SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)

theorem affineChart_uniform_face_modulus :
    ∀ ε:ℝ,0<ε→∃δ:ℝ,0<δ ∧
      ∀ {V:Type v} [Fintype V] (height theta:V→I) (r:ℤ) (s:Finset V)
        (p q:Probability V),s.card≤3→p.SupportedOn (s:Set V)→q.SupportedOn (s:Set V)→
        dist p q<δ→dist (SupportPair.paritySwap H r (D.affineChart height theta p))
          (SupportPair.paritySwap H r (D.affineChart height theta q))<ε := by
  intro ε hε
  have huc : UniformContinuous D.relationHomotopy :=
    CompactSpace.uniformContinuous_of_continuous D.relationHomotopy.continuous
  obtain ⟨η,hη,hbound⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  refine ⟨η/3,by positivity,?_⟩
  intro V inst height theta r s p q hcard hp hq hd
  rw [SupportPair.paritySwap_dist]
  apply hbound
  have h₁ := Probability.parameter_dist_le_of_supported height s p q hp hq
  have h₂ := Probability.parameter_dist_le_of_supported theta s p q hp hq
  have hc : (s.card:ℝ)≤3 := by exact_mod_cast hcard
  have hh : dist (Probability.parameter height p,Probability.parameter theta p)
      (Probability.parameter height q,Probability.parameter theta q)≤3*dist p q := by
    rw [Prod.dist_eq]
    exact max_le (h₁.trans (mul_le_mul_of_nonneg_right hc dist_nonneg))
      (h₂.trans (mul_le_mul_of_nonneg_right hc dist_nonneg))
  exact hh.trans_lt (by linarith)

theorem affineChart_bottom_constant {V : Type*} [Fintype V] (p:Probability V) :
    D.affineChart (fun _ => 0) (fun _ => 0) p=D.base := by
  unfold affineChart
  simp only [Probability.parameter_const,Path.Homotopy.source]

theorem affineChart_top_indicator {V : Type*} [Fintype V] (p:Probability V) (v:V) :
    D.affineChart (fun _ => 1) (Probability.unitIndicator v) p=
      D.a ⟨p.mass v,p.nonneg v,p.mass_le_one v⟩ := by
  classical
  unfold affineChart
  rw [Probability.parameter_const,Probability.parameter_indicator,D.relationHomotopy.apply_one]
  rfl

end SupportTorsionData
end
end AbelianTargets
