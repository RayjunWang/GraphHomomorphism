import AbelianTargets.CarrierSupportProjection

/-! Exact images of the literal horizontal and vertical carrier edge paths. -/
namespace AbelianTargets.SupportTorsionData
noncomputable section
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
open IntervalCarriers

private theorem edgePath_rawSupported {m K : ℕ} {A B : ℤ} (v w:CarrierVertex K A B)
    (hf:CarrierFace m K A B {v.1,w.1}) (r:I) :
    RawSupported (edgePath v w hf r).1 {v.1,w.1} := by
  have hp : (edgePath v w hf r).1.SupportedOn ({v,w}:Set _) :=
    Probability.supportedOn_mix
      (Probability.supportedOn_dirac v (by simp))
      (Probability.supportedOn_dirac w (by simp)) r
  intro u hu
  rcases hp u hu with rfl | rfl <;> simp

theorem carrierProjection_horizontal_edgePath {K:ℕ} {A B:ℤ} (v w:CarrierVertex K A B)
    (he:HorizontalStep (2*D.power+1) v.1 w.1)
    (hf:CarrierFace (2*D.power+1) K A B {v.1,w.1}) (r:I) :
    D.carrierProjection K A B (edgePath v w hf r)=
      SupportPair.paritySwap H v.1.1 (D.a r) := by
  have hsk : SkeletonSupported (m:=2*D.power+1) (edgePath v w hf r).1 :=
    Or.inr ⟨v.1,v.2,w.1,w.2,horizontal_adj (by omega) he,edgePath_rawSupported v w hf r⟩
  rw [carrierProjection,(D.projectionCharts K A B).eval_eq_skeleton (by omega) _ hsk]
  change D.skeletonMap Subtype.val (Probability.mix (Probability.dirac v) (Probability.dirac w) r)=_
  have hp : (Probability.mix (Probability.dirac v) (Probability.dirac w) r).SupportedOn ({v,w}:Set _) :=
    Probability.supportedOn_mix (Probability.supportedOn_dirac v (by simp))
      (Probability.supportedOn_dirac w (by simp)) r
  rw [D.skeletonMap_horizontal Subtype.val _ v w hp he]
  have hne : v≠w := by intro hvw; subst w; exact (horizontal_adj (by omega) he).ne rfl
  congr 2
  apply Subtype.ext
  simp [Probability.mix_mass,Probability.dirac_mass,hne.symm]

theorem carrierProjection_vertical_edgePath {K:ℕ} {A B:ℤ} (v w:CarrierVertex K A B)
    (he:VerticalStep v.1 w.1)
    (hf:CarrierFace (2*D.power+1) K A B {v.1,w.1}) (r:I) :
    D.carrierProjection K A B (edgePath v w hf r)=SupportPair.paritySwap H v.1.1 D.base := by
  have hsk : SkeletonSupported (m:=2*D.power+1) (edgePath v w hf r).1 :=
    Or.inr ⟨v.1,v.2,w.1,w.2,vertical_adj he,edgePath_rawSupported v w hf r⟩
  rw [carrierProjection,(D.projectionCharts K A B).eval_eq_skeleton (by omega) _ hsk]
  change D.skeletonMap Subtype.val (Probability.mix (Probability.dirac v) (Probability.dirac w) r)=_
  have hp : (Probability.mix (Probability.dirac v) (Probability.dirac w) r).SupportedOn ({v,w}:Set _) :=
    Probability.supportedOn_mix (Probability.supportedOn_dirac v (by simp))
      (Probability.supportedOn_dirac w (by simp)) r
  apply D.skeletonMap_vertical Subtype.val _ v w hp
  change v.1.1=w.1.1
  change w.1=(v.1.1,v.1.2+1) at he
  rw [he]

end
end AbelianTargets.SupportTorsionData
