import AbelianTargets.CarrierSupportProjection
import AbelianTargets.UniformAffineSupportCharts

namespace AbelianTargets.SupportTorsionData
noncomputable section
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
open IntervalCarriers

theorem faceValue_affine_representation (K : ℕ) (A B : ℤ) (s : Finset (CarrierVertex K A B))
    (hs : s∈simplexFaces (2*D.power+1) K A B) :
    ∃ (r:ℤ) (height theta:CarrierVertex K A B→I),
      ∀p:Probability (CarrierVertex K A B),p.SupportedOn (s:Set _)→
        (D.projectionCharts K A B).faceValue s p=
          SupportPair.paritySwap H r (D.affineChart height theta p) := by
  by_cases hc : FaceHasCell (m:=2*D.power+1) s
  · refine ⟨hc.choose.1,cellHeight hc.choose∘Subtype.val,
      cellTheta D.power (2*D.power+1) hc.choose∘Subtype.val,?_⟩
    intro p hp
    rw [CarrierProjectionCharts.faceValue,dif_pos hc]
    rfl
  · rcases (mem_simplexFaces s).mp hs with ⟨v,hv,hsub⟩ | ⟨u,hu,v,hv,he,hsub⟩ | ⟨t,ht,hsub⟩
    · refine ⟨v.1,(fun _=>0),(fun _=>0),?_⟩
      intro p hp
      rw [CarrierProjectionCharts.faceValue,dif_neg hc]
      change D.skeletonMap Subtype.val p= _
      rw [D.skeletonMap_singleton Subtype.val p ⟨v,hv⟩
        (rawSupported_singleton p v hv ((rawSupported_of_face hp).mono hsub)),
        D.affineChart_bottom_constant]
    · let u' : CarrierVertex K A B := ⟨u,hu⟩
      let v' : CarrierVertex K A B := ⟨v,hv⟩
      have hp : ∀p:Probability (CarrierVertex K A B),p.SupportedOn (s:Set _)→
          p.SupportedOn ({u',v'}:Set _) := fun p h =>
        rawSupported_pair p u v hu hv ((rawSupported_of_face h).mono hsub)
      rcases he with ⟨_,he | he⟩ <;> rcases he with he | he
      · refine ⟨u.1,(fun _=>1),Probability.unitIndicator v',?_⟩
        intro p h
        rw [CarrierProjectionCharts.faceValue,dif_neg hc]
        change D.skeletonMap Subtype.val p= _
        rw [D.skeletonMap_horizontal Subtype.val p u' v' (hp p h) he,D.affineChart_top_indicator]
      · refine ⟨u.1,(fun _=>0),(fun _=>0),?_⟩
        intro p h
        rw [CarrierProjectionCharts.faceValue,dif_neg hc]
        change D.skeletonMap Subtype.val p= _
        have hh : u.1=v.1 := by change v=(u.1,u.2+1) at he; rw [he]
        rw [D.skeletonMap_vertical Subtype.val p u' v' (hp p h) hh,D.affineChart_bottom_constant]
      · refine ⟨v.1,(fun _=>1),Probability.unitIndicator u',?_⟩
        intro p h
        rw [CarrierProjectionCharts.faceValue,dif_neg hc]
        change D.skeletonMap Subtype.val p= _
        have hp' : p.SupportedOn ({v',u'}:Set _) := by simpa [Set.pair_comm] using hp p h
        rw [D.skeletonMap_horizontal Subtype.val p v' u' hp' he,D.affineChart_top_indicator]
      · refine ⟨u.1,(fun _=>0),(fun _=>0),?_⟩
        intro p h
        rw [CarrierProjectionCharts.faceValue,dif_neg hc]
        change D.skeletonMap Subtype.val p= _
        have hh : u.1=v.1 := by change u=(v.1,v.2+1) at he; rw [he]
        rw [D.skeletonMap_vertical Subtype.val p u' v' (hp p h) hh,D.affineChart_bottom_constant]
    · obtain ⟨c,hc',hct⟩ := fanTriangle_of_carrierTriangle ht
      exact False.elim (hc ⟨c,hc',t,hct,hsub⟩)

theorem carrierProjection_eq_faceValue (K : ℕ) (A B : ℤ)
    (p : Realization (2*D.power+1) K A B) (s : Finset (CarrierVertex K A B))
    (hs : s∈simplexFaces (2*D.power+1) K A B) (hp : p.1.SupportedOn (s:Set _)) :
    D.carrierProjection K A B p=(D.projectionCharts K A B).faceValue s p.1 := by
  exact ((D.projectionCharts K A B).simplicialData (by omega)).eval_eq_chart p s hs hp

end
end AbelianTargets.SupportTorsionData
