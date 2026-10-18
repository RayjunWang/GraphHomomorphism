import AbelianTargets.SupportSkeletonMap
import AbelianTargets.EquivariantCellCharts
import AbelianTargets.ProbabilityPushGeometry

set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets
noncomputable section
open scoped BigOperators unitInterval
attribute [local instance] Classical.propDecidable

namespace Probability
variable {V W : Type*} [Fintype V] [Fintype W]

theorem parameter_push (f : V → W) (c : W → I) (p : Probability V) :
    parameter c (push f p)=parameter (c ∘ f) p := by
  apply Subtype.ext
  change (∑ w,(∑ v,if f v=w then p.mass v else 0)*(c w : ℝ)) = _
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_eq_single (f v)]
  · simp
  · intro w hw hwf
    simp [Ne.symm hwf]
  · simp

theorem positiveCoordinates_push (f : V → W) (c : W → ℤ) (p : Probability V) :
    positiveCoordinates c (push f p)=positiveCoordinates (c ∘ f) p := by
  ext z
  simp only [positiveCoordinates,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨w,hw,hz⟩
    obtain ⟨v,hv,hp⟩ := (push_pos_iff f p w).mp hw
    exact ⟨v,hp,by simpa only [Function.comp_apply,hv] using hz⟩
  · rintro ⟨v,hp,hz⟩
    exact ⟨f v,(push_pos_iff f p (f v)).mpr ⟨v,rfl,hp⟩,hz⟩

theorem minimumCoordinate_push (f : V → W) (c : W → ℤ) (p : Probability V) :
    minimumCoordinate c (push f p)=minimumCoordinate (c ∘ f) p := by
  apply le_antisymm
  · obtain ⟨v,hv,he⟩ := minimumCoordinate_mem (c ∘ f) p
    have hh := minimumCoordinate_le c (push f p) (f v)
      ((push_pos_iff f p (f v)).mpr ⟨v,rfl,hv⟩)
    change c (f v)=_ at he
    rw [he] at hh
    exact hh
  · obtain ⟨w,hw,he⟩ := minimumCoordinate_mem c (push f p)
    obtain ⟨v,hv,hp⟩ := (push_pos_iff f p w).mp hw
    have hh := minimumCoordinate_le (c ∘ f) p v hp
    simpa only [Function.comp_apply,hv,he] using hh

theorem minimumCoordinate_add (c : V → ℤ) (p : Probability V) (a : ℤ) :
    minimumCoordinate (fun v => c v+a) p=minimumCoordinate c p+a := by
  apply le_antisymm
  · obtain ⟨v,hv,he⟩ := minimumCoordinate_mem c p
    have h := minimumCoordinate_le (fun v => c v+a) p v hv
    simpa only [he] using h
  · obtain ⟨v,hv,he⟩ := minimumCoordinate_mem (fun v => c v+a) p
    have h := minimumCoordinate_le c p v hv
    omega

end Probability

namespace SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
variable {V U : Type*} [Fintype V] [Fintype U]

theorem rawCellChart_push (f : V → U) (g : U → IntervalCarriers.Vertex)
    (c : IntervalCarriers.Vertex) (p : Probability V) :
    D.rawCellChart g c (Probability.push f p)=D.rawCellChart (g ∘ f) c p := by
  unfold rawCellChart affineChart
  rw [Probability.parameter_push,Probability.parameter_push]
  rfl

theorem cellChart_push (f : V → U) (g : U → IntervalCarriers.Vertex)
    (c : IntervalCarriers.Vertex) (p : Probability V) :
    D.cellChart g c (Probability.push f p)=D.cellChart (g ∘ f) c p := by
  unfold cellChart
  rw [D.rawCellChart_push]

theorem skeletonMap_push (f : V → U) (g : U → IntervalCarriers.Vertex)
    (p : Probability V) : D.skeletonMap g (Probability.push f p)=D.skeletonMap (g ∘ f) p := by
  unfold skeletonMap
  rw [Probability.minimumCoordinate_push]
  dsimp only
  rw [Probability.parameter_push]
  rfl

theorem rawCellChart_translate (f : V → IntervalCarriers.Vertex)
    (c : IntervalCarriers.Vertex) (a : ℤ) (p : Probability V) :
    D.rawCellChart (IntervalCarriers.translate a ∘ f) (IntervalCarriers.translate a c) p=
      D.rawCellChart f c p := by
  unfold rawCellChart
  have hh : IntervalCarriers.cellHeight (IntervalCarriers.translate a c) ∘ (IntervalCarriers.translate a ∘ f)=
      IntervalCarriers.cellHeight c ∘ f := by
    funext v
    exact IntervalCarriers.cellHeight_translate a c (f v)
  have ht : IntervalCarriers.cellTheta D.power (2*D.power+1) (IntervalCarriers.translate a c) ∘
      (IntervalCarriers.translate a ∘ f)=IntervalCarriers.cellTheta D.power (2*D.power+1) c ∘ f := by
    funext v
    exact IntervalCarriers.cellTheta_translate a _ _ c (f v)
  rw [hh,ht]

theorem cellChart_translate (f : V → IntervalCarriers.Vertex)
    (c : IntervalCarriers.Vertex) (a : ℤ) (p : Probability V) :
    D.cellChart (IntervalCarriers.translate a ∘ f) (IntervalCarriers.translate a c) p=
      SupportPair.paritySwap H a (D.cellChart f c p) := by
  unfold cellChart
  rw [D.rawCellChart_translate]
  change SupportPair.paritySwap H (c.1+a) _=SupportPair.paritySwap H a _
  rw [add_comm,SupportPair.paritySwap_add]

theorem skeletonMap_translate (f : V → IntervalCarriers.Vertex) (a : ℤ)
    (p : Probability V) : D.skeletonMap (IntervalCarriers.translate a ∘ f) p=
      SupportPair.paritySwap H a (D.skeletonMap f p) := by
  unfold skeletonMap
  change SupportPair.paritySwap H (p.minimumCoordinate (fun v => (f v).1+a))
    (D.a (Probability.parameter (fun v => if p.minimumCoordinate (fun w => (f w).1+a)<(f v).1+a then 1 else 0) p))=_
  rw [Probability.minimumCoordinate_add]
  simp only [add_lt_add_iff_right]
  rw [add_comm,SupportPair.paritySwap_add]

end SupportTorsionData
end
end AbelianTargets
