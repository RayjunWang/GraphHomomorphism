import AbelianTargets.SupportCellRestrictions
import AbelianTargets.CarrierProjectionGluing

/-! The actual continuous carrier projection supplied by odd torsion. -/
namespace AbelianTargets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped unitInterval

namespace IntervalCarriers
theorem rawSupported_singleton {K : ℕ} {A B : ℤ} (p : Probability (CarrierVertex K A B))
    (u : Vertex) (hu : u∈carrierVertices K A B) (hp : RawSupported p {u}) :
    p.SupportedOn ({⟨u,hu⟩}:Set (CarrierVertex K A B)) := by
  intro v hv
  apply Subtype.ext
  exact Finset.mem_singleton.mp (hp v hv)

theorem rawSupported_pair {K : ℕ} {A B : ℤ} (p : Probability (CarrierVertex K A B))
    (u v : Vertex) (hu : u∈carrierVertices K A B) (hv : v∈carrierVertices K A B)
    (hp : RawSupported p {u,v}) :
    p.SupportedOn ({⟨u,hu⟩,⟨v,hv⟩}:Set (CarrierVertex K A B)) := by
  intro w hw
  have hs := hp w hw
  simp only [Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with hs | hs
  · exact Or.inl (Subtype.ext hs)
  · exact Or.inr (Subtype.ext hs)
end IntervalCarriers

namespace SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
variable {V : Type*} [Fintype V]

theorem continuousOn_skeletonMap_singleton (f : V → IntervalCarriers.Vertex) (v : V) :
    ContinuousOn (D.skeletonMap f) {p | p.SupportedOn ({v}:Set V)} := by
  apply (continuous_const : Continuous (fun _:Probability V => SupportPair.paritySwap H (f v).1 D.base)).continuousOn.congr
  intro p hp
  exact D.skeletonMap_singleton f p v hp

theorem continuousOn_skeletonMap_horizontal (f : V → IntervalCarriers.Vertex) (u v : V)
    (he : IntervalCarriers.HorizontalStep (2*D.power+1) (f u) (f v)) :
    ContinuousOn (D.skeletonMap f) {p | p.SupportedOn ({u,v}:Set V)} := by
  have hc : Continuous (fun p:Probability V => SupportPair.paritySwap H (f u).1
      (D.a ⟨p.mass v,p.nonneg v,p.mass_le_one v⟩)) :=
    (SupportPair.continuous_paritySwap H _).comp
      (D.a.continuous.comp ((Probability.continuous_mass_apply v).subtype_mk _))
  apply hc.continuousOn.congr
  intro p hp
  exact D.skeletonMap_horizontal f p u v hp he

theorem continuousOn_skeletonMap_vertical (f : V → IntervalCarriers.Vertex) (u v : V)
    (he : (f u).1=(f v).1) :
    ContinuousOn (D.skeletonMap f) {p | p.SupportedOn ({u,v}:Set V)} := by
  apply (continuous_const : Continuous (fun _:Probability V => SupportPair.paritySwap H (f u).1 D.base)).continuousOn.congr
  intro p hp
  exact D.skeletonMap_vertical f p u v hp he

theorem cellChart_supported_skeleton_pair (f : V → IntervalCarriers.Vertex)
    (c : IntervalCarriers.Vertex) (s : Finset IntervalCarriers.Vertex)
    (hs : IntervalCarriers.IsFanTriangle (2*D.power+1) c s)
    (p : Probability V) (hps : ∀v,0<p.mass v→f v∈s) (u v : V)
    (hp : p.SupportedOn ({u,v}:Set V))
    (he : (IntervalCarriers.graph (2*D.power+1)).Adj (f u) (f v)) :
    D.cellChart f c p=D.skeletonMap f p := by
  by_cases hu : 0<p.mass u
  · by_cases hv : 0<p.mass v
    · exact D.cellChart_supported_pair f c s hs p u v hp (hps u hu) (hps v hv) he
    · have hz : p.mass v=0 := le_antisymm (le_of_not_gt hv) (p.nonneg v)
      have hp' : p.SupportedOn ({u}:Set V) := by
        intro w hw
        rcases hp w hw with rfl | rfl
        · rfl
        · simp [hz] at hw
      rw [D.skeletonMap_singleton f p u hp',p.eq_dirac_of_singleton u hp']
      exact D.cellChart_vertex f c s hs u (hps u hu)
  · have hz : p.mass u=0 := le_antisymm (le_of_not_gt hu) (p.nonneg u)
    have hp' : p.SupportedOn ({v}:Set V) := by
      intro w hw
      rcases hp w hw with rfl | rfl
      · simp [hz] at hw
      · rfl
    have hv : f v∈s := by
      have hpv : p.mass v=1 := by rw [p.eq_dirac_of_singleton v hp']; simp
      exact hps v (by rw [hpv]; norm_num)
    rw [D.skeletonMap_singleton f p v hp',p.eq_dirac_of_singleton v hp']
    exact D.cellChart_vertex f c s hs v hv

def projectionCharts (K : ℕ) (A B : ℤ) :
    IntervalCarriers.CarrierProjectionCharts (2*D.power+1) K A B (SupportPair H) where
  skeleton := D.skeletonMap Subtype.val
  continuous_vertex u hu := by
    exact (D.continuousOn_skeletonMap_singleton Subtype.val ⟨u,hu⟩).mono
      (fun p hp => IntervalCarriers.rawSupported_singleton p u hu hp)
  continuous_edge u hu v hv he := by
    let u' : IntervalCarriers.CarrierVertex K A B := ⟨u,hu⟩
    let v' : IntervalCarriers.CarrierVertex K A B := ⟨v,hv⟩
    have hp : ∀p,IntervalCarriers.RawSupported p {u,v}→p.SupportedOn ({u',v'}:Set _) :=
      fun p hp => IntervalCarriers.rawSupported_pair p u v hu hv hp
    rcases he with ⟨_,he | he⟩ <;> rcases he with he | he
    · exact (D.continuousOn_skeletonMap_horizontal Subtype.val u' v' he).mono (fun p h => hp p h)
    · exact (D.continuousOn_skeletonMap_vertical Subtype.val u' v'
        (by change u.1=v.1; change v=(u.1,u.2+1) at he; rw [he])).mono (fun p h => hp p h)
    · have hrev := (D.continuousOn_skeletonMap_horizontal Subtype.val v' u' he)
      exact hrev.mono (fun p h => by simpa [Set.pair_comm] using hp p h)
    · exact (D.continuousOn_skeletonMap_vertical Subtype.val u' v'
        (by change u.1=v.1; change u=(v.1,v.2+1) at he; rw [he])).mono (fun p h => hp p h)
  cell := D.cellChart Subtype.val
  continuous_cell c hc := D.continuous_cellChart _ c
  cell_skeleton c hc t ht p hpt hsk := by
    rcases hsk with ⟨v,hv,hp⟩ | ⟨u,hu,v,hv,he,hp⟩
    · have hp' := IntervalCarriers.rawSupported_singleton p v hv hp
      have hv' : v∈t := by
        have hmass : p.mass ⟨v,hv⟩=1 := by rw [p.eq_dirac_of_singleton ⟨v,hv⟩ hp']; simp
        exact hpt ⟨v,hv⟩ (by rw [hmass]; norm_num)
      rw [D.skeletonMap_singleton Subtype.val p ⟨v,hv⟩ hp',p.eq_dirac_of_singleton ⟨v,hv⟩ hp']
      exact D.cellChart_vertex (Subtype.val : IntervalCarriers.CarrierVertex K A B → _) c t ht ⟨v,hv⟩ hv'
    · exact D.cellChart_supported_skeleton_pair _ c t ht p hpt ⟨u,hu⟩ ⟨v,hv⟩
        (IntervalCarriers.rawSupported_pair p u v hu hv hp) he

def carrierProjection (K : ℕ) (A B : ℤ) :
    IntervalCarriers.Realization (2*D.power+1) K A B → SupportPair H :=
  (D.projectionCharts K A B).eval (by omega)

theorem continuous_carrierProjection (K : ℕ) (A B : ℤ) :
    Continuous (D.carrierProjection K A B) :=
  (D.projectionCharts K A B).continuous_eval (by omega)

end SupportTorsionData
end
end AbelianTargets
