import AbelianTargets.ParitySwapGeometry

/-! A total support-space map whose restrictions to skeleton edges are literal paths. -/
namespace AbelianTargets
noncomputable section
open scoped unitInterval
attribute [local instance] Classical.propDecidable

namespace Probability
variable {V : Type*} [Fintype V]

def positiveCoordinates (f : V → ℤ) (p : Probability V) : Finset ℤ :=
  (Finset.univ.filter (fun v => 0<p.mass v)).image f

theorem positiveCoordinates_nonempty (f : V → ℤ) (p : Probability V) :
    (positiveCoordinates f p).Nonempty := by
  have hp : ∃v,0<p.mass v := by
    by_contra hn
    push_neg at hn
    have hz : ∀v,p.mass v=0 := fun v => le_antisymm (hn v) (p.nonneg v)
    have hs := p.sum_one
    simp [hz] at hs
  obtain ⟨v,hv⟩ := hp
  exact ⟨f v,Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩⟩

def minimumCoordinate (f : V → ℤ) (p : Probability V) : ℤ :=
  (positiveCoordinates f p).min' (positiveCoordinates_nonempty f p)

theorem minimumCoordinate_mem (f : V → ℤ) (p : Probability V) :
    ∃v,0<p.mass v ∧ f v=minimumCoordinate f p := by
  have h := Finset.min'_mem (positiveCoordinates f p) (positiveCoordinates_nonempty f p)
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp h
  exact ⟨v,(Finset.mem_filter.mp hv).2,he⟩

theorem minimumCoordinate_le (f : V → ℤ) (p : Probability V) (v : V) (hv : 0<p.mass v) :
    minimumCoordinate f p≤f v :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩)

theorem minimumCoordinate_pair_left (f : V → ℤ) (p : Probability V) (u v : V)
    (hp : p.SupportedOn ({u,v} : Set V)) (hu : 0<p.mass u) (hord : f u≤f v) :
    minimumCoordinate f p=f u := by
  obtain ⟨w,hw,he⟩ := minimumCoordinate_mem f p
  have hs := hp w hw
  rcases hs with rfl | rfl
  · exact he.symm
  · have hm := minimumCoordinate_le f p u hu
    omega

theorem minimumCoordinate_singleton (f : V → ℤ) (p : Probability V) (v : V)
    (hp : p.SupportedOn ({v} : Set V)) : minimumCoordinate f p=f v := by
  obtain ⟨w,hw,he⟩ := minimumCoordinate_mem f p
  have hs : w=v := hp w hw
  simpa only [hs] using he.symm

end Probability

namespace SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
variable {V : Type*} [Fintype V]

def skeletonMap (f : V → IntervalCarriers.Vertex) (p : Probability V) : SupportPair H :=
  let r := p.minimumCoordinate (fun v => (f v).1)
  SupportPair.paritySwap H r (D.a (Probability.parameter
    (fun v => if r<(f v).1 then 1 else 0) p))

theorem skeletonMap_singleton (f : V → IntervalCarriers.Vertex) (p : Probability V) (v : V)
    (hp : p.SupportedOn ({v} : Set V)) :
    D.skeletonMap f p=SupportPair.paritySwap H (f v).1 D.base := by
  unfold skeletonMap
  rw [Probability.minimumCoordinate_singleton _ _ v hp]
  dsimp only
  have hz : Probability.parameter (fun w => if (f v).1<(f w).1 then (1:I) else 0) p=0 := by
    rw [Probability.parameter_eq_on_support p ({v}:Set V) hp
      (show ∀w∈({v}:Set V),(if (f v).1<(f w).1 then (1:I) else 0)=0 from by
        intro w hw; have : w=v := hw; subst w; simp),Probability.parameter_const]
  rw [hz,D.a.source]

theorem skeletonMap_vertical (f : V → IntervalCarriers.Vertex) (p : Probability V) (u v : V)
    (hp : p.SupportedOn ({u,v} : Set V)) (hcoord : (f u).1=(f v).1) :
    D.skeletonMap f p=SupportPair.paritySwap H (f u).1 D.base := by
  unfold skeletonMap
  have hr : p.minimumCoordinate (fun w => (f w).1)=(f u).1 := by
    obtain ⟨w,hw,he⟩ := Probability.minimumCoordinate_mem (fun w => (f w).1) p
    rcases hp w hw with rfl | rfl
    · exact he.symm
    · exact he.symm.trans hcoord.symm
  rw [hr]
  dsimp only
  have hz : Probability.parameter (fun w => if (f u).1<(f w).1 then (1:I) else 0) p=0 := by
    rw [Probability.parameter_eq_on_support p ({u,v}:Set V) hp
      (show ∀w∈({u,v}:Set V),(if (f u).1<(f w).1 then (1:I) else 0)=0 from by
        intro w hw; rcases hw with rfl | rfl <;> simp [hcoord]),Probability.parameter_const]
  rw [hz,D.a.source]

theorem skeletonMap_horizontal (f : V → IntervalCarriers.Vertex) (p : Probability V) (u v : V)
    (hp : p.SupportedOn ({u,v} : Set V))
    (hstep : IntervalCarriers.HorizontalStep (2*D.power+1) (f u) (f v)) :
    D.skeletonMap f p=SupportPair.paritySwap H (f u).1
      (D.a ⟨p.mass v,p.nonneg v,p.mass_le_one v⟩) := by
  have hcoord : (f u).1<(f v).1 := by
    have he := congrArg Prod.fst hstep
    have hpow : 0<((2*D.power+1:ℕ):ℤ)^(f u).2 := pow_pos (by positivity) _
    change (f v).1=(f u).1+((2*D.power+1:ℕ):ℤ)^(f u).2 at he
    omega
  have hne : u≠v := by intro he; subst v; exact (lt_irrefl _ hcoord)
  by_cases hu : 0<p.mass u
  · unfold skeletonMap
    rw [Probability.minimumCoordinate_pair_left _ _ u v hp hu (le_of_lt hcoord)]
    dsimp only
    have hparam : Probability.parameter (fun w => if (f u).1<(f w).1 then (1:I) else 0) p=
        ⟨p.mass v,p.nonneg v,p.mass_le_one v⟩ := by
      apply Subtype.ext
      change Probability.weightedCoordinate _ p=p.mass v
      rw [Probability.weightedCoordinate,p.weighted_pair_sum u v hne hp]
      simp [hcoord]
    rw [hparam]
  · have hzero : p.mass u=0 := le_antisymm (le_of_not_gt hu) (p.nonneg u)
    have hpv : p.SupportedOn ({v}:Set V) := by
      intro w hw
      rcases hp w hw with rfl | rfl
      · simp [hzero] at hw
      · rfl
    rw [D.skeletonMap_singleton f p v hpv]
    have hv : (⟨p.mass v,p.nonneg v,p.mass_le_one v⟩ : I)=1 := by
      apply Subtype.ext
      have hs := p.mass_pair_sum u v hne hp
      simpa [hzero] using hs
    rw [hv,D.a.target]
    have he := congrArg Prod.fst hstep
    change (f v).1=(f u).1+((2*D.power+1:ℕ):ℤ)^(f u).2 at he
    rw [he,SupportPair.paritySwap_odd_pow]
    by_cases hr : (f u).1%2=0 <;> simp [SupportPair.paritySwap,hr,SupportPair.swap_swap]

end SupportTorsionData
end
end AbelianTargets
