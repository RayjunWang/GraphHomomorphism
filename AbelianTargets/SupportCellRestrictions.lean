import AbelianTargets.EquivariantCellCharts
import AbelianTargets.SupportSkeletonMap

namespace AbelianTargets.SupportTorsionData
noncomputable section
open scoped unitInterval
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
variable {V : Type*} [Fintype V]

theorem cellChart_vertex (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (s : Finset IntervalCarriers.Vertex) (hs : IntervalCarriers.IsFanTriangle (2*D.power+1) c s)
    (v : V) (hv : f v∈s) :
    D.cellChart f c (Probability.dirac v)=SupportPair.paritySwap H (f v).1 D.base := by
  classical
  rcases hs with rfl | ⟨n,hn,rfl⟩
  · simp only [IntervalCarriers.upperTriangle,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with hv | hv | hv
    · exact D.cellChart_upperLeft_vertex f c v hv
    · exact D.cellChart_lower_vertex f c _ le_rfl v hv
    · exact D.cellChart_upperRight_vertex f c v hv
  · simp only [IntervalCarriers.lowerTriangle,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with hv | hv | hv
    · exact D.cellChart_upperLeft_vertex f c v hv
    · exact D.cellChart_lower_vertex f c n (by omega) v hv
    · exact D.cellChart_lower_vertex f c (n+1) (by omega) v hv

theorem cellChart_supported_lower_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (n : ℕ) (hn : n<2*D.power+1) (p : Probability V) (l r : V)
    (hp : p.SupportedOn ({l,r}:Set V))
    (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 n)
    (hr : f r=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 (n+1)) :
    D.cellChart f c p=D.skeletonMap f p := by
  have hs : IntervalCarriers.HorizontalStep (2*D.power+1) (f l) (f r) := by
    rw [hl,hr]; exact IntervalCarriers.lowerVertex_step _ _ _ _
  have hne : l≠r := by
    intro he; subst r
    exact (IntervalCarriers.horizontal_adj (by omega) hs).ne rfl
  rw [D.skeletonMap_horizontal f p l r hp hs]
  conv_lhs => rw [p.eq_mix_dirac_of_pair l r hne hp]
  exact D.cellChart_lower_edge f c n hn l r hl hr _

theorem cellChart_supported_upper_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (p : Probability V) (u v : V) (hp : p.SupportedOn ({u,v}:Set V))
    (hu : f u=IntervalCarriers.upperLeft c.1 c.2)
    (hv : f v=IntervalCarriers.upperRight (2*D.power+1) c.1 c.2) :
    D.cellChart f c p=D.skeletonMap f p := by
  have hs : IntervalCarriers.HorizontalStep (2*D.power+1) (f u) (f v) := by rw [hu,hv]; rfl
  have hne : u≠v := by
    intro he; subst v
    exact (IntervalCarriers.horizontal_adj (by omega) hs).ne rfl
  rw [D.skeletonMap_horizontal f p u v hp hs]
  conv_lhs => rw [p.eq_mix_dirac_of_pair u v hne hp]
  exact D.cellChart_upper_edge f c u v hu hv _

theorem cellChart_supported_left_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (p : Probability V) (l u : V) (hp : p.SupportedOn ({l,u}:Set V))
    (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 0)
    (hu : f u=IntervalCarriers.upperLeft c.1 c.2) :
    D.cellChart f c p=D.skeletonMap f p := by
  have hc : (f l).1=(f u).1 := by simp [hl,hu,IntervalCarriers.lowerVertex,IntervalCarriers.upperLeft]
  have hne : l≠u := by
    intro he; subst u
    have hh := congrArg Prod.snd (hl.symm.trans hu)
    simp [IntervalCarriers.lowerVertex,IntervalCarriers.upperLeft] at hh
  rw [D.skeletonMap_vertical f p l u hp hc]
  conv_lhs => rw [p.eq_mix_dirac_of_pair l u hne hp]
  exact D.cellChart_left_edge f c l u hl hu _

theorem cellChart_supported_right_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (p : Probability V) (l v : V) (hp : p.SupportedOn ({l,v}:Set V))
    (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 (2*D.power+1))
    (hv : f v=IntervalCarriers.upperRight (2*D.power+1) c.1 c.2) :
    D.cellChart f c p=D.skeletonMap f p := by
  have hc : (f l).1=(f v).1 := by
    rw [hl,hv]
    dsimp [IntervalCarriers.lowerVertex,IntervalCarriers.upperRight]
    rw [pow_succ,mul_comm]
  have hne : l≠v := by
    intro he; subst v
    have hh := congrArg Prod.snd (hl.symm.trans hv)
    simp [IntervalCarriers.lowerVertex,IntervalCarriers.upperRight] at hh
  rw [D.skeletonMap_vertical f p l v hp hc]
  conv_lhs => rw [p.eq_mix_dirac_of_pair l v hne hp]
  exact D.cellChart_right_edge f c l v hl hv _

theorem cellChart_supported_pair (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (s : Finset IntervalCarriers.Vertex) (hs : IntervalCarriers.IsFanTriangle (2*D.power+1) c s)
    (p : Probability V) (u v : V) (hp : p.SupportedOn ({u,v}:Set V))
    (hu : f u∈s) (hv : f v∈s) (he : (IntervalCarriers.graph (2*D.power+1)).Adj (f u) (f v)) :
    D.cellChart f c p=D.skeletonMap f p := by
  classical
  have pairCases : ∀a b:IntervalCarriers.Vertex,
      ({f u,f v}:Finset _)=({a,b}:Finset _) →
        (f u=a ∧ f v=b) ∨ (f u=b ∧ f v=a) := by
    intro a b h
    apply Set.pair_eq_pair_iff.mp
    have hcoe := congrArg (fun s:Finset IntervalCarriers.Vertex => (s:Set IntervalCarriers.Vertex)) h
    simpa only [Finset.coe_insert,Finset.coe_singleton] using hcoe
  have hp' : p.SupportedOn ({v,u}:Set V) := by simpa [Set.pair_comm] using hp
  rcases hs with rfl | ⟨n,hn,rfl⟩
  · rcases IntervalCarriers.upperTriangle_skeleton_edge (by omega) c hu hv he with h | h
    · rcases pairCases _ _ h with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact D.cellChart_supported_upper_edge f c p u v hp ha hb
      · exact D.cellChart_supported_upper_edge f c p v u hp' hb ha
    · rcases pairCases _ _ h with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact D.cellChart_supported_right_edge f c p u v hp ha hb
      · exact D.cellChart_supported_right_edge f c p v u hp' hb ha
  · rcases IntervalCarriers.lowerTriangle_skeleton_edge (by omega) c n hu hv he with h | ⟨rfl,h⟩
    · rcases pairCases _ _ h with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact D.cellChart_supported_lower_edge f c n hn p u v hp ha hb
      · exact D.cellChart_supported_lower_edge f c n hn p v u hp' hb ha
    · rcases pairCases _ _ h with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact D.cellChart_supported_left_edge f c p v u hp' hb ha
      · exact D.cellChart_supported_left_edge f c p u v hp ha hb

end
end AbelianTargets.SupportTorsionData
