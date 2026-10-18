import AbelianTargets.SimplicialChartGluing
import AbelianTargets.TriangleChartIntersections

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Global carrier projections assembled from polygon and skeleton charts. -/
namespace AbelianTargets.IntervalCarriers
noncomputable section
attribute [local instance] Classical.propDecidable

def RawSupported {K : ℕ} {A B : ℤ} (p : Probability (CarrierVertex K A B)) (s : Finset Vertex) : Prop :=
  ∀ v,0<p.mass v→v.1∈s

def SkeletonSupported {m K : ℕ} {A B : ℤ} (p : Probability (CarrierVertex K A B)) : Prop :=
  (∃ v∈carrierVertices K A B,RawSupported p {v}) ∨
    ∃ u∈carrierVertices K A B,∃ v∈carrierVertices K A B,(graph m).Adj u v ∧ RawSupported p {u,v}

def FaceHasCell {m K : ℕ} {A B : ℤ} (s : Finset (CarrierVertex K A B)) : Prop :=
  ∃ c∈carrierCells m K A B,∃ t,IsFanTriangle m c t ∧ s.image Subtype.val⊆t

theorem rawSupported_of_face {K : ℕ} {A B : ℤ} {p : Probability (CarrierVertex K A B)}
    {s : Finset (CarrierVertex K A B)} (hp : p.SupportedOn (s : Set _)) :
    RawSupported p (s.image Subtype.val) := fun v hv => Finset.mem_image.mpr ⟨v,hp v hv,rfl⟩

theorem RawSupported.mono {K : ℕ} {A B : ℤ} {p : Probability (CarrierVertex K A B)}
    {s t : Finset Vertex} (hp : RawSupported p s) (h : s⊆t) : RawSupported p t := fun v hv => h (hp v hv)

theorem skeletonSupported_without_cell {m K : ℕ} {A B : ℤ}
    {s : Finset (CarrierVertex K A B)} (hs : s∈simplexFaces m K A B) (hn : ¬FaceHasCell (m := m) s)
    {p : Probability (CarrierVertex K A B)} (hp : p.SupportedOn (s : Set _)) : SkeletonSupported (m := m) p := by
  rcases (mem_simplexFaces s).mp hs with ⟨v,hv,hsub⟩ | ⟨u,hu,v,hv,he,hsub⟩ | ⟨t,ht,hsub⟩
  · exact Or.inl ⟨v,hv,(rawSupported_of_face hp).mono hsub⟩
  · exact Or.inr ⟨u,hu,v,hv,he,(rawSupported_of_face hp).mono hsub⟩
  · obtain ⟨c,hc,hct⟩ := fanTriangle_of_carrierTriangle ht
    exact False.elim (hn ⟨c,hc,t,hct,hsub⟩)

structure CarrierProjectionCharts (m K : ℕ) (A B : ℤ) (Z : Type*) [TopologicalSpace Z] where
  skeleton : Probability (CarrierVertex K A B) → Z
  continuous_vertex : ∀ v∈carrierVertices K A B,ContinuousOn skeleton {p | RawSupported p {v}}
  continuous_edge : ∀ u∈carrierVertices K A B,∀ v∈carrierVertices K A B,(graph m).Adj u v→
    ContinuousOn skeleton {p | RawSupported p {u,v}}
  cell : Vertex → Probability (CarrierVertex K A B) → Z
  continuous_cell : ∀ c∈carrierCells m K A B,Continuous (cell c)
  cell_skeleton : ∀ c∈carrierCells m K A B,∀ t,IsFanTriangle m c t→
    ∀ p,RawSupported p t→SkeletonSupported (m := m) p→cell c p=skeleton p

namespace CarrierProjectionCharts
variable {m K : ℕ} {A B : ℤ} {Z : Type*} [TopologicalSpace Z]

def faceValue (D : CarrierProjectionCharts m K A B Z) (s : Finset (CarrierVertex K A B))
    (p : Probability (CarrierVertex K A B)) : Z :=
  if h : FaceHasCell (m := m) s then D.cell h.choose p else D.skeleton p

theorem continuous_faceValue (D : CarrierProjectionCharts m K A B Z)
    (s : Finset (CarrierVertex K A B)) (hs : s∈simplexFaces m K A B) :
    Continuous (fun p : ProbabilityFace s => D.faceValue s p.1) := by
  by_cases h : FaceHasCell (m := m) s
  · simpa only [faceValue,dif_pos h] using
      (D.continuous_cell h.choose h.choose_spec.1).comp continuous_subtype_val
  · have hc : ContinuousOn D.skeleton {p | p.SupportedOn (s : Set _)} := by
      rcases (mem_simplexFaces s).mp hs with ⟨v,hv,hsub⟩ | ⟨u,hu,v,hv,he,hsub⟩ | ⟨t,ht,hsub⟩
      · exact (D.continuous_vertex v hv).mono (fun p hp => (rawSupported_of_face hp).mono hsub)
      · exact (D.continuous_edge u hu v hv he).mono (fun p hp => (rawSupported_of_face hp).mono hsub)
      · obtain ⟨c,hc,hct⟩ := fanTriangle_of_carrierTriangle ht
        exact False.elim (h ⟨c,hc,t,hct,hsub⟩)
    simpa only [faceValue,dif_neg h] using continuousOn_iff_continuous_restrict.mp hc

private theorem raw_positiveSupport_nonempty {K : ℕ} {A B : ℤ}
    (p : Probability (CarrierVertex K A B)) : (p.positiveSupport.image Subtype.val).Nonempty := by
  have hp : p.positiveSupport.Nonempty := by
    by_contra hn
    have hz : ∀ v,p.mass v=0 := by
      intro v
      have hv : ¬0<p.mass v := fun h => hn ⟨v,(Probability.mem_positiveSupport p v).mpr h⟩
      exact le_antisymm (le_of_not_gt hv) (p.nonneg v)
    have he := p.sum_one
    simp only [hz,Finset.sum_const_zero] at he
    norm_num at he
  exact hp.image _

private theorem shared_cell_skeleton (hm : 1≤m) {p : Probability (CarrierVertex K A B)}
    {c d : Vertex} {s t : Finset Vertex} (hs : IsFanTriangle m c s) (ht : IsFanTriangle m d t)
    (hcd : c≠d) (hp : RawSupported p s) (hq : RawSupported p t) : SkeletonSupported (m := m) p := by
  let u := p.positiveSupport.image Subtype.val
  have hus : u⊆s := by
    intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact hp w ((Probability.mem_positiveSupport p w).mp hw)
  have hut : u⊆t := by
    intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact hq w ((Probability.mem_positiveSupport p w).mp hw)
  have huv : u⊆carrierVertices K A B := by
    intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact w.2
  have hpu : RawSupported p u := rawSupported_of_face (Probability.supportedOn_positiveSupport p)
  rcases different_fan_origins_shared_face hm hs ht hcd hus hut (raw_positiveSupport_nonempty p) huv with
    ⟨v,hv,hsub⟩ | ⟨v,hv,w,hw,he,hsub⟩
  · exact Or.inl ⟨v,hv,hpu.mono hsub⟩
  · exact Or.inr ⟨v,hv,w,hw,he,hpu.mono hsub⟩

theorem faceValue_agree (D : CarrierProjectionCharts m K A B Z) (hm : 1≤m)
    (s : Finset (CarrierVertex K A B)) (hs : s∈simplexFaces m K A B)
    (t : Finset (CarrierVertex K A B)) (ht : t∈simplexFaces m K A B)
    (p : Probability (CarrierVertex K A B)) (hp : p.SupportedOn (s : Set _))
    (hq : p.SupportedOn (t : Set _)) : D.faceValue s p=D.faceValue t p := by
  by_cases hc : FaceHasCell (m := m) s <;> by_cases hd : FaceHasCell (m := m) t
  · simp only [faceValue,dif_pos hc,dif_pos hd]
    obtain ⟨a,ha,hpa⟩ := hc.choose_spec.2
    obtain ⟨b,hb,hpb⟩ := hd.choose_spec.2
    have hps := (rawSupported_of_face hp).mono hpa
    have hpt := (rawSupported_of_face hq).mono hpb
    by_cases he : hc.choose=hd.choose
    · rw [he]
    · have hsk := shared_cell_skeleton hm ha hb he hps hpt
      exact (D.cell_skeleton _ hc.choose_spec.1 _ ha p hps hsk).trans
        (D.cell_skeleton _ hd.choose_spec.1 _ hb p hpt hsk).symm
  · simp only [faceValue,dif_pos hc,dif_neg hd]
    obtain ⟨a,ha,hpa⟩ := hc.choose_spec.2
    exact D.cell_skeleton _ hc.choose_spec.1 _ ha p ((rawSupported_of_face hp).mono hpa)
      (skeletonSupported_without_cell ht hd hq)
  · simp only [faceValue,dif_neg hc,dif_pos hd]
    obtain ⟨b,hb,hpb⟩ := hd.choose_spec.2
    exact (D.cell_skeleton _ hd.choose_spec.1 _ hb p ((rawSupported_of_face hq).mono hpb)
      (skeletonSupported_without_cell hs hc hp)).symm
  · simp only [faceValue,dif_neg hc,dif_neg hd]

def simplicialData (D : CarrierProjectionCharts m K A B Z) (hm : 1≤m) :
    SimplicialChartData (simplexFaces m K A B) Z where
  chart s hs p := D.faceValue s p.1
  continuous_chart := D.continuous_faceValue
  agree s hs t ht p hp hq := D.faceValue_agree hm s hs t ht p hp hq

def eval (D : CarrierProjectionCharts m K A B Z) (hm : 1≤m) (p : Realization m K A B) : Z :=
  (D.simplicialData hm).eval p

theorem continuous_eval (D : CarrierProjectionCharts m K A B Z) (hm : 1≤m) :
    Continuous (D.eval hm) := (D.simplicialData hm).continuous_eval

theorem eval_eq_skeleton (D : CarrierProjectionCharts m K A B Z) (hm : 1≤m)
    (p : Realization m K A B) (hsk : SkeletonSupported (m := m) p.1) : D.eval hm p=D.skeleton p.1 := by
  obtain ⟨s,hs,hp⟩ := p.2
  rw [eval,(D.simplicialData hm).eval_eq_chart p s hs hp]
  change D.faceValue s p.1=D.skeleton p.1
  by_cases hc : FaceHasCell (m := m) s
  · rw [faceValue,dif_pos hc]
    obtain ⟨a,ha,hpa⟩ := hc.choose_spec.2
    exact D.cell_skeleton _ hc.choose_spec.1 _ ha p.1 ((rawSupported_of_face hp).mono hpa) hsk
  · simp only [faceValue,dif_neg hc]

theorem eval_eq_cell (D : CarrierProjectionCharts m K A B Z) (hm : 1≤m)
    (p : Realization m K A B) (c : Vertex) (hc : c∈carrierCells m K A B)
    (t : Finset Vertex) (ht : IsFanTriangle m c t) (hp : RawSupported p.1 t) :
    D.eval hm p=D.cell c p.1 := by
  let s := p.1.positiveSupport
  have hs : s∈simplexFaces m K A B := positiveSupport_mem p
  have hps := Probability.supportedOn_positiveSupport p.1
  have hsub : s.image Subtype.val⊆t := by
    intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact hp w ((Probability.mem_positiveSupport p.1 w).mp hw)
  have hcell : FaceHasCell (m := m) s := ⟨c,hc,t,ht,hsub⟩
  rw [eval,(D.simplicialData hm).eval_eq_chart p s hs hps]
  change D.faceValue s p.1=D.cell c p.1
  rw [faceValue,dif_pos hcell]
  obtain ⟨a,ha,hpa⟩ := hcell.choose_spec.2
  have hpa' := (rawSupported_of_face hps).mono hpa
  by_cases he : hcell.choose=c
  · rw [he]
  · have hsk := shared_cell_skeleton hm ha ht he hpa' hp
    exact (D.cell_skeleton _ hcell.choose_spec.1 _ ha p.1 hpa' hsk).trans
      (D.cell_skeleton c hc t ht p.1 hp hsk).symm

end CarrierProjectionCharts
end
end AbelianTargets.IntervalCarriers
