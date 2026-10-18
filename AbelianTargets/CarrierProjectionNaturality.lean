import AbelianTargets.CarrierSupportProjection
import AbelianTargets.SupportChartNaturality
import AbelianTargets.CarrierIntervalInclusion
import AbelianTargets.CarrierNesting
import AbelianTargets.CarrierTranslationGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AbelianTargets
noncomputable section
attribute [local instance] Classical.propDecidable

namespace IntervalCarriers

theorem realization_skeleton_or_cell {m K : ℕ} {A B : ℤ} (p : Realization m K A B) :
    SkeletonSupported (m := m) p.1 ∨
      ∃ c∈carrierCells m K A B,∃ t,IsFanTriangle m c t ∧ RawSupported p.1 t := by
  obtain ⟨s,hs,hp⟩ := p.2
  have hr := rawSupported_of_face hp
  rcases (mem_simplexFaces s).mp hs with ⟨v,hv,hsub⟩ | ⟨u,hu,v,hv,he,hsub⟩ | ⟨t,ht,hsub⟩
  · exact Or.inl (Or.inl ⟨v,hv,hr.mono hsub⟩)
  · exact Or.inl (Or.inr ⟨u,hu,v,hv,he,hr.mono hsub⟩)
  · obtain ⟨c,hc,hct⟩ := fanTriangle_of_carrierTriangle ht
    exact Or.inr ⟨c,hc,t,hct,hr.mono hsub⟩

theorem RawSupported.push_same {K T : ℕ} {A B C D : ℤ}
    (f : CarrierVertex K A B → CarrierVertex T C D)
    (hf : ∀v,(f v).1=v.1) {p : Probability (CarrierVertex K A B)}
    {s : Finset Vertex} (hp : RawSupported p s) : RawSupported (Probability.push f p) s := by
  intro w hw
  obtain ⟨v,hv,hpv⟩ := (Probability.push_pos_iff f p w).mp hw
  rw [←hv,hf]
  exact hp v hpv

theorem SkeletonSupported.push_same {m K T : ℕ} {A B C D : ℤ}
    (f : CarrierVertex K A B → CarrierVertex T C D)
    (hf : ∀v,(f v).1=v.1) {p : Probability (CarrierVertex K A B)}
    (hp : SkeletonSupported (m := m) p) : SkeletonSupported (m := m) (Probability.push f p) := by
  have hm : ∀v∈carrierVertices K A B,v∈carrierVertices T C D := by
    intro v hv
    have h := (f ⟨v,hv⟩).2
    simpa only [hf] using h
  rcases hp with ⟨v,hv,hp⟩ | ⟨u,hu,v,hv,he,hp⟩
  · exact Or.inl ⟨v,hm v hv,hp.push_same f hf⟩
  · exact Or.inr ⟨u,hm u hu,v,hm v hv,he,hp.push_same f hf⟩

theorem IsFanTriangle.translated {m : ℕ} {c : Vertex} {t : Finset Vertex}
    (ht : IsFanTriangle m c t) (a : ℤ) : IsFanTriangle m (translate a c) (t.image (translate a)) := by
  rcases ht with rfl | ⟨n,hn,rfl⟩
  · exact Or.inl (translate_upperTriangle m c a)
  · exact Or.inr ⟨n,hn,translate_lowerTriangle m c n a⟩

theorem RawSupported.push_translate {K : ℕ} {A B : ℤ} (a : ℤ)
    {p : Probability (CarrierVertex K A B)} {s : Finset Vertex} (hp : RawSupported p s) :
    RawSupported (Probability.push (vertexTranslation a) p) (s.image (translate a)) := by
  intro w hw
  obtain ⟨v,hv,hpv⟩ := (Probability.push_pos_iff (vertexTranslation a) p w).mp hw
  rw [←hv]
  exact Finset.mem_image.mpr ⟨v.1,hp v hpv,rfl⟩

theorem SkeletonSupported.push_translate {m K : ℕ} {A B : ℤ} (a : ℤ)
    {p : Probability (CarrierVertex K A B)} (hp : SkeletonSupported (m := m) p) :
    SkeletonSupported (m := m) (Probability.push (vertexTranslation a) p) := by
  rcases hp with ⟨v,hv,hp⟩ | ⟨u,hu,v,hv,he,hp⟩
  · refine Or.inl ⟨translate a v,(translate_mem_carrierVertices a v).mpr hv,?_⟩
    simpa only [Finset.image_singleton] using hp.push_translate a
  · have he' : (graph m).Adj (translate a u) (translate a v) :=
      (carrierTranslation m K A B a).map_rel_iff.mpr
        (show (carrierGraph m K A B).Adj ⟨u,hu⟩ ⟨v,hv⟩ from he)
    refine Or.inr ⟨translate a u,(translate_mem_carrierVertices a u).mpr hu,
      translate a v,(translate_mem_carrierVertices a v).mpr hv,he',?_⟩
    simpa only [Finset.image_insert,Finset.image_singleton] using hp.push_translate a

end IntervalCarriers

namespace SupportTorsionData
open IntervalCarriers
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)

@[simp] theorem carrierProjection_point {K : ℕ} {A B : ℤ} (v : CarrierVertex K A B) :
    D.carrierProjection K A B (point v)=SupportPair.paritySwap H v.1.1 D.base := by
  have hp : (Probability.dirac v).SupportedOn ({v} : Set (CarrierVertex K A B)) :=
    Probability.supportedOn_dirac v (by simp)
  have hraw : RawSupported (point v : Realization (2*D.power+1) K A B).1 {v.1} := by
    intro w hw
    have he : w=v := hp w hw
    simp [he]
  have hsk : SkeletonSupported (m := 2*D.power+1) (point v : Realization (2*D.power+1) K A B).1 :=
    Or.inl ⟨v.1,v.2,hraw⟩
  rw [carrierProjection,(D.projectionCharts K A B).eval_eq_skeleton (by omega) _ hsk]
  exact D.skeletonMap_singleton Subtype.val _ v hp

theorem carrierProjection_push_same {K T : ℕ} {A B C E : ℤ}
    (f : CarrierVertex K A B → CarrierVertex T C E) (hf : ∀v,(f v).1=v.1)
    (hc : carrierCells (2*D.power+1) K A B ⊆ carrierCells (2*D.power+1) T C E)
    (i : Realization (2*D.power+1) K A B → Realization (2*D.power+1) T C E)
    (hi : ∀p,(i p).1=Probability.push f p.1)
    (p : Realization (2*D.power+1) K A B) : D.carrierProjection T C E (i p)=D.carrierProjection K A B p := by
  have hf' : (Subtype.val : CarrierVertex T C E → Vertex) ∘ f=Subtype.val := by funext v; exact hf v
  rcases realization_skeleton_or_cell p with hsk | ⟨c,hc',t,ht,hpt⟩
  · have hsk' : SkeletonSupported (m := 2*D.power+1) (i p).1 := by
      rw [hi]
      exact hsk.push_same f hf
    rw [carrierProjection,(D.projectionCharts T C E).eval_eq_skeleton (by omega) _ hsk']
    rw [carrierProjection,(D.projectionCharts K A B).eval_eq_skeleton (by omega) _ hsk]
    change D.skeletonMap Subtype.val (i p).1=D.skeletonMap Subtype.val p.1
    rw [hi,D.skeletonMap_push,hf']
  · have hpt' : RawSupported (i p).1 t := by rw [hi]; exact hpt.push_same f hf
    rw [carrierProjection,(D.projectionCharts T C E).eval_eq_cell (by omega) _ c (hc hc') t ht hpt']
    rw [carrierProjection,(D.projectionCharts K A B).eval_eq_cell (by omega) _ c hc' t ht hpt]
    change D.cellChart Subtype.val c (i p).1=D.cellChart Subtype.val c p.1
    rw [hi,D.cellChart_push,hf']

theorem carrierProjection_intervalInclusion {K : ℕ} {A B C E : ℤ}
    (hAC : A ≤ C) (hEB : E ≤ B) (p : Realization (2*D.power+1) K C E) :
    D.carrierProjection K A B (intervalInclusion hAC hEB p)=D.carrierProjection K C E p :=
  D.carrierProjection_push_same (intervalVertexInclusion hAC hEB) (fun _ => rfl)
    (carrierCells_mono hAC hEB) (intervalInclusion hAC hEB) (fun _ => rfl) p

theorem carrierProjection_heightInclusion {K T : ℕ} {A B : ℤ}
    (hKT : K ≤ T) (p : Realization (2*D.power+1) K A B) :
    D.carrierProjection T A B (carrierInclude hKT p)=D.carrierProjection K A B p :=
  D.carrierProjection_push_same (vertexInclude hKT) (fun _ => rfl)
    (carrierCells_height_mono hKT) (carrierInclude hKT) (fun _ => rfl) p

theorem carrierProjection_translate {K : ℕ} {A B : ℤ} (a : ℤ)
    (p : Realization (2*D.power+1) K A B) :
    D.carrierProjection K (A+a) (B+a) (realizationTranslation a p)=
      SupportPair.paritySwap H a (D.carrierProjection K A B p) := by
  have hf : (Subtype.val : CarrierVertex K (A+a) (B+a) → Vertex) ∘ vertexTranslation a=
      translate a ∘ (Subtype.val : CarrierVertex K A B → Vertex) := rfl
  rcases realization_skeleton_or_cell p with hsk | ⟨c,hc,t,ht,hpt⟩
  · have hsk' : SkeletonSupported (m := 2*D.power+1) (realizationTranslation a p).1 := hsk.push_translate a
    rw [carrierProjection,(D.projectionCharts K (A+a) (B+a)).eval_eq_skeleton (by omega) _ hsk']
    rw [carrierProjection,(D.projectionCharts K A B).eval_eq_skeleton (by omega) _ hsk]
    change D.skeletonMap Subtype.val (Probability.push (vertexTranslation a) p.1)=
      SupportPair.paritySwap H a (D.skeletonMap Subtype.val p.1)
    rw [D.skeletonMap_push,hf,D.skeletonMap_translate]
  · have hc' := (translate_mem_carrierCells a c).mpr hc
    have ht' := ht.translated a
    have hpt' : RawSupported (realizationTranslation a p).1 (t.image (translate a)) := hpt.push_translate a
    rw [carrierProjection,(D.projectionCharts K (A+a) (B+a)).eval_eq_cell (by omega) _ (translate a c) hc' _ ht' hpt']
    rw [carrierProjection,(D.projectionCharts K A B).eval_eq_cell (by omega) _ c hc t ht hpt]
    change D.cellChart Subtype.val (translate a c) (Probability.push (vertexTranslation a) p.1)=
      SupportPair.paritySwap H a (D.cellChart Subtype.val c p.1)
    rw [D.cellChart_push,hf,D.cellChart_translate]

end SupportTorsionData
end
end AbelianTargets
