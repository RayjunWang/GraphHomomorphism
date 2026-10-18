import AbelianTargets.CarrierHeightCut
import AbelianTargets.SimplicialSupport
import AbelianTargets.ProbabilityPushGeometry

set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets.IntervalCarriers
noncomputable section
attribute [local instance] Classical.propDecidable

theorem carrierVertices_height_mono {K T : ℕ} {A B : ℤ} (hKT : K ≤ T) :
    carrierVertices K A B ⊆ carrierVertices T A B := by
  intro v hv
  obtain ⟨hA,hB,hK⟩ := mem_carrierVertices.mp hv
  exact mem_carrierVertices.mpr ⟨hA,hB,hK.trans hKT⟩
theorem carrierCells_height_mono {m K T : ℕ} {A B : ℤ} (hKT : K ≤ T) :
    carrierCells m K A B ⊆ carrierCells m T A B := by
  intro c hc
  obtain ⟨hv,hj,hr⟩ := Finset.mem_filter.mp hc
  exact Finset.mem_filter.mpr ⟨carrierVertices_height_mono hKT hv,hj.trans_le hKT,hr⟩
theorem CarrierFace.height_mono {m K T : ℕ} {A B : ℤ} {s : Finset Vertex}
    (hs : CarrierFace m K A B s) (hKT : K ≤ T) : CarrierFace m T A B s := by
  rcases hs with ⟨v,hv,hs⟩ | ⟨u,hu,v,hv,he,hs⟩ | ⟨t,ht,hs⟩
  · exact Or.inl ⟨v,carrierVertices_height_mono hKT hv,hs⟩
  · exact Or.inr (Or.inl ⟨u,carrierVertices_height_mono hKT hu,v,carrierVertices_height_mono hKT hv,he,hs⟩)
  · obtain ⟨c,hc,ht⟩ := Finset.mem_biUnion.mp ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · subst t
      exact Or.inr (Or.inr ⟨_,mem_carrierTriangles_upper (carrierCells_height_mono hKT hc),hs⟩)
    · obtain ⟨n,hn,ht⟩ := Finset.mem_image.mp ht
      subst t
      exact Or.inr (Or.inr ⟨_,mem_carrierTriangles_lower (carrierCells_height_mono hKT hc)
        (Finset.mem_range.mp hn),hs⟩)

def vertexInclude {K T : ℕ} {A B : ℤ} (hKT : K ≤ T) (v : CarrierVertex K A B) : CarrierVertex T A B :=
  ⟨v.1,carrierVertices_height_mono hKT v.2⟩
theorem vertexInclude_injective {K T : ℕ} {A B : ℤ} (hKT : K ≤ T) :
    Function.Injective (vertexInclude (A := A) (B := B) hKT) := by
  intro u v h
  have hh : u.1 = v.1 := congrArg (fun w : CarrierVertex T A B => w.1) h
  exact Subtype.ext hh

def carrierInclude {m K T : ℕ} {A B : ℤ} (hKT : K ≤ T) (p : Realization m K A B) : Realization m T A B := by
  refine ⟨Probability.push (vertexInclude hKT) p.1,?_⟩
  obtain ⟨s,hs,hp⟩ := p.2
  refine ⟨s.image (vertexInclude hKT),?_,?_⟩
  · apply (mem_simplexFaces _).mpr
    rw [Finset.image_image]
    exact ((mem_simplexFaces s).mp hs).height_mono hKT
  · intro w hw
    obtain ⟨v,hv,hvp⟩ := (Probability.push_pos_iff (vertexInclude hKT) p.1 w).mp hw
    exact Finset.mem_image.mpr ⟨v,hp v hvp,hv⟩

theorem isometry_include {m K T : ℕ} {A B : ℤ} (hKT : K ≤ T) :
    Isometry (carrierInclude (m := m) (A := A) (B := B) hKT) := by
  apply Isometry.of_dist_eq
  intro p q
  exact (Probability.isometry_push (vertexInclude hKT) (vertexInclude_injective hKT)).dist_eq p.1 q.1

def vertexLower {K : ℕ} {A B : ℤ} (v : CarrierVertex (K+1) A B) : CarrierVertex K A B :=
  ⟨(v.1.1,min v.1.2 K),lower_vertex_mem v.1 v.2⟩

def restrictHeight {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B)
    (hp : ∀ v, 0 < p.1.mass v → v.1.2 ≤ K) : Realization m K A B := by
  refine ⟨Probability.push vertexLower p.1,?_⟩
  let s := p.1.positiveSupport
  have hs : s ∈ simplexFaces m (K+1) A B := positiveSupport_mem p
  have hface := ((mem_simplexFaces s).mp hs).lower_of_height hm (by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact hp w ((Probability.mem_positiveSupport p.1 w).mp hw))
  refine ⟨s.image vertexLower,?_,?_⟩
  · apply (mem_simplexFaces _).mpr
    rw [Finset.image_image]
    have he : s.image (fun v => (vertexLower v).1) = s.image Subtype.val := by
      apply Finset.image_congr
      intro v hv
      have hh := hp v ((Probability.mem_positiveSupport p.1 v).mp hv)
      simp only [vertexLower,min_eq_left hh,Prod.eta]
    change CarrierFace m K A B (s.image (fun v => (vertexLower v).1))
    rw [he]
    exact hface
  · intro w hw
    obtain ⟨v,hv,hvp⟩ := (Probability.push_pos_iff vertexLower p.1 w).mp hw
    exact Finset.mem_image.mpr ⟨v,(Probability.mem_positiveSupport p.1 v).mpr hvp,hv⟩

theorem include_restrictHeight {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B)
    (hp : ∀ v, 0 < p.1.mass v → v.1.2 ≤ K) :
    carrierInclude (by omega : K ≤ K+1) (restrictHeight hm p hp) = p := by
  apply Subtype.ext
  change Probability.push (vertexInclude (by omega : K ≤ K+1)) (Probability.push vertexLower p.1) = p.1
  rw [Probability.push_comp]
  apply Probability.push_eq_self
  intro v hv
  apply Subtype.ext
  simp only [Function.comp_def,vertexInclude,vertexLower,min_eq_left (hp v hv),Prod.eta]

abbrev LowerHeight (m K : ℕ) (A B : ℤ) :=
  {p : Realization m (K+1) A B // ∀ v, 0 < p.1.mass v → v.1.2 ≤ K}

def lowerHeightEquiv {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) : Realization m K A B ≃ᵢ LowerHeight m K A B where
  toFun p := ⟨carrierInclude (by omega) p,by
    intro v hv
    obtain ⟨u,hu,hup⟩ := (Probability.push_pos_iff (vertexInclude (by omega)) p.1 v).mp hv
    rw [←hu]
    exact (mem_carrierVertices.mp u.2).2.2⟩
  invFun p := restrictHeight hm p.1 p.2
  left_inv p := by
    apply (isometry_include (m := m) (A := A) (B := B) (by omega : K ≤ K+1)).injective
    exact include_restrictHeight hm _ _
  right_inv p := Subtype.ext (include_restrictHeight hm p.1 p.2)
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro p q
    exact (isometry_include (m := m) (A := A) (B := B) (by omega : K ≤ K+1)).dist_eq p q

end
end AbelianTargets.IntervalCarriers

