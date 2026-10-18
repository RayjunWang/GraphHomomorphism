import AbelianTargets.CarrierGeometry
import AbelianTargets.ProbabilityPushGeometry

set_option backward.isDefEq.respectTransparency false

/-! Literal horizontal translation is an isometry of barycentric carriers. -/
namespace AbelianTargets.IntervalCarriers
noncomputable section
attribute [local instance] Classical.propDecidable

theorem translate_mem_carrierCells {m K : ℕ} {A B : ℤ} (a : ℤ) (c : Vertex) :
    translate a c ∈ carrierCells m K (A+a) (B+a) ↔ c ∈ carrierCells m K A B := by
  simp only [carrierCells,Finset.mem_filter,mem_carrierVertices,translate]
  omega

theorem translate_lowerTriangle (m : ℕ) (c : Vertex) (n : ℕ) (a : ℤ) :
    (lowerTriangle m c n).image (translate a)=lowerTriangle m (translate a c) n := by
  simp [lowerTriangle,translate,upperLeft,lowerVertex,add_assoc,add_comm,add_left_comm]

theorem translate_upperTriangle (m : ℕ) (c : Vertex) (a : ℤ) :
    (upperTriangle m c).image (translate a)=upperTriangle m (translate a c) := by
  simp [upperTriangle,translate,upperLeft,upperRight,lowerVertex,add_assoc,add_comm,add_left_comm]

theorem translate_carrierTriangle {m K : ℕ} {A B : ℤ} {s : Finset Vertex}
    (hs : s ∈ carrierTriangles m K A B) (a : ℤ) :
    s.image (translate a) ∈ carrierTriangles m K (A+a) (B+a) := by
  obtain ⟨c,hc,hs⟩ := Finset.mem_biUnion.mp hs
  have hc' := (translate_mem_carrierCells a c).mpr hc
  rcases Finset.mem_insert.mp hs with he | he
  · subst s; rw [translate_upperTriangle]; exact mem_carrierTriangles_upper hc'
  · obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp he
    rw [translate_lowerTriangle]
    exact mem_carrierTriangles_lower hc' (Finset.mem_range.mp hn)

theorem CarrierFace.translated {m K : ℕ} {A B : ℤ} {s : Finset Vertex}
    (hs : CarrierFace m K A B s) (a : ℤ) :
    CarrierFace m K (A+a) (B+a) (s.image (translate a)) := by
  rcases hs with ⟨v,hv,hs⟩ | ⟨u,hu,v,hv,he,hs⟩ | ⟨t,ht,hs⟩
  · exact Or.inl ⟨translate a v,(translate_mem_carrierVertices a v).mpr hv,
      by simpa only [Finset.image_singleton] using Finset.image_subset_image hs⟩
  · have he' : (graph m).Adj (translate a u) (translate a v) :=
      (carrierTranslation m K A B a).map_rel_iff.mpr (show (carrierGraph m K A B).Adj ⟨u,hu⟩ ⟨v,hv⟩ from he)
    exact Or.inr (Or.inl ⟨translate a u,(translate_mem_carrierVertices a u).mpr hu,
      translate a v,(translate_mem_carrierVertices a v).mpr hv,he',
      by simpa only [Finset.image_insert,Finset.image_singleton] using Finset.image_subset_image hs⟩)
  · exact Or.inr (Or.inr ⟨t.image (translate a),translate_carrierTriangle ht a,Finset.image_subset_image hs⟩)

def vertexTranslation {K : ℕ} {A B : ℤ} (a : ℤ) (v : CarrierVertex K A B) : CarrierVertex K (A+a) (B+a) :=
  ⟨translate a v.1,(translate_mem_carrierVertices a v.1).mpr v.2⟩

theorem vertexTranslation_injective {K : ℕ} {A B : ℤ} (a : ℤ) :
    Function.Injective (vertexTranslation (K := K) (A := A) (B := B) a) := by
  intro u v h
  apply Subtype.ext
  have he := congrArg (fun w : CarrierVertex K (A+a) (B+a) => translate (-a) w.1) h
  simpa [vertexTranslation,translate] using he

def realizationTranslation {m K : ℕ} {A B : ℤ} (a : ℤ) (p : Realization m K A B) :
    Realization m K (A+a) (B+a) := by
  refine ⟨Probability.push (vertexTranslation a) p.1,?_⟩
  obtain ⟨s,hs,hp⟩ := p.2
  refine ⟨s.image (vertexTranslation a),?_,?_⟩
  · apply (mem_simplexFaces _).mpr
    rw [Finset.image_image]
    change CarrierFace m K (A+a) (B+a) (s.image (translate a ∘ Subtype.val))
    rw [←Finset.image_image]
    exact ((mem_simplexFaces s).mp hs).translated a
  · intro w hw
    obtain ⟨v,hv,hvp⟩ := (Probability.push_pos_iff (vertexTranslation a) p.1 w).mp hw
    exact Finset.mem_image.mpr ⟨v,hp v hvp,hv⟩

theorem realizationTranslation_isometry {m K : ℕ} {A B : ℤ} (a : ℤ) :
    Isometry (realizationTranslation (m := m) (K := K) (A := A) (B := B) a) := by
  apply Isometry.of_dist_eq
  intro p q
  exact (Probability.isometry_push (vertexTranslation a) (vertexTranslation_injective a)).dist_eq p.1 q.1

end
end AbelianTargets.IntervalCarriers
