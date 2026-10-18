import AbelianTargets.CarrierGeometry

namespace AbelianTargets.IntervalCarriers

theorem mem_carrierVertices_lower {K : ℕ} {A B : ℤ} {v : Vertex}
    (hv : v ∈ carrierVertices (K+1) A B) (hheight : v.2 ≤ K) : v ∈ carrierVertices K A B :=
  mem_carrierVertices.mpr ⟨(mem_carrierVertices.mp hv).1,(mem_carrierVertices.mp hv).2.1,hheight⟩

theorem lower_vertex_mem {K : ℕ} {A B : ℤ} (v : Vertex)
    (hv : v ∈ carrierVertices (K+1) A B) : (v.1,min v.2 K) ∈ carrierVertices K A B :=
  mem_carrierVertices.mpr ⟨(mem_carrierVertices.mp hv).1,(mem_carrierVertices.mp hv).2.1,min_le_right _ _⟩

theorem subset_pair_drop_left {V : Type*} [DecidableEq V] {s : Finset V} {x y : V}
    (hs : s ⊆ {x,y}) (hx : x ∉ s) : s ⊆ {y} := by
  intro v hv
  have h := hs hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at h ⊢
  rcases h with h | h
  · exact (hx (by simpa only [h] using hv)).elim
  · exact h

theorem CarrierFace.lower_of_height {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) {s : Finset Vertex}
    (hs : CarrierFace m (K+1) A B s) (hheight : ∀ v ∈ s, v.2 ≤ K) : CarrierFace m K A B s := by
  rcases hs with ⟨x,hx,hs⟩ | ⟨x,hx,y,hy,he,hs⟩ | ⟨t,ht,hs⟩
  · by_cases hxl : x.2 ≤ K
    · exact Or.inl ⟨x,mem_carrierVertices_lower hx hxl,hs⟩
    · refine Or.inl ⟨(x.1,min x.2 K),lower_vertex_mem x hx,?_⟩
      intro v hv
      have he := Finset.mem_singleton.mp (hs hv)
      exact (hxl (by simpa only [he] using hheight v hv)).elim
  · by_cases hxl : x.2 ≤ K
    · by_cases hyl : y.2 ≤ K
      · exact Or.inr (Or.inl ⟨x,mem_carrierVertices_lower hx hxl,y,mem_carrierVertices_lower hy hyl,he,hs⟩)
      · have hyn : y ∉ s := fun h => hyl (hheight y h)
        exact Or.inl ⟨x,mem_carrierVertices_lower hx hxl,
          subset_pair_drop_left (by simpa only [Finset.pair_comm] using hs) hyn⟩
    · have hxn : x ∉ s := fun h => hxl (hheight x h)
      have hs' := subset_pair_drop_left hs hxn
      by_cases hyl : y.2 ≤ K
      · exact Or.inl ⟨y,mem_carrierVertices_lower hy hyl,hs'⟩
      · refine Or.inl ⟨(x.1,min x.2 K),lower_vertex_mem x hx,?_⟩
        intro v hv
        have he := Finset.mem_singleton.mp (hs' hv)
        exact (hyl (by simpa only [he] using hheight v hv)).elim
  · obtain ⟨c,hc,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨hcv,hcj,hcr⟩ := Finset.mem_filter.mp hc
    by_cases hcl : c.2 < K
    · have hc' : c ∈ carrierCells m K A B :=
        Finset.mem_filter.mpr ⟨mem_carrierVertices_lower hcv (by omega),hcl,hcr⟩
      rcases Finset.mem_insert.mp ht with ht | ht
      · subst t
        exact Or.inr (Or.inr ⟨_,mem_carrierTriangles_upper hc',hs⟩)
      · obtain ⟨n,hn,ht⟩ := Finset.mem_image.mp ht
        subst t
        exact Or.inr (Or.inr ⟨_,mem_carrierTriangles_lower hc' (Finset.mem_range.mp hn),hs⟩)
    · have hcK : c.2 = K := by omega
      rcases Finset.mem_insert.mp ht with ht | ht
      · subst t
        have hvl : lowerVertex m c.1 c.2 m ∈ carrierVertices K A B :=
          mem_carrierVertices_lower (lowerVertex_mem_of_cell hc le_rfl) (by dsimp [lowerVertex]; omega)
        refine Or.inl ⟨_,hvl,?_⟩
        intro v hv
        have hv' := hs hv
        simp only [upperTriangle,Finset.mem_insert,Finset.mem_singleton] at hv'
        rcases hv' with h | h | h
        · have hh := hheight v hv
          rw [h] at hh; dsimp [upperLeft] at hh; omega
        · exact Finset.mem_singleton.mpr h
        · have hh := hheight v hv
          rw [h] at hh; dsimp [upperRight] at hh; omega
      · obtain ⟨n,hn,ht⟩ := Finset.mem_image.mp ht
        subst t
        have hnm : n < m := Finset.mem_range.mp hn
        have hvn : lowerVertex m c.1 c.2 n ∈ carrierVertices K A B :=
          mem_carrierVertices_lower (lowerVertex_mem_of_cell hc (by omega)) (by dsimp [lowerVertex]; omega)
        have hvn' : lowerVertex m c.1 c.2 (n+1) ∈ carrierVertices K A B :=
          mem_carrierVertices_lower (lowerVertex_mem_of_cell hc (by omega)) (by dsimp [lowerVertex]; omega)
        refine Or.inr (Or.inl ⟨_,hvn,_,hvn',horizontal_adj hm (lowerVertex_step _ _ _ _),?_⟩)
        intro v hv
        have hv' := hs hv
        simp only [lowerTriangle,Finset.mem_insert,Finset.mem_singleton] at hv'
        rcases hv' with h | h | h
        · have hh := hheight v hv
          rw [h] at hh; dsimp [upperLeft] at hh; omega
        · simp [h]
        · simp [h]

end AbelianTargets.IntervalCarriers
