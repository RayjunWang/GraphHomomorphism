import AbelianTargets.CarrierNesting

set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets.IntervalCarriers
noncomputable section
attribute [local instance] Classical.propDecidable

theorem CarrierFace.of_height_le {m K T : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (hKT : K ≤ T) {s : Finset Vertex} (hs : CarrierFace m T A B s)
    (hheight : ∀ v ∈ s,v.2 ≤ K) : CarrierFace m K A B s := by
  induction T generalizing K with
  | zero =>
    have he : K=0 := by omega
    subst K
    exact hs
  | succ T ih =>
    by_cases h : K ≤ T
    · exact ih h (hs.lower_of_height hm (fun v hv => (hheight v hv).trans h)) hheight
    · have he : K=T+1 := by omega
      subst K
      exact hs

def vertexFloor {K T : ℕ} {A B : ℤ} (v : CarrierVertex T A B) : CarrierVertex K A B :=
  ⟨(v.1.1,min v.1.2 K),mem_carrierVertices.mpr
    ⟨(mem_carrierVertices.mp v.2).1,(mem_carrierVertices.mp v.2).2.1,min_le_right _ _⟩⟩

/-- Restrict an actual probability realization whose positive support has height at most `K`.
No geometric existence hypothesis is added: the face witness is lowered one layer at a time. -/
def restrictCarrierHeight {m K T : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hKT : K ≤ T)
    (p : Realization m T A B) (hp : ∀ v,0 < p.1.mass v → v.1.2 ≤ K) :
    Realization m K A B := by
  refine ⟨Probability.push (vertexFloor (K := K)) p.1,?_⟩
  let s := p.1.positiveSupport
  have hs : s ∈ simplexFaces m T A B := positiveSupport_mem p
  have hface := ((mem_simplexFaces s).mp hs).of_height_le hm hKT (by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact hp w ((Probability.mem_positiveSupport p.1 w).mp hw))
  refine ⟨s.image (vertexFloor (K := K)),?_,?_⟩
  · apply (mem_simplexFaces _).mpr
    rw [Finset.image_image]
    have he : s.image (fun v => (vertexFloor (K := K) v).1) = s.image Subtype.val := by
      apply Finset.image_congr
      intro v hv
      have hh := hp v ((Probability.mem_positiveSupport p.1 v).mp hv)
      simp only [vertexFloor,min_eq_left hh,Prod.eta]
    change CarrierFace m K A B (s.image (fun v => (vertexFloor (K := K) v).1))
    rw [he]
    exact hface
  · intro w hw
    obtain ⟨v,hv,hvp⟩ := (Probability.push_pos_iff (vertexFloor (K := K)) p.1 w).mp hw
    exact Finset.mem_image.mpr ⟨v,(Probability.mem_positiveSupport p.1 v).mpr hvp,hv⟩

theorem carrierInclude_restrictCarrierHeight {m K T : ℕ} {A B : ℤ}
    (hm : 1 ≤ m) (hKT : K ≤ T) (p : Realization m T A B)
    (hp : ∀ v,0 < p.1.mass v → v.1.2 ≤ K) :
    carrierInclude hKT (restrictCarrierHeight hm hKT p hp)=p := by
  apply Subtype.ext
  change Probability.push (vertexInclude hKT) (Probability.push (vertexFloor (K := K)) p.1)=p.1
  rw [Probability.push_comp]
  apply Probability.push_eq_self
  intro v hv
  apply Subtype.ext
  simp only [Function.comp_def,vertexInclude,vertexFloor,min_eq_left (hp v hv),Prod.eta]

theorem restrictCarrierHeight_preserves_bottom {m K T : ℕ} {A B : ℤ}
    (hm : 1 ≤ m) (hKT : K ≤ T) (p : Realization m T A B)
    (hp : ∀ v,0 < p.1.mass v → v.1.2 ≤ K)
    (hzero : ∀ v,0 < p.1.mass v → v.1.2=0) :
    ∀ v,0 < (restrictCarrierHeight hm hKT p hp).1.mass v → v.1.2=0 := by
  intro w hw
  obtain ⟨v,hv,hvp⟩ := (Probability.push_pos_iff (vertexFloor (K := K)) p.1 w).mp hw
  rw [←hv]
  simp [vertexFloor,hzero v hvp]

end
end AbelianTargets.IntervalCarriers
