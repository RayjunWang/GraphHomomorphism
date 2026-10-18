import AbelianTargets.ProbabilityPushGeometry

/-! Literal isometric inclusions of nested bounded interval carriers. -/

namespace AbelianTargets.IntervalCarriers
noncomputable section
variable {m K : ℕ} {A B C D : ℤ}

theorem carrierTriangles_mono_interval (hAC : A ≤ C) (hDB : D ≤ B) :
    carrierTriangles m K C D ⊆ carrierTriangles m K A B := by
  intro t ht
  obtain ⟨c,hc,ht⟩ := Finset.mem_biUnion.mp ht
  exact Finset.mem_biUnion.mpr ⟨c,carrierCells_mono hAC hDB hc,ht⟩

theorem CarrierFace.mono_interval {s : Finset Vertex}
    (hs : CarrierFace m K C D s) (hAC : A ≤ C) (hDB : D ≤ B) : CarrierFace m K A B s := by
  rcases hs with ⟨v,hv,hsv⟩ | ⟨u,hu,v,hv,he,hsv⟩ | ⟨t,ht,hst⟩
  · exact Or.inl ⟨v,carrierVertices_mono hAC hDB hv,hsv⟩
  · exact Or.inr (Or.inl ⟨u,carrierVertices_mono hAC hDB hu,v,
      carrierVertices_mono hAC hDB hv,he,hsv⟩)
  · exact Or.inr (Or.inr ⟨t,carrierTriangles_mono_interval hAC hDB ht,hst⟩)

def intervalVertexInclusion (hAC : A ≤ C) (hDB : D ≤ B) :
    CarrierVertex K C D → CarrierVertex K A B :=
  fun v => ⟨v.val,carrierVertices_mono hAC hDB v.property⟩

theorem intervalVertexInclusion_injective (hAC : A ≤ C) (hDB : D ≤ B) :
    Function.Injective (intervalVertexInclusion (K := K) hAC hDB) :=
  fun v w he => Subtype.ext (congrArg (fun u : CarrierVertex K A B => u.val) he)

def intervalInclusion (hAC : A ≤ C) (hDB : D ≤ B) :
    Realization m K C D → Realization m K A B := by
  classical
  intro p
  let f := intervalVertexInclusion (K := K) hAC hDB
  refine ⟨Probability.push f p.val,?_⟩
  obtain ⟨s,hs,hp⟩ := p.property
  refine ⟨s.image f,?_,?_⟩
  · apply (mem_simplexFaces _).mpr
    have he : (s.image f).image Subtype.val=s.image Subtype.val := by
      simp only [Finset.image_image]
      rfl
    rw [he]
    exact ((mem_simplexFaces s).mp hs).mono_interval hAC hDB
  · intro w hw
    obtain ⟨v,hvw,hpv⟩ := (Probability.push_pos_iff f p.val w).mp hw
    exact Finset.mem_image.mpr ⟨v,hp v hpv,hvw⟩

@[simp] theorem intervalInclusion_val (hAC : A ≤ C) (hDB : D ≤ B)
    (p : Realization m K C D) :
    (intervalInclusion hAC hDB p).val=Probability.push (intervalVertexInclusion hAC hDB) p.val := by
  rfl

theorem intervalInclusion_isometry (hAC : A ≤ C) (hDB : D ≤ B) :
    Isometry (intervalInclusion (m := m) (K := K) hAC hDB) := by
  apply Isometry.of_dist_eq
  intro p q
  change dist (Probability.push (intervalVertexInclusion hAC hDB) p.val)
    (Probability.push (intervalVertexInclusion hAC hDB) q.val)=dist p.val q.val
  exact (Probability.isometry_push _ (intervalVertexInclusion_injective hAC hDB)).dist_eq p.val q.val

theorem intervalInclusion_comp {E F : ℤ}
    (hAC : A ≤ C) (hDB : D ≤ B) (hCE : C ≤ E) (hFD : F ≤ D)
    (p : Realization m K E F) :
    intervalInclusion hAC hDB (intervalInclusion hCE hFD p)=
      intervalInclusion (hAC.trans hCE) (hFD.trans hDB) p := by
  apply Subtype.ext
  rw [intervalInclusion_val]
  simp only [intervalInclusion_val,Probability.push_comp]
  rfl

theorem intervalInclusion_self (p : Realization m K A B) : intervalInclusion le_rfl le_rfl p=p := by
  apply Subtype.ext
  apply Probability.push_eq_self
  intro v hv
  exact Subtype.ext rfl

end
end AbelianTargets.IntervalCarriers
