import AbelianTargets.BottomCoordinateInverse

/-! Literal height-zero carrier faces are single vertices or adjacent
horizontal unit edges. Hence every bottom realization point is exactly
recovered from its barycentric horizontal coordinate. -/

namespace AbelianTargets.IntervalCarriers
noncomputable section

theorem carrierFace_zero_classification {m R : ℕ} {s : Finset Vertex}
    (hs : CarrierFace m 0 0 R s) :
    (∃ n : ℕ,n ≤ R ∧ s ⊆ {((n : ℤ),0)}) ∨
      ∃ n : ℕ,n < R ∧ s ⊆ {((n : ℤ),0),(((n+1 : ℕ) : ℤ),0)} := by
  have hvertex : ∀ v ∈ carrierVertices 0 0 R,∃ n : ℕ,n ≤ R ∧ v=((n : ℤ),0) := by
    intro v hv
    obtain ⟨hv₀,hvR,hvh⟩ := mem_carrierVertices.mp hv
    refine ⟨v.1.toNat,?_,?_⟩
    · have he := Int.toNat_of_nonneg hv₀
      exact_mod_cast (he ▸ hvR)
    · apply Prod.ext
      · exact (Int.toNat_of_nonneg hv₀).symm
      · omega
  have hedge : ∀ u ∈ carrierVertices 0 0 R,∀ v ∈ carrierVertices 0 0 R,
      HorizontalStep m u v → ∃ n : ℕ,n < R ∧
        u=((n : ℤ),0) ∧ v=(((n+1 : ℕ) : ℤ),0) := by
    intro u hu v hv he
    obtain ⟨n,hn,rfl⟩ := hvertex u hu
    have hvR := (mem_carrierVertices.mp hv).2.1
    have he' : v=(((n+1 : ℕ) : ℤ),0) := by simpa [HorizontalStep] using he
    refine ⟨n,?_,rfl,he'⟩
    rw [he'] at hvR
    dsimp only at hvR
    have hnat : n+1 ≤ R := by exact_mod_cast hvR
    omega
  rcases hs with ⟨v,hv,hsv⟩ | ⟨u,hu,v,hv,he,hsv⟩ | ⟨t,ht,hst⟩
  · obtain ⟨n,hn,rfl⟩ := hvertex v hv
    exact Or.inl ⟨n,hn,hsv⟩
  · obtain ⟨hne,hrel | hrel⟩ := he
    · rcases hrel with hhor | hver
      · obtain ⟨n,hn,rfl,rfl⟩ := hedge u hu v hv hhor
        exact Or.inr ⟨n,hn,hsv⟩
      · have hvh := (mem_carrierVertices.mp hv).2.2
        have hh := congrArg Prod.snd hver
        dsimp [VerticalStep] at hh
        omega
    · rcases hrel with hhor | hver
      · obtain ⟨n,hn,rfl,rfl⟩ := hedge v hv u hu hhor
        exact Or.inr ⟨n,hn,by simpa only [Finset.pair_comm] using hsv⟩
      · have huh := (mem_carrierVertices.mp hu).2.2
        have hh := congrArg Prod.snd hver
        dsimp [VerticalStep] at hh
        omega
  · obtain ⟨c,hc,ht⟩ := Finset.mem_biUnion.mp ht
    have hh := (Finset.mem_filter.mp hc).2.1
    omega

theorem bottomSupported_of_face {m K R : ℕ}
    (p : Probability (CarrierVertex K 0 R)) (s : Finset (CarrierVertex K 0 R))
    (hs : CarrierFace m 0 0 R (s.image Subtype.val))
    (hp : p.SupportedOn (s : Set _)) : BottomSupported K R p := by
  rcases carrierFace_zero_classification hs with ⟨n,hn,hsub⟩ | ⟨n,hn,hsub⟩
  · left
    refine ⟨n,hn,?_⟩
    intro v hv
    have hr := hsub (Finset.mem_image.mpr ⟨v,hp v hv,rfl⟩)
    have he : v=bottomVertex K R n hn := Subtype.ext (Finset.mem_singleton.mp hr)
    simp [he]
  · right
    refine ⟨n,hn,?_⟩
    intro v hv
    have hr := hsub (Finset.mem_image.mpr ⟨v,hp v hv,rfl⟩)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with hr | hr
    · have he : v=bottomVertex K R n hn.le := Subtype.ext hr
      simp [he]
    · have he : v=bottomVertex K R (n+1) (by omega) := Subtype.ext hr
      simp [he]

theorem realization_zero_bottomSupported {m R : ℕ} (p : Realization m 0 0 R) :
    BottomSupported 0 R p.val := by
  obtain ⟨s,hs,hp⟩ := p.property
  exact bottomSupported_of_face p.val s ((mem_simplexFaces s).mp hs) hp

theorem bottomMap_inverse_realization_zero {m R : ℕ} (p : Realization m 0 0 R) :
    bottomMap 0 R (bottomCoordinate 0 R p.val)=p.val.mass :=
  bottomMap_inverse 0 R p.val (realization_zero_bottomSupported p)

end
end AbelianTargets.IntervalCarriers
