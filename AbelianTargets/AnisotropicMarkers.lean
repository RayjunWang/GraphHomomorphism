import AbelianTargets.MarkerExistence

/-!
# Clopen markers at independent coordinate scales

The initial marker construction in Lemma 3.2 is proved for an actual free
continuous action. Each coordinate has its own scale. This is the input
to the later packing, priority, cut, and rectangular subdivision steps.
-/

namespace AbelianTargets

noncomputable section

def anisotropicDisplacements {d : ℕ} (L : Fin d → ℕ) : Finset (Lattice d) :=
  (Fintype.piFinset (fun i => Finset.Icc (-(L i : ℤ)) (L i : ℤ))).filter (· ≠ 0)

theorem mem_anisotropicDisplacements {d : ℕ} (L : Fin d → ℕ) (g : Lattice d) :
    g ∈ anisotropicDisplacements L ↔ (∀ i, |g i| ≤ (L i : ℤ)) ∧ g ≠ 0 := by
  simp only [anisotropicDisplacements, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_Icc, abs_le]

theorem neg_mem_anisotropicDisplacements {d : ℕ} {L : Fin d → ℕ} {g : Lattice d}
    (hg : g ∈ anisotropicDisplacements L) : -g ∈ anisotropicDisplacements L := by
  obtain ⟨hbound,hne⟩ := (mem_anisotropicDisplacements L g).mp hg
  exact (mem_anisotropicDisplacements L (-g)).mpr
    ⟨by simpa only [Pi.neg_apply,abs_neg] using hbound,neg_ne_zero.mpr hne⟩

variable {d : ℕ} {X : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]

def anisotropicDisplacementGraph (L : Fin d → ℕ)
    (free : IsFree (G := Lattice d) (X := X)) : SimpleGraph X where
  Adj x y := ∃ g ∈ anisotropicDisplacements L, g +ᵥ x = y
  symm := by
    rintro x y ⟨g,hg,hxy⟩
    refine ⟨-g,neg_mem_anisotropicDisplacements hg,?_⟩
    rw [← hxy,← add_vadd,neg_add_cancel,zero_vadd]
  loopless := ⟨by
    rintro x ⟨g,hg,hfix⟩
    exact ((mem_anisotropicDisplacements L g).mp hg).2 (free g x hfix)⟩

variable [ContinuousVAdd (Lattice d) X]

theorem neighbor_clopen_anisotropicDisplacementGraph (L : Fin d → ℕ)
    (free : IsFree (G := Lattice d) (X := X)) (S : Set X) (hS : IsClopen S) :
    IsClopen (NeighborSet (anisotropicDisplacementGraph L free) S) := by
  have heq : NeighborSet (anisotropicDisplacementGraph L free) S =
      ⋃ g ∈ anisotropicDisplacements L, {y : X | (-g) +ᵥ y ∈ S} := by
    ext y
    constructor
    · rintro ⟨x,hx,g,hg,hxy⟩
      refine Set.mem_iUnion.mpr ⟨g,Set.mem_iUnion.mpr ⟨hg,?_⟩⟩
      change -g +ᵥ y ∈ S
      rw [← hxy,← add_vadd,neg_add_cancel,zero_vadd]
      exact hx
    · intro hy
      obtain ⟨g,hy⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hg,hy⟩ := Set.mem_iUnion.mp hy
      refine ⟨-g +ᵥ y,hy,g,hg,?_⟩
      rw [← add_vadd,add_neg_cancel,zero_vadd]
  rw [heq]
  apply isClopen_biUnion_finset
  intro g _
  exact hS.preimage (continuous_const_vadd (-g))

variable [T1Space X] [SecondCountableTopology X]

theorem exists_countable_anisotropic_independent_cover (L : Fin d → ℕ)
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X)) :
    ∃ C : ℕ → Set X, (∀ n,IsClopen (C n)) ∧
      (∀ n,GraphIndependent (anisotropicDisplacementGraph L free) (C n)) ∧
      ∀ x,∃ n,x ∈ C n := by
  classical
  have hlocal : ∀ x : X, ∃ U : Set X, IsClopen U ∧ x ∈ U ∧
      GraphIndependent (anisotropicDisplacementGraph L free) U := by
    intro x
    let I := {g : Lattice d // g ∈ anisotropicDisplacements L}
    have hs : ∀ g : I, ∃ U : Set X,IsClopen U ∧ x ∈ U ∧
        ∀ y ∈ U,g.val +ᵥ y ∉ U := by
      intro g
      exact exists_clopen_shift_independent zeroDim free x g.val
        ((mem_anisotropicDisplacements L g.val).mp g.property).2
    choose U hclopen hx hshift using hs
    refine ⟨⋂ g : I,U g,isClopen_iInter_of_finite hclopen,Set.mem_iInter.mpr hx,?_⟩
    intro y hy z hz hadj
    obtain ⟨g,hg,hgyz⟩ := hadj
    exact hshift ⟨g,hg⟩ y (Set.mem_iInter.mp hy ⟨g,hg⟩)
      (hgyz.symm ▸ Set.mem_iInter.mp hz ⟨g,hg⟩)
  by_cases hX : Nonempty X
  · letI : Nonempty X := hX
    choose U hclopen hx hindep using hlocal
    obtain ⟨f,hcov⟩ := isLindelof_univ.indexed_countable_subcover U
      (fun x => (hclopen x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x,hx x⟩)
    exact ⟨fun n => U (f n),fun n => hclopen (f n),fun n => hindep (f n),
      fun x => Set.mem_iUnion.mp (hcov (Set.mem_univ x))⟩
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    exact ⟨fun _ => ∅,fun _ => isClopen_empty,fun _ x => isEmptyElim x,fun x => isEmptyElim x⟩

structure AnisotropicClopenMarkers (d : ℕ) (L : Fin d → ℕ) (X : Type*)
    [TopologicalSpace X] [AddAction (Lattice d) X] where
  markers : Set X
  clopen : IsClopen markers
  separated : ∀ (x : X) (u v : Lattice d),u +ᵥ x ∈ markers → v +ᵥ x ∈ markers → u ≠ v →
    ∃ i,(L i : ℤ) < |u i-v i|
  covering : ∀ (x : X) (u : Lattice d),∃ v : Lattice d,v +ᵥ x ∈ markers ∧ ∀ i,|u i-v i| ≤ (L i : ℤ)

/-- Actual anisotropic separated covering clopen markers on every free
zero-dimensional second-countable T1 lattice action. -/
theorem exists_anisotropicClopenMarkers (L : Fin d → ℕ)
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X)) :
    Nonempty (AnisotropicClopenMarkers d L X) := by
  classical
  obtain ⟨C,hclopen,hindep,hcover⟩ := exists_countable_anisotropic_independent_cover L zeroDim free
  obtain ⟨A,hA,hAi,hmax⟩ := exists_clopen_maximal_independent
    (anisotropicDisplacementGraph L free) C hclopen hindep hcover
    (neighbor_clopen_anisotropicDisplacementGraph L free)
  refine ⟨⟨A,hA,?_,?_⟩⟩
  · intro x u v hu hv hne
    by_contra hnone
    have hg : v-u ∈ anisotropicDisplacements L := by
      apply (mem_anisotropicDisplacements L (v-u)).mpr
      refine ⟨?_,sub_ne_zero.mpr hne.symm⟩
      intro i
      have hi : |u i-v i| ≤ (L i : ℤ) := le_of_not_gt (fun hi => hnone ⟨i,hi⟩)
      simpa only [Pi.sub_apply,abs_sub_comm] using hi
    apply hAi (u +ᵥ x) hu (v +ᵥ x) hv
    refine ⟨v-u,hg,?_⟩
    rw [← add_vadd,sub_add_cancel]
  · intro x u
    by_cases hu : u +ᵥ x ∈ A
    · exact ⟨u,hu,by intro i; simp⟩
    · obtain ⟨b,hb,g,hg,hgb⟩ := hmax (u +ᵥ x) hu
      have hab : (u-g) +ᵥ x = b := by
        have hlat : u-g = -g+u := by rw [sub_eq_add_neg,add_comm]
        rw [hlat,add_vadd,← hgb,← add_vadd,neg_add_cancel,zero_vadd]
      refine ⟨u-g,hab.symm ▸ hb,?_⟩
      intro i
      simpa only [Pi.sub_apply,sub_sub_cancel] using
        ((mem_anisotropicDisplacements L g).mp hg).1 i

end

end AbelianTargets
