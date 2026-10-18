import AbelianTargets.AnisotropicMarkers
import AbelianTargets.AtlasPacking
import AbelianTargets.ClopenColoring

/-!
# Continuous marker priorities with a scale-independent color bound

The marker proximity graph is the actual induced finite-displacement
graph. Its finite neighbors are counted by the anisotropic packing bound.
The general continuous finite-coloring theorem supplies the priorities.
-/

namespace AbelianTargets

noncomputable section

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X]

def scaledMarkerNeighborhood (M : AnisotropicClopenMarkers d L X) (S : ℕ)
    (x : M.markers) : Finset (Lattice d) := by
  classical
  exact (Fintype.piFinset (fun i => Finset.Icc (-(S : ℤ)*(L i : ℤ)) ((S : ℤ)*(L i : ℤ)))).filter
    (fun g => g +ᵥ x.val ∈ M.markers)

@[simp] theorem mem_scaledMarkerNeighborhood (M : AnisotropicClopenMarkers d L X)
    (S : ℕ) (x : M.markers) (g : Lattice d) :
    g ∈ scaledMarkerNeighborhood M S x ↔
      (∀ i,-(S : ℤ)*(L i : ℤ) ≤ g i ∧ g i ≤ (S : ℤ)*(L i : ℤ)) ∧
        g +ᵥ x.val ∈ M.markers := by
  simp only [scaledMarkerNeighborhood,Finset.mem_filter,Fintype.mem_piFinset,Finset.mem_Icc]

theorem zero_mem_scaledMarkerNeighborhood (M : AnisotropicClopenMarkers d L X)
    (S : ℕ) (x : M.markers) : 0 ∈ scaledMarkerNeighborhood M S x := by
  apply (mem_scaledMarkerNeighborhood M S x 0).mpr
  refine ⟨?_,by simpa using x.property⟩
  intro i
  change -(S : ℤ)*(L i : ℤ) ≤ 0 ∧ 0 ≤ (S : ℤ)*(L i : ℤ)
  have hpos : 0 ≤ (S : ℤ)*(L i : ℤ) := by positivity
  exact ⟨by simpa only [neg_mul] using neg_nonpos.mpr hpos,hpos⟩

theorem scaledMarkerNeighborhood_card_le (M : AnisotropicClopenMarkers d L X)
    (hL : ∀ i,1 ≤ L i) (S : ℕ) (x : M.markers) :
    (scaledMarkerNeighborhood M S x).card ≤ (2*S+1)^d := by
  apply anisotropic_marker_packing S L hL
  · intro g hg
    exact ((mem_scaledMarkerNeighborhood M S x g).mp hg).1
  · intro g hg h hh hne
    exact M.separated x.val g h ((mem_scaledMarkerNeighborhood M S x g).mp hg).2
      ((mem_scaledMarkerNeighborhood M S x h).mp hh).2 hne

def markerNeighborList (M : AnisotropicClopenMarkers d L X) (S : ℕ)
    (x : M.markers) : Finset M.markers := by
  classical
  exact ((scaledMarkerNeighborhood M S x).erase 0).attach.image (fun g =>
    ⟨g.val +ᵥ x.val,((mem_scaledMarkerNeighborhood M S x g.val).mp
      (Finset.mem_of_mem_erase g.property)).2⟩)

theorem markerNeighborList_card_le (M : AnisotropicClopenMarkers d L X)
    (hL : ∀ i,1 ≤ L i) (S : ℕ) (x : M.markers) :
    (markerNeighborList M S x).card ≤ (2*S+1)^d-1 := by
  classical
  unfold markerNeighborList
  calc
    _ ≤ (((scaledMarkerNeighborhood M S x).erase 0).attach).card := Finset.card_image_le
    _ = (scaledMarkerNeighborhood M S x).card-1 := by
      rw [Finset.card_attach,Finset.card_erase_of_mem (zero_mem_scaledMarkerNeighborhood M S x)]
    _ ≤ (2*S+1)^d-1 := Nat.sub_le_sub_right (scaledMarkerNeighborhood_card_le M hL S x) 1

def markerProximityGraph (M : AnisotropicClopenMarkers d L X) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X)) : SimpleGraph M.markers :=
  (anisotropicDisplacementGraph (fun i => S*L i) free).induce M.markers

theorem markerProximity_adj_neighbor (M : AnisotropicClopenMarkers d L X) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X)) (x y : M.markers)
    (hxy : (markerProximityGraph M S free).Adj y x) : y ∈ markerNeighborList M S x := by
  classical
  obtain ⟨g,hg,hgy⟩ := (markerProximityGraph M S free).symm hxy
  obtain ⟨hbound,hne⟩ := (mem_anisotropicDisplacements (fun i => S*L i) g).mp hg
  have hgN : g ∈ (scaledMarkerNeighborhood M S x).erase 0 := by
    apply Finset.mem_erase.mpr
    refine ⟨hne,(mem_scaledMarkerNeighborhood M S x g).mpr ⟨?_,hgy ▸ y.property⟩⟩
    intro i
    have hi := hbound i
    rw [abs_le] at hi
    simpa only [Nat.cast_mul,neg_mul] using hi
  apply Finset.mem_image.mpr
  refine ⟨⟨g,hgN⟩,Finset.mem_attach _ _,?_⟩
  exact Subtype.ext hgy

variable [ContinuousVAdd (Lattice d) X] [T1Space X] [SecondCountableTopology X]

omit [T1Space X] [SecondCountableTopology X] in
theorem neighbor_clopen_markerProximityGraph (M : AnisotropicClopenMarkers d L X)
    (S : ℕ) (free : IsFree (G := Lattice d) (X := X))
    (U : Set M.markers) (hU : IsClopen U) :
    IsClopen (NeighborSet (markerProximityGraph M S free) U) := by
  have hImage : IsClopen (Subtype.val '' U : Set X) :=
    ⟨M.clopen.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _ hU.isClosed,
      M.clopen.isOpen.isOpenMap_subtype_val _ hU.isOpen⟩
  have heq : NeighborSet (markerProximityGraph M S free) U =
      Subtype.val ⁻¹' NeighborSet (anisotropicDisplacementGraph (fun i => S*L i) free)
        (Subtype.val '' U) := by
    ext y
    constructor
    · rintro ⟨x,hx,hxy⟩
      exact ⟨x.val,⟨x,hx,rfl⟩,hxy⟩
    · rintro ⟨x,⟨x',hx',rfl⟩,hxy⟩
      exact ⟨x',hx',hxy⟩
  rw [heq]
  exact (neighbor_clopen_anisotropicDisplacementGraph _ free _ hImage).preimage continuous_subtype_val

/-- Actual continuous priorities with a number of colors independent of
the scales. This proves the marker-coloring step in Lemma 3.2. -/
theorem exists_continuous_markerPriorities (M : AnisotropicClopenMarkers d L X)
    (hL : ∀ i,1 ≤ L i) (S : ℕ) (zeroDim : ZeroDimensional X)
    (free : IsFree (G := Lattice d) (X := X)) :
    ∃ c : M.markers → Fin ((2*S+1)^d),Continuous c ∧
      ∀ x y,(markerProximityGraph M S free).Adj x y → c x ≠ c y := by
  classical
  obtain ⟨C,hclopen,hindep,hcover⟩ := exists_countable_anisotropic_independent_cover
    (fun i => S*L i) zeroDim free
  let C' := fun n => (Subtype.val : M.markers → X) ⁻¹' C n
  have hC' : ∀ n,IsClopen (C' n) := fun n => (hclopen n).preimage continuous_subtype_val
  have hi' : ∀ n,GraphIndependent (markerProximityGraph M S free) (C' n) := by
    intro n x hx y hy hxy
    exact hindep n x.val hx y.val hy hxy
  have hc' : ∀ x : M.markers,∃ n,x ∈ C' n := fun x => hcover x.val
  have hP : 1 ≤ (2*S+1)^d := Nat.one_le_pow _ _ (by omega)
  obtain ⟨c,hc,hproper⟩ := exists_continuous_finite_coloring (markerProximityGraph M S free) C'
    hC' hi' hc' (neighbor_clopen_markerProximityGraph M S free)
    ((2*S+1)^d-1) (markerNeighborList M S)
    (markerNeighborList_card_le M hL S) (markerProximity_adj_neighbor M S free)
  have heq : (2*S+1)^d-1+1 = (2*S+1)^d := by omega
  exact ⟨fun x => Fin.cast heq (c x),
    (continuous_of_discreteTopology (f := fun j => Fin.cast heq j)).comp hc,
    fun x y hxy he => hproper x y hxy (Fin.cast_injective heq he)⟩

end

end AbelianTargets
