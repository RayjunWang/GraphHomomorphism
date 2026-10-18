import AbelianTargets.ContinuousOrbitCuts

/-!
# Actual fixed-index continuous priority cuts

Inactive lattice indices are isolated; active indices use the literal
finite marker-proximity neighborhood. This packages the neighborhood
fields left explicit in `ContinuousOrbitCuts` and proves continuity of
the resulting cuts from actual continuous marker priorities.
-/

namespace AbelianTargets
noncomputable section

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]

theorem mem_orbitCandidateBox (S : ℕ) (L : Fin d → ℕ) (a b : Lattice d) :
    b ∈ orbitCandidateBox S L a ↔ ∀ i,|b i-a i| ≤ (S*L i : ℕ) := by
  classical
  constructor
  · rintro hb
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hb
    have h := Fintype.mem_piFinset.mp hg
    intro i
    have hi := Finset.mem_Icc.mp (h i)
    simpa only [Pi.add_apply,add_sub_cancel_right,Nat.cast_mul,abs_le,neg_mul] using hi
  · intro hb
    apply Finset.mem_image.mpr
    refine ⟨b-a,?_,sub_add_cancel _ _⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    simpa only [Pi.sub_apply,Nat.cast_mul,neg_mul] using abs_le.mp (hb i)

theorem mem_inactiveOrbitNeighbors_of_mem
    (M : AnisotropicClopenMarkers d L X) (S : ℕ) (x : X) (a b : Lattice d)
    (ha : a +ᵥ x ∈ M.markers) :
    b ∈ inactiveOrbitNeighbors M S x a ↔
      b +ᵥ x ∈ M.markers ∧ ∀ i,|b i-a i| ≤ (S*L i : ℕ) := by
  classical
  simp only [inactiveOrbitNeighbors,if_pos ha,Finset.mem_filter,mem_orbitCandidateBox]
  exact and_comm

theorem inactiveOrbitNeighbors_active_eq
    (M : AnisotropicClopenMarkers d L X) (S : ℕ) (x : X) (a : Lattice d)
    (ha : a +ᵥ x ∈ M.markers) :
    inactiveOrbitNeighbors M S x a =
      (scaledMarkerNeighborhood M S ⟨a +ᵥ x,ha⟩).image (fun g => g+a) := by
  classical
  ext b
  rw [mem_inactiveOrbitNeighbors_of_mem M S x a b ha,Finset.mem_image]
  constructor
  · rintro ⟨hb,hclose⟩
    refine ⟨b-a,(mem_scaledMarkerNeighborhood M S _ _).mpr ⟨?_,?_⟩,sub_add_cancel _ _⟩
    · intro i
      simpa only [Pi.sub_apply,Nat.cast_mul,neg_mul] using abs_le.mp (hclose i)
    · simpa only [← add_vadd,sub_add_cancel] using hb
  · rintro ⟨g,hg,rfl⟩
    obtain ⟨hbound,hmarker⟩ := (mem_scaledMarkerNeighborhood M S _ _).mp hg
    refine ⟨by simpa only [add_vadd] using hmarker,?_⟩
    intro i
    simpa only [Pi.add_apply,add_sub_cancel_right,Nat.cast_mul,abs_le,neg_mul] using hbound i

theorem inactiveOrbitNeighbors_card_le
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (S : ℕ)
    (x : X) (a : Lattice d) :
    (inactiveOrbitNeighbors M S x a).card ≤ (2*S+1)^d := by
  classical
  by_cases ha : a +ᵥ x ∈ M.markers
  · rw [inactiveOrbitNeighbors_active_eq M S x a ha]
    exact Finset.card_image_le.trans (scaledMarkerNeighborhood_card_le M hL S _)
  · simp only [inactiveOrbitNeighbors,if_neg ha,Finset.card_singleton]
    exact Nat.one_le_pow _ _ (by omega)

def fixedOrbitPriorityNeighborhood
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X))
    (c : M.markers → Fin ((2*S+1)^d))
    (hproper : ∀ u v,(markerProximityGraph M S free).Adj u v → c u ≠ c v)
    (x : X) : PriorityNeighborhood (Lattice d) ((2*S+1)^d) where
  nearby := inactiveOrbitNeighbors M S x
  bound := inactiveOrbitNeighbors_card_le M hL S x
  symmetric a b hab := by
    classical
    by_cases ha : a +ᵥ x ∈ M.markers
    · obtain ⟨hb,hclose⟩ := (mem_inactiveOrbitNeighbors_of_mem M S x a b ha).mp hab
      apply (mem_inactiveOrbitNeighbors_of_mem M S x b a hb).mpr
      exact ⟨ha,by intro i; simpa only [abs_sub_comm] using hclose i⟩
    · have he : b = a := by simpa only [inactiveOrbitNeighbors,if_neg ha,Finset.mem_singleton] using hab
      subst b
      simpa only [inactiveOrbitNeighbors,if_neg ha,Finset.mem_singleton]
  priority a := markerPriorityExtension M.markers c ⟨0,Nat.one_le_pow _ _ (by omega)⟩ (a +ᵥ x)
  proper a b hab hne := by
    classical
    by_cases ha : a +ᵥ x ∈ M.markers
    · obtain ⟨hb,hclose⟩ := (mem_inactiveOrbitNeighbors_of_mem M S x a b ha).mp hab
      simp only [markerPriorityExtension,dif_pos ha,dif_pos hb]
      apply hproper
      refine ⟨b-a,(mem_anisotropicDisplacements (fun i => S*L i) _).mpr ⟨?_,?_⟩,?_⟩
      · intro i
        simpa only [Pi.sub_apply] using hclose i
      · exact sub_ne_zero.mpr hne.symm
      · change (b-a) +ᵥ (a +ᵥ x) = b +ᵥ x
        rw [← add_vadd,sub_add_cancel]
    · have he : b = a := by simpa only [inactiveOrbitNeighbors,if_neg ha,Finset.mem_singleton] using hab
      exact (hne he.symm).elim

theorem continuous_fixedOrbitCuts
    [TopologicalSpace (Finset (Lattice d))] [DiscreteTopology (Finset (Lattice d))]
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X))
    (c : M.markers → Fin ((2*S+1)^d)) (hc : Continuous c)
    (hproper : ∀ u v,(markerProximityGraph M S free).Adj u v → c u ≠ c v)
    (hscale : ∀ i,32*((2*S+1)^d) ≤ L i) (i : Fin d) (n : ℕ) (a : Lattice d) :
    Continuous (fun x => priorityCutIteration (fixedOrbitPriorityNeighborhood M hL S free c hproper x)
      (Nat.one_le_pow _ _ (by omega)) (hscale i) (fun g => g i) n a) := by
  exact continuous_actualOrbitCuts M S c hc _
    (fixedOrbitPriorityNeighborhood M hL S free c hproper) (fun _ _ => rfl) (fun _ _ => rfl)
    (Nat.one_le_pow _ _ (by omega)) hscale i n a

end
end AbelianTargets
