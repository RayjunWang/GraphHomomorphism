import AbelianTargets.MarkerPriorities
import AbelianTargets.PriorityCuts

/-!
# The actual marker neighborhood used by the priority-cut algorithm

The finite marker neighbor list is exactly the proximity graph's neighbor
set. A continuous proper marker coloring therefore supplies all fields of
the finite-priority neighborhood, with the scale-independent packing bound.
-/

namespace AbelianTargets

noncomputable section

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X]

theorem mem_markerNeighborList_iff (M : AnisotropicClopenMarkers d L X) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X)) (x y : M.markers) :
    y ∈ markerNeighborList M S x ↔ (markerProximityGraph M S free).Adj x y := by
  classical
  constructor
  · intro hy
    obtain ⟨g,hg,he⟩ := Finset.mem_image.mp hy
    have hg' : g.val ∈ (scaledMarkerNeighborhood M S x).erase 0 := g.property
    obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hg'
    obtain ⟨hbound,_⟩ := (mem_scaledMarkerNeighborhood M S x g.val).mp hmem
    refine ⟨g.val,(mem_anisotropicDisplacements (fun i => S*L i) g.val).mpr ⟨?_,hne⟩,?_⟩
    · intro i
      rw [abs_le]
      simpa only [Nat.cast_mul,neg_mul] using hbound i
    · exact congrArg Subtype.val he
  · intro hxy
    exact markerProximity_adj_neighbor M S free x y ((markerProximityGraph M S free).symm hxy)

/-- Continuous marker priorities supply the exact finite-neighborhood
input of the previously verified cut iteration. -/
theorem exists_markerPriorityNeighborhood
    [ContinuousVAdd (Lattice d) X] [T1Space X] [SecondCountableTopology X]
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (S : ℕ)
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X)) :
    ∃ N : PriorityNeighborhood M.markers ((2*S+1)^d),
      Continuous N.priority ∧
      ∀ x y,y ∈ N.nearby x ↔ x = y ∨ (markerProximityGraph M S free).Adj x y := by
  classical
  obtain ⟨c,hc,hproper⟩ := exists_continuous_markerPriorities M hL S zeroDim free
  let N : PriorityNeighborhood M.markers ((2*S+1)^d) := {
    nearby := fun x => insert x (markerNeighborList M S x)
    bound := by
      intro x
      have hP : 1 ≤ (2*S+1)^d := Nat.one_le_pow _ _ (by omega)
      exact (Finset.card_insert_le _ _).trans (by
        have h := markerNeighborList_card_le M hL S x
        omega)
    symmetric := by
      intro x y hy
      rcases Finset.mem_insert.mp hy with he | hn
      · subst y; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem ((mem_markerNeighborList_iff M S free y x).mpr
          ((markerProximityGraph M S free).symm ((mem_markerNeighborList_iff M S free x y).mp hn)))
    priority := c
    proper := by
      intro x y hy hne
      rcases Finset.mem_insert.mp hy with he | hn
      · exact (hne he.symm).elim
      · exact hproper x y ((mem_markerNeighborList_iff M S free x y).mp hn) }
  refine ⟨N,hc,?_⟩
  intro x y
  change y ∈ insert x (markerNeighborList M S x) ↔ _
  rw [Finset.mem_insert,mem_markerNeighborList_iff M S free]
  exact or_congr eq_comm Iff.rfl

end

end AbelianTargets
