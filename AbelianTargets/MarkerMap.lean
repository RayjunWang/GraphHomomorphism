import AbelianTargets.MarkerWindows
import Mathlib.Topology.Clopen

/-!
# The continuous map into a finite marker graph

This file proves the positive window-map construction of Lemma 7.3 from
an actual clopen, separated, covering marker set. It does not assert
the existence of that marker set for an arbitrary free action.
-/

namespace AbelianTargets

noncomputable section

/-- The exact orbit marker data needed by the window-map construction. -/
structure ClopenMarkers (d L : ℕ) (X : Type*)
    [TopologicalSpace X] [AddAction (Lattice d) X] where
  carrier : Set X
  isClopen : IsClopen carrier
  separated : ∀ (x : X) (u v : Lattice d),
    u +ᵥ x ∈ carrier → v +ᵥ x ∈ carrier → u ≠ v →
      ∃ i, (L : ℤ) < |u i - v i|
  covering : ∀ (x : X) (u : Lattice d),
    ∃ a : Lattice d, a +ᵥ x ∈ carrier ∧ ∀ i, |u i - a i| ≤ (L : ℤ)

namespace ClopenMarkers

variable {d L : ℕ} {X : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]

/-- Record precisely the marker positions visible in the finite box. -/
def window (markers : ClopenMarkers d L X) (x : X) : MarkerPattern d L := by
  classical
  refine ⟨(markerBox d L).filter (fun u => u +ᵥ x ∈ markers.carrier),
    Finset.filter_subset _ _, ?_, ?_⟩
  · intro a ha b hb hne
    exact markers.separated x a b (Finset.mem_filter.mp ha).2
      (Finset.mem_filter.mp hb).2 hne
  · intro u hu
    obtain ⟨a, ha, hclose⟩ := markers.covering x u
    have habox : a ∈ markerBox d L := by
      apply (mem_markerBox _).2
      intro i
      have hui := abs_le.mp (hu i)
      have hai := abs_le.mp (hclose i)
      apply abs_le.mpr
      constructor <;> omega
    exact ⟨a, Finset.mem_filter.mpr ⟨habox, ha⟩, hclose⟩

theorem mem_window (markers : ClopenMarkers d L X) (x : X) (u : Lattice d) :
    u ∈ (markers.window x).val ↔
      u ∈ markerBox d L ∧ u +ᵥ x ∈ markers.carrier := by
  classical
  exact Finset.mem_filter

theorem window_overlap (markers : ClopenMarkers d L X)
    (x : X) (g : Lattice d) :
    WindowOverlap g (markers.window x) (markers.window (g +ᵥ x)) := by
  intro z hz hzg
  rw [markers.mem_window, markers.mem_window]
  have hact : (z - g) +ᵥ (g +ᵥ x) = z +ᵥ x := by
    rw [← add_vadd, sub_add_cancel]
  simp only [hz, hzg, true_and, hact]

theorem window_adjacent (markers : ClopenMarkers d L X) (hL : 4 ≤ L)
    (x : X) (i : Fin d) :
    (MarkerGraph d L hL).Adj (markers.window x)
      (markers.window (unitVector i +ᵥ x)) :=
  ⟨unitVector i, ⟨i, Or.inl rfl⟩, markers.window_overlap x (unitVector i)⟩

theorem window_eq_iff (markers : ClopenMarkers d L X)
    (x : X) (D : MarkerPattern d L) :
    markers.window x = D ↔
      ∀ u ∈ markerBox d L, (u +ᵥ x ∈ markers.carrier ↔ u ∈ D.val) := by
  constructor
  · intro heq u hu
    have hm : u ∈ (markers.window x).val ↔ u ∈ D.val := by rw [heq]
    simpa only [markers.mem_window, hu, true_and] using hm
  · intro h
    apply Subtype.ext
    apply Finset.ext
    intro u
    by_cases hu : u ∈ markerBox d L
    · simpa only [markers.mem_window, hu, true_and] using h u hu
    · have hnD : u ∉ D.val := fun hmem => hu (D.mem_box hmem)
      simp only [markers.mem_window, hu, false_and, hnD]

/-- Clopen marker membership in each of finitely many coordinates gives
continuous discrete-valued windows. -/
theorem continuous_window [ContinuousVAdd (Lattice d) X]
    (markers : ClopenMarkers d L X) : Continuous markers.window := by
  classical
  apply continuous_discrete_rng.mpr
  intro D
  have hfiber : markers.window ⁻¹' {D} =
      ⋂ u ∈ markerBox d L,
        {x : X | u +ᵥ x ∈ markers.carrier ↔ u ∈ D.val} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_iInter, Set.mem_setOf_eq]
    exact markers.window_eq_iff x D
  rw [hfiber]
  apply isOpen_biInter_finset
  intro u _hu
  have hc : IsClopen {x : X | u +ᵥ x ∈ markers.carrier} :=
    markers.isClopen.preimage (continuous_const_vadd u)
  by_cases hD : u ∈ D.val
  · simpa only [hD, iff_true] using hc.isOpen
  · simpa only [hD, iff_false, Set.compl_setOf] using hc.isClosed.isOpen_compl

/-- The positive part of Lemma 7.3, conditional only on an existing clopen
marker set with the stated orbit separation and coverage properties. -/
theorem hasContinuousHom [ContinuousVAdd (Lattice d) X]
    (markers : ClopenMarkers d L X) (hL : 4 ≤ L) :
    HasContinuousHom (d := d) (X := X) (MarkerGraph d L hL) :=
  hasContinuousHom_of_positive markers.window markers.continuous_window
    (markers.window_adjacent hL)

end ClopenMarkers

end

end AbelianTargets
