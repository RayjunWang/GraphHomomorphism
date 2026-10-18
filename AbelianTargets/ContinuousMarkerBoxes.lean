import AbelianTargets.CovariantOrbitCuts

/-!
# Actual continuous covariant marker boxes

This record contains cut data, rather than a tiling or an assumed atlas.
Its existence follows from the checked finite-priority construction on
the actual marker graph. It supplies all inputs to retained subdivisions.
-/

namespace AbelianTargets
noncomputable section

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]

structure ContinuousMarkerBoxes (M : AnisotropicClopenMarkers d L X) (S : ℕ) where
  priority : X → Lattice d → Fin ((2*S+1)^d)
  priority_continuous : ∀ a,Continuous (fun x => priority x a)
  priority_repoint : ∀ x t a,priority (t +ᵥ x) a = priority x (a+t)
  priority_proper : ∀ (x : X) (a b : Lattice d),a +ᵥ x ∈ M.markers → b +ᵥ x ∈ M.markers → a ≠ b →
    (∀ i,|b i-a i| ≤ (S*L i : ℕ)) → priority x a ≠ priority x b
  cuts : X → Lattice d → Fin d → ℤ × ℤ
  cuts_continuous : ∀ a i,Continuous (fun x => cuts x a i)
  cuts_bounds : ∀ x a i,a i-3*(L i : ℤ) ≤ (cuts x a i).1 ∧
    (cuts x a i).1 ≤ a i-2*(L i : ℤ) ∧
    a i+2*(L i : ℤ) ≤ (cuts x a i).2 ∧ (cuts x a i).2 ≤ a i+3*(L i : ℤ)
  cuts_repoint : ∀ x t a i,cuts (t +ᵥ x) a i =
    ((cuts x (a+t) i).1-t i,(cuts x (a+t) i).2-t i)
  cuts_separated : ∀ (x : X) (a b : Lattice d),a +ᵥ x ∈ M.markers → b +ᵥ x ∈ M.markers → a ≠ b →
    (∀ j,|b j-a j| ≤ (S*L j : ℕ)) → ∀ i s t,
      ((L i/(16*((2*S+1)^d)) : ℕ) : ℤ) <
        |cutSide (cuts x a i) s-cutSide (cuts x b i) t|

def ContinuousMarkerBoxes.rectangularCuts
    {M : AnisotropicClopenMarkers d L X} {S : ℕ}
    (B : ContinuousMarkerBoxes M S) (x : X) :
    RectangularCuts L {a : Lattice d | a +ᵥ x ∈ M.markers} where
  lower a i := (B.cuts x a.val i).1
  upper a i := (B.cuts x a.val i).2
  lower_bound a i := ⟨(B.cuts_bounds x a.val i).1,(B.cuts_bounds x a.val i).2.1⟩
  upper_bound a i := ⟨(B.cuts_bounds x a.val i).2.2.1,(B.cuts_bounds x a.val i).2.2.2⟩

theorem ContinuousMarkerBoxes.boxes_cover
    {M : AnisotropicClopenMarkers d L X} {S : ℕ}
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (x : X) :
    ∀ z : RealCoordinates d,∃ a,z ∈ (B.rectangularCuts x).box a :=
  anisotropic_marker_boxes_cover M hL x (B.rectangularCuts x)

def markerBoxesFromPriorities
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X))
    (c : M.markers → Fin ((2*S+1)^d)) (hc : Continuous c)
    (hproper : ∀ u v,(markerProximityGraph M S free).Adj u v → c u ≠ c v)
    (hscale : ∀ i,32*((2*S+1)^d) ≤ L i) : ContinuousMarkerBoxes M S where
  priority x a := (fixedOrbitPriorityNeighborhood M hL S free c hproper x).priority a
  priority_continuous a := continuous_orbitPriorityExtension M c hc _ a
  priority_repoint := fixedOrbitPriority_repoint M hL S free c hproper
  priority_proper x a b ha hb hne hclose := by
    apply (fixedOrbitPriorityNeighborhood M hL S free c hproper x).proper a b _ hne
    exact (mem_inactiveOrbitNeighbors_of_mem M S x a b ha).mpr ⟨hb,hclose⟩
  cuts x a i := priorityCutIteration (fixedOrbitPriorityNeighborhood M hL S free c hproper x)
    (Nat.one_le_pow _ _ (by omega)) (hscale i) (fun g => g i) ((2*S+1)^d) a
  cuts_continuous a i := by
    letI : TopologicalSpace (Finset (Lattice d)) := ⊥
    letI : DiscreteTopology (Finset (Lattice d)) := ⟨rfl⟩
    exact continuous_fixedOrbitCuts M hL S free c hc hproper hscale i ((2*S+1)^d) a
  cuts_bounds x a i := priorityCutIteration_bounds _ _ _ _ _ _
  cuts_repoint x t a i := fixedOrbitCutIteration_repoint M hL S free c hproper hscale x t i _ a
  cuts_separated x a b ha hb hne hclose i s t := by
    apply priorityCuts_separated _ _ _ _ _ hne s t
    exact (mem_inactiveOrbitNeighbors_of_mem M S x a b ha).mpr ⟨hb,hclose⟩

/-- All continuous covariant cut data exist on an actual free action.
No geometric atlas or continuity conclusion is supplied as an input. -/
theorem exists_continuousMarkerBoxes
    [T1Space X] [SecondCountableTopology X]
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X)) (zeroDim : ZeroDimensional X)
    (hscale : ∀ i,32*((2*S+1)^d) ≤ L i) : Nonempty (ContinuousMarkerBoxes M S) := by
  obtain ⟨c,hc,hproper⟩ := exists_continuous_markerPriorities M hL S zeroDim free
  exact ⟨markerBoxesFromPriorities M hL S free c hc hproper hscale⟩

end
end AbelianTargets
