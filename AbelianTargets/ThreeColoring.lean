import AbelianTargets.MarkerExistence

/-!
# Three colors for a nonzero displacement

This proves the degree-two case of Lemma 3.1 used to build the compact
universal action in Lemma 7.5. A maximal independent clopen set receives
color zero; its complement is colored according to its forward neighbor.
-/

namespace AbelianTargets

noncomputable section

variable {d : ℕ} {X : Type*} [TopologicalSpace X]
  [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]

def displacementLineGraph (free : IsFree (G := Lattice d) (X := X))
    (g : Lattice d) (hg : g ≠ 0) : SimpleGraph X where
  Adj x y := g +ᵥ x = y ∨ g +ᵥ y = x
  symm := fun _ _ h => h.symm
  loopless := by
    constructor
    intro x h
    rcases h with h | h <;> exact hg (free g x h)

omit [TopologicalSpace X] [ContinuousVAdd (Lattice d) X] in
theorem neighborSet_displacementLineGraph
    (free : IsFree (G := Lattice d) (X := X))
    (g : Lattice d) (hg : g ≠ 0) (A : Set X) :
    NeighborSet (displacementLineGraph free g hg) A =
      (fun x : X => g +ᵥ x) ⁻¹' A ∪ (fun x : X => (-g) +ᵥ x) ⁻¹' A := by
  ext y
  constructor
  · rintro ⟨x, hx, h | h⟩
    · right
      change (-g) +ᵥ y ∈ A
      rw [← h, ← add_vadd, neg_add_cancel, zero_vadd]
      exact hx
    · left
      change g +ᵥ y ∈ A
      simpa only [h] using hx
  · rintro (h | h)
    · exact ⟨g +ᵥ y, h, Or.inr rfl⟩
    · refine ⟨(-g) +ᵥ y, h, Or.inl ?_⟩
      rw [← add_vadd, add_neg_cancel, zero_vadd]

theorem neighbor_clopen_displacementLineGraph
    (free : IsFree (G := Lattice d) (X := X))
    (g : Lattice d) (hg : g ≠ 0) (A : Set X) (hA : IsClopen A) :
    IsClopen (NeighborSet (displacementLineGraph free g hg) A) := by
  rw [neighborSet_displacementLineGraph]
  exact (hA.preimage (continuous_const_vadd g)).union
    (hA.preimage (continuous_const_vadd (-g)))

variable [T1Space X] [SecondCountableTopology X]

theorem exists_countable_clopen_line_independent_cover
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X))
    (g : Lattice d) (hg : g ≠ 0) :
    ∃ C : ℕ → Set X, (∀ n, IsClopen (C n)) ∧
      (∀ n, GraphIndependent (displacementLineGraph free g hg) (C n)) ∧
      ∀ x, ∃ n, x ∈ C n := by
  classical
  by_cases hX : Nonempty X
  · letI := hX
    choose U hU hx hshift using
      (fun x : X => exists_clopen_shift_independent zeroDim free x g hg)
    obtain ⟨f, hcov⟩ := isLindelof_univ.indexed_countable_subcover
      U (fun x => (hU x).isOpen) (by
        intro x _
        exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
    refine ⟨fun n => U (f n), fun n => hU (f n), ?_, ?_⟩
    · intro n x hx y hy hadj
      rcases hadj with hadj | hadj
      · exact hshift (f n) x hx (hadj.symm ▸ hy)
      · exact hshift (f n) y hy (hadj.symm ▸ hx)
    · intro x
      exact Set.mem_iUnion.mp (hcov (Set.mem_univ x))
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    refine ⟨fun _ => ∅, fun _ => isClopen_empty, ?_, ?_⟩
    · intro n x
      exact isEmptyElim x
    · intro x
      exact isEmptyElim x

def lineThreeColor (A : Set X) (g : Lattice d) (x : X) : Fin 3 :=
  by
    classical
    exact if x ∈ A then 0 else if g +ᵥ x ∈ A then 1 else 2

omit [T1Space X] [SecondCountableTopology X] in
theorem continuous_lineThreeColor (A : Set X) (g : Lattice d)
    (hA : IsClopen A) : Continuous (lineThreeColor A g) := by
  classical
  let q : Bool × Bool → Fin 3 := fun z => if z.1 then 0 else if z.2 then 1 else 2
  have hb : Continuous A.boolIndicator :=
    (continuous_boolIndicator_iff_isClopen A).mpr hA
  have hc : Continuous (fun x : X => (A.boolIndicator x, A.boolIndicator (g +ᵥ x))) :=
    hb.prodMk (hb.comp (continuous_const_vadd g))
  have hq : Continuous q := continuous_of_discreteTopology
  convert hq.comp hc using 1
  funext x
  simp [q, lineThreeColor, Set.boolIndicator]

omit [TopologicalSpace X] [ContinuousVAdd (Lattice d) X]
  [T1Space X] [SecondCountableTopology X] in
theorem lineThreeColor_shift_ne
    (free : IsFree (G := Lattice d) (X := X))
    (g : Lattice d) (hg : g ≠ 0) (A : Set X)
    (hind : GraphIndependent (displacementLineGraph free g hg) A)
    (hmax : ∀ x, x ∉ A → ∃ y ∈ A, (displacementLineGraph free g hg).Adj y x) :
    ∀ x, lineThreeColor A g (g +ᵥ x) ≠ lineThreeColor A g x := by
  classical
  intro x
  by_cases hx : x ∈ A
  · have hy : g +ᵥ x ∉ A := fun h => hind x hx (g +ᵥ x) h (Or.inl rfl)
    simp [lineThreeColor, hx, hy]
    split <;> decide
  · by_cases hy : g +ᵥ x ∈ A
    · simp [lineThreeColor, hx, hy]
    · have hyy : g +ᵥ (g +ᵥ x) ∈ A := by
        obtain ⟨z, hz, h | h⟩ := hmax (g +ᵥ x) hy
        · have hzx : z = x := by
            have hh := congrArg (fun y : X => (-g) +ᵥ y) h
            simpa only [← add_vadd, neg_add_cancel, zero_vadd] using hh
          exact False.elim (hx (hzx ▸ hz))
        · exact h.symm ▸ hz
      simp [lineThreeColor, hx, hy, hyy]

/-- The actual continuous proper three-coloring for any nonzero lattice
displacement, with no reference assumptions. -/
theorem exists_continuous_displacement_three_coloring
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X))
    (g : Lattice d) (hg : g ≠ 0) :
    ∃ c : X → Fin 3, Continuous c ∧ ∀ x, c (g +ᵥ x) ≠ c x := by
  obtain ⟨C, hC, hind, hcov⟩ :=
    exists_countable_clopen_line_independent_cover zeroDim free g hg
  obtain ⟨A, hA, hAi, hmax⟩ := exists_clopen_maximal_independent
    (displacementLineGraph free g hg) C hC hind hcov
    (neighbor_clopen_displacementLineGraph free g hg)
  exact ⟨lineThreeColor A g, continuous_lineThreeColor A g hA,
    lineThreeColor_shift_ne free g hg A hAi hmax⟩

end

end AbelianTargets
