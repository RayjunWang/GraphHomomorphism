import AbelianTargets.EvenFiniteSources
import AbelianTargets.ShiftTransitivity

/-!
# The actual product of two-dimensional free shifts

The `2k`-dimensional action translates just the specified coordinate
block. Restricting a nonzero product translation to its active factors
gives exactly the transitive cyclic action proved in `ShiftTransitivity`.
-/

namespace AbelianTargets

def ProductShift (k : ℕ) := Fin k → FreeShift 2

instance productShiftTopology (k : ℕ) : TopologicalSpace (ProductShift k) :=
  inferInstanceAs (TopologicalSpace (Fin k → FreeShift 2))

instance productShiftAction (k : ℕ) : AddAction (Lattice (2 * k)) (ProductShift k) where
  vadd g x := fun i => blockVector g i +ᵥ x i
  zero_vadd x := by funext i; change blockVector 0 i +ᵥ x i = x i; simp
  add_vadd g h x := by
    funext i
    change blockVector (g + h) i +ᵥ x i = blockVector g i +ᵥ (blockVector h i +ᵥ x i)
    rw [blockVector_add, add_vadd]

instance productShiftContinuousVAdd (k : ℕ) :
    ContinuousVAdd (Lattice (2 * k)) (ProductShift k) where
  continuous_vadd := continuous_prod_of_discrete_left.mpr (by
    intro g
    exact continuous_pi (fun i =>
      (continuous_const_vadd (blockVector g i)).comp (continuous_apply i)))

theorem exists_active_block {k : ℕ} (t : Lattice (2 * k)) (ht : t ≠ 0) :
    ∃ i, blockVector t i ≠ 0 := by
  by_contra h
  push Not at h
  apply ht
  funext a
  obtain ⟨⟨i,j⟩, rfl⟩ := (blockIndex k).surjective a
  exact congrFun (h i) j

noncomputable section

def activeProductEmbedding {k : ℕ} (t : Lattice (2 * k))
    (base : ProductShift k)
    (y : CyclicProductShift 2 (fun i : {i : Fin k // blockVector t i ≠ 0} => blockVector t i)) :
    ProductShift k :=
  fun i => if h : blockVector t i ≠ 0 then y ⟨i,h⟩ else base i

theorem continuous_activeProductEmbedding {k : ℕ} (t : Lattice (2 * k))
    (base : ProductShift k) : Continuous (activeProductEmbedding t base) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : blockVector t i ≠ 0
  · simpa only [activeProductEmbedding, dif_pos hi] using continuous_apply (⟨i,hi⟩ : {i // blockVector t i ≠ 0})
  · simpa only [activeProductEmbedding, dif_neg hi] using
      (continuous_const : Continuous (fun _ => base i))

theorem activeProductEmbedding_one_step {k : ℕ} (t : Lattice (2 * k))
    (base : ProductShift k)
    (y : CyclicProductShift 2 (fun i : {i : Fin k // blockVector t i ≠ 0} => blockVector t i)) :
    activeProductEmbedding t base ((1 : ℤ) +ᵥ y) = t +ᵥ activeProductEmbedding t base y := by
  classical
  funext i
  change _ = blockVector t i +ᵥ activeProductEmbedding t base y i
  by_cases hi : blockVector t i ≠ 0
  · simp only [activeProductEmbedding, dif_pos hi]
    change (1 : ℤ) • blockVector t i +ᵥ y ⟨i,hi⟩ = blockVector t i +ᵥ y ⟨i,hi⟩
    rw [one_zsmul]
  · have hz : blockVector t i = 0 := not_ne_iff.mp hi
    simp [activeProductEmbedding, hz]

/-- A proper continuous coloring of all standard product edges cannot
be invariant under any nonzero product translation. Inactive factors are
fixed; the active factors carry the actual transitive cyclic action. -/
theorem productShift_no_nonzero_invariant_proper_coloring
    {k : ℕ} {V : Type*} [TopologicalSpace V] [DiscreteTopology V]
    (H : SimpleGraph V) (t : Lattice (2 * k)) (ht : t ≠ 0)
    (c : ProductShift k → V) (hc : Continuous c)
    (hinv : ∀ x, c (t +ᵥ x) = c x)
    (hproper : ∀ (a : Fin (2 * k)) x, H.Adj (c x) (c (unitVector a +ᵥ x))) : False := by
  classical
  obtain ⟨i, hi⟩ := exists_active_block t ht
  let I := {i : Fin k // blockVector t i ≠ 0}
  let t' : I → Lattice 2 := fun i => blockVector t i
  let Y := CyclicProductShift 2 t'
  let base : ProductShift k := fun _ => originFreeConfiguration 2
  let E : Y → ProductShift k := activeProductEmbedding t base
  letI : AddAction.IsTopologicallyTransitive ℤ Y :=
    cyclicProductShift_transitive (by decide) t' (fun i => i.property)
  have hc' : Continuous (fun y : Y => c (E y)) := hc.comp (continuous_activeProductEmbedding t base)
  have hstep : ∀ y : Y, c (E ((1 : ℤ) +ᵥ y)) = c (E y) := by
    intro y
    exact (congrArg c (activeProductEmbedding_one_step t base y)).trans (hinv (E y))
  have hconstant := cyclic_invariant_discrete_coloring_constant (fun y : Y => c (E y)) hc' hstep
  let y₀ : Y := fun _ => originFreeConfiguration 2
  let y₁ : Y := fun a => if a.val = i then unitVector (0 : Fin 2) +ᵥ y₀ a else y₀ a
  have hembed : E y₁ = unitVector (blockIndex k (i, (0 : Fin 2))) +ᵥ E y₀ := by
    funext a
    change activeProductEmbedding t base y₁ a =
      blockVector (unitVector (blockIndex k (i, (0 : Fin 2)))) a +ᵥ activeProductEmbedding t base y₀ a
    rw [blockVector_unit]
    by_cases hai : a = i
    · subst a
      simp [activeProductEmbedding, hi, y₁]
    · by_cases ha : blockVector t a ≠ 0
      · simp only [activeProductEmbedding, dif_pos ha, y₁, if_neg hai, zero_vadd]
      · simp only [activeProductEmbedding, dif_neg ha, if_neg hai, zero_vadd]
  have hp := hproper (blockIndex k (i, (0 : Fin 2))) (E y₀)
  rw [← hembed] at hp
  exact hp.ne (hconstant y₀ y₁)

end
end AbelianTargets
