import AbelianTargets.CompactFreeModel
import AbelianTargets.CompactFactorization
import AbelianTargets.FiniteSourceReferences
import AbelianTargets.References
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite twelve-tile sources in even dimension

This proves the even-dimensional part of Lemma 7.5. Its only reference
assumptions are Bernshteyn's continuous universality theorem and GJKS's
two-dimensional eventual finite-source theorem. The compact product,
its finite factor partitions, and the finite graph product map are proved.
-/

namespace AbelianTargets

open scoped BigOperators

/-- Identify the coordinate blocks with the standard `2k` coordinates. -/
def blockIndex (k : ℕ) : Fin k × Fin 2 ≃ Fin (2 * k) :=
  finProdFinEquiv.trans (Equiv.cast (congrArg Fin (Nat.mul_comm k 2)))

def blockVector {k : ℕ} (g : Lattice (2 * k)) (i : Fin k) : Lattice 2 :=
  fun j => g (blockIndex k (i, j))

@[simp] theorem blockVector_zero {k : ℕ} (i : Fin k) :
    blockVector (0 : Lattice (2 * k)) i = 0 := rfl

@[simp] theorem blockVector_add {k : ℕ} (g h : Lattice (2 * k)) (i : Fin k) :
    blockVector (g + h) i = blockVector g i + blockVector h i := rfl

theorem blockVector_unit {k : ℕ} (i a : Fin k) (j : Fin 2) :
    blockVector (unitVector (blockIndex k (i, j))) a =
      if a = i then unitVector j else 0 := by
  classical
  funext b
  by_cases hai : a = i
  · subst a
    simp [blockVector, unitVector, (blockIndex k).injective.eq_iff]
  · simp [blockVector, unitVector, (blockIndex k).injective.eq_iff, hai]

/-- The compact model for a product of `k` two-dimensional actions. -/
abbrev ProductCompactModel (k : ℕ) := Fin k → CompactFreeModel 2

instance productCompactModelAction (k : ℕ) :
    AddAction (Lattice (2 * k)) (ProductCompactModel k) where
  vadd g x i := blockVector g i +ᵥ x i
  zero_vadd x := by
    funext i
    change blockVector 0 i +ᵥ x i = x i
    rw [blockVector_zero, zero_vadd]
  add_vadd g h x := by
    funext i
    change blockVector (g + h) i +ᵥ x i = blockVector g i +ᵥ (blockVector h i +ᵥ x i)
    rw [blockVector_add, add_vadd]

instance productCompactModelContinuousVAdd (k : ℕ) :
    ContinuousVAdd (Lattice (2 * k)) (ProductCompactModel k) where
  continuous_vadd := continuous_prod_of_discrete_left.mpr (by
    intro g
    exact continuous_pi (fun i =>
      (continuous_const_vadd (blockVector g i)).comp (continuous_apply i)))

theorem productCompactModel_isFree (k : ℕ) :
    IsFree (G := Lattice (2 * k)) (X := ProductCompactModel k) := by
  intro g x hfix
  have hblock : ∀ i, blockVector g i = 0 := by
    intro i
    exact compactFreeModel_isFree 2 (blockVector g i) (x i) (congrFun hfix i)
  funext j
  obtain ⟨⟨i, l⟩, hj⟩ := (blockIndex k).surjective j
  simpa only [blockVector, hj] using congrFun (hblock i) l

theorem productCompactModel_zeroDimensional (k : ℕ) :
    ZeroDimensional (ProductCompactModel k) := isTopologicalBasis_isClopen

/-- The standard graph of a free lattice action. -/
def SchreierGraph {d : ℕ} {X : Type*} [AddAction (Lattice d) X]
    (free : IsFree (G := Lattice d) (X := X)) : SimpleGraph X where
  Adj := StandardEdge (d := d)
  symm x y := by
    rintro ⟨i, h | h⟩
    · exact ⟨i, Or.inr h⟩
    · exact ⟨i, Or.inl h⟩
  loopless := ⟨by
    rintro x ⟨i, h | h⟩ <;>
      have hz := free (unitVector i) x h <;>
      have hi := congrFun hz i <;>
      simp [unitVector] at hi⟩

/-- Equivariant maps preserve the standard Schreier edges. -/
theorem standardEdge_map {d : ℕ} {X Y : Type*}
    [AddAction (Lattice d) X] [AddAction (Lattice d) Y]
    (f : X → Y) (hequiv : ∀ (g : Lattice d) (x : X), f (g +ᵥ x) = g +ᵥ f x)
    {x y : X} (hxy : StandardEdge (d := d) x y) :
    StandardEdge (d := d) (f x) (f y) := by
  obtain ⟨i, h | h⟩ := hxy
  · refine ⟨i, Or.inl ?_⟩
    rw [← hequiv, h]
  · refine ⟨i, Or.inr ?_⟩
    rw [← hequiv, h]

/-- One coordinate edge is a standard edge of the product lattice action. -/
theorem product_standardEdge_of_coordinate {k : ℕ}
    {x y : ProductCompactModel k} (i : Fin k)
    (hxy : StandardEdge (d := 2) (x i) (y i))
    (hrest : ∀ a, a ≠ i → x a = y a) :
    StandardEdge (d := 2 * k) x y := by
  classical
  obtain ⟨j, h | h⟩ := hxy
  · refine ⟨blockIndex k (i, j), Or.inl ?_⟩
    funext a
    change blockVector (unitVector (blockIndex k (i, j))) a +ᵥ x a = y a
    rw [blockVector_unit]
    by_cases hai : a = i
    · subst a
      simpa using h
    · simpa [hai] using hrest a hai
  · refine ⟨blockIndex k (i, j), Or.inr ?_⟩
    funext a
    change blockVector (unitVector (blockIndex k (i, j))) a +ᵥ y a = x a
    rw [blockVector_unit]
    by_cases hai : a = i
    · subst a
      simpa using h
    · simpa [hai] using (hrest a hai).symm

/-- The compact factor atom graph belongs to `𝓗₂` because the actual free
shift maps continuously and equivariantly into the compact model. -/
theorem compact_factor_atom_inClass
    {B : Type*} [TopologicalSpace B] (α : CompactFreeModel 2 → B)
    (hα : Continuous α)
    (hproper : ∀ x y, (SchreierGraph (compactFreeModel_isFree 2)).Adj x y → α x ≠ α y) :
    InClass 2 (AtomGraph (SchreierGraph (compactFreeModel_isFree 2)) α hproper) := by
  obtain ⟨f, hf, hequiv⟩ := exists_continuous_equivariant_compactFreeModel
    (freeShift_zeroDimensional 2) (freeShift_isFree 2)
  refine ⟨fun x => codeAtom α (f x), (continuous_codeAtom α hα).comp hf, ?_⟩
  intro x y hxy
  exact ⟨f x, f y, standardEdge_map f hequiv hxy, rfl, rfl⟩

/-- A continuous `2k`-dimensional target receives all sufficiently large
products of admissible width-one twelve-tile sources. In particular the
parameters may subsequently be chosen as distinct large odd primes. -/
theorem even_dimension_eventual_finite_sources
    {V : Type*} [TopologicalSpace V] [Fintype V] [DiscreteTopology V]
    (H : SimpleGraph V) (k : ℕ) (hk : 1 ≤ k) (hH : InClass (2 * k) H) :
    ∃ N : ℕ, ∀ (p q : Fin k → ℕ) (hp : ∀ i, 5 ≤ p i) (hq : ∀ i, 5 ≤ q i),
      (∀ i, N ≤ p i) → (∀ i, N ≤ q i) → (∀ i, (p i).Coprime (q i)) →
      Nonempty (CartesianGraph (fun i => TwelveTiles.graph (p i) (q i) (hp i) (hq i)) →g H) := by
  classical
  have huni := References.bernshteyn_theorem_1_12 H (2 * k) (by omega) hH
  obtain ⟨c, hc, hcolor⟩ := huni (ProductCompactModel k)
    (productCompactModel_zeroDimensional k) (productCompactModel_isFree k)
  let G : Fin k → SimpleGraph (CompactFreeModel 2) :=
    fun _ => SchreierGraph (compactFreeModel_isFree 2)
  let cHom : CartesianGraph G →g H := ⟨c, by
    rintro x y ⟨i, hi, hrest⟩
    exact hcolor x y (product_standardEdge_of_coordinate i hi hrest)⟩
  obtain ⟨n, α, hα, hproper, ⟨f⟩⟩ := compact_cartesian_finite_quotient
    (fun _ => compactFreeModel_zeroDimensional 2) G H cHom hc
  let J := fun i => AtomGraph (G i) (α i) (hproper i)
  have hJ : ∀ i, InClass 2 (J i) := fun i => compact_factor_atom_inClass (α i) (hα i) (hproper i)
  have hsources : ∀ i, ∃ N : ℕ, ∀ (p q : ℕ) (hp : 5 ≤ p) (hq : 5 ≤ q),
      N ≤ p → N ≤ q → p.Coprime q → Nonempty (TwelveTiles.graph p q hp hq →g J i) :=
    fun i => References.gjks_eventual_twelve_tile_source (J i) (hJ i)
  choose N hN using hsources
  let M : ℕ := Finset.univ.sup N
  refine ⟨M, ?_⟩
  intro p q hp hq hMp hMq hcop
  have hNp : ∀ i, N i ≤ p i := by
    intro i
    exact (Finset.le_sup (f := N) (Finset.mem_univ i)).trans (hMp i)
  have hNq : ∀ i, N i ≤ q i := by
    intro i
    exact (Finset.le_sup (f := N) (Finset.mem_univ i)).trans (hMq i)
  have hfactors : ∀ i, Nonempty (TwelveTiles.graph (p i) (q i) (hp i) (hq i) →g J i) :=
    fun i => hN i (p i) (q i) (hp i) (hq i) (hNp i) (hNq i) (hcop i)
  let φ : ∀ i, TwelveTiles.graph (p i) (q i) (hp i) (hq i) →g J i :=
    fun i => Classical.choice (hfactors i)
  exact ⟨f.comp (cartesianGraphMap φ)⟩

end AbelianTargets
