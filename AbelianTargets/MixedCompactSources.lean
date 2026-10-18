import AbelianTargets.EvenFiniteSources
import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# Compact factor graphs for odd-dimensional actions

The extra factor has one lattice coordinate; all remaining factors have
two. This is a variant of Lemma 7.5's compactness construction using the
universal compact free model in every factor.
-/

namespace AbelianTargets

abbrev mixedDimension {k : ℕ} : Option (Fin k) → ℕ
  | none => 1
  | some _ => 2

def mixedBlockVector {k : ℕ} (g : Lattice (2 * k + 1)) :
    (i : Option (Fin k)) → Lattice (mixedDimension i)
  | none => fun _ => g 0
  | some i => fun j => g (blockIndex k (i, j)).succ

@[simp] theorem mixedBlockVector_zero {k : ℕ} (i : Option (Fin k)) :
    mixedBlockVector (0 : Lattice (2 * k + 1)) i = 0 := by cases i <;> rfl

@[simp] theorem mixedBlockVector_add {k : ℕ}
    (g h : Lattice (2 * k + 1)) (i : Option (Fin k)) :
    mixedBlockVector (g + h) i = mixedBlockVector g i + mixedBlockVector h i := by
  cases i <;> rfl

theorem mixedBlockVector_unit_first {k : ℕ} (i : Option (Fin k)) :
    mixedBlockVector (unitVector (0 : Fin (2 * k + 1))) i =
      match i with
      | none => unitVector (0 : Fin 1)
      | some _ => 0 := by
  cases i with
  | none =>
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [mixedBlockVector, unitVector]
  | some i =>
      funext j
      simp [mixedBlockVector, unitVector]

theorem mixedBlockVector_unit_rest {k : ℕ} (a : Fin k) (j : Fin 2) (i : Option (Fin k)) :
    mixedBlockVector (unitVector (blockIndex k (a, j)).succ) i =
      match i with
      | none => 0
      | some b => if b = a then unitVector j else 0 := by
  classical
  cases i with
  | none =>
      funext l
      have hzero : (0 : Fin (2 * k + 1)) ≠ (blockIndex k (a, j)).succ := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_zero, Fin.val_succ] at this
        omega
      simp [mixedBlockVector, unitVector, hzero]
  | some b =>
      funext l
      by_cases hba : b = a
      · subst b
        simp [mixedBlockVector, unitVector, (blockIndex k).injective.eq_iff]
      · simp [mixedBlockVector, unitVector, (blockIndex k).injective.eq_iff, hba]

abbrev MixedCompactModel (k : ℕ) :=
  (i : Option (Fin k)) → CompactFreeModel (mixedDimension i)

instance mixedCompactModelAction (k : ℕ) :
    AddAction (Lattice (2 * k + 1)) (MixedCompactModel k) where
  vadd g x i := mixedBlockVector g i +ᵥ x i
  zero_vadd x := by
    funext i
    change mixedBlockVector 0 i +ᵥ x i = x i
    rw [mixedBlockVector_zero, zero_vadd]
  add_vadd g h x := by
    funext i
    change mixedBlockVector (g + h) i +ᵥ x i =
      mixedBlockVector g i +ᵥ (mixedBlockVector h i +ᵥ x i)
    rw [mixedBlockVector_add, add_vadd]

instance mixedCompactModelContinuousVAdd (k : ℕ) :
    ContinuousVAdd (Lattice (2 * k + 1)) (MixedCompactModel k) where
  continuous_vadd := continuous_prod_of_discrete_left.mpr (by
    intro g
    exact continuous_pi (fun i =>
      (continuous_const_vadd (mixedBlockVector g i)).comp (continuous_apply i)))

theorem mixedCompactModel_isFree (k : ℕ) :
    IsFree (G := Lattice (2 * k + 1)) (X := MixedCompactModel k) := by
  intro g x hfix
  have hblock : ∀ i, mixedBlockVector g i = 0 := by
    intro i
    exact compactFreeModel_isFree (mixedDimension i) (mixedBlockVector g i) (x i)
      (congrFun hfix i)
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact congrFun (hblock none) (0 : Fin 1)
  · obtain ⟨⟨i, l⟩, hj⟩ := (blockIndex k).surjective j
    simpa only [mixedBlockVector, hj] using congrFun (hblock (some i)) l

theorem mixedCompactModel_zeroDimensional (k : ℕ) :
    ZeroDimensional (MixedCompactModel k) := isTopologicalBasis_isClopen

/-- A coordinate edge is a standard edge of the odd-dimensional product. -/
theorem mixed_standardEdge_of_coordinate {k : ℕ}
    {x y : MixedCompactModel k} (i : Option (Fin k))
    (hxy : StandardEdge (d := mixedDimension i) (x i) (y i))
    (hrest : ∀ a, a ≠ i → x a = y a) :
    StandardEdge (d := 2 * k + 1) x y := by
  classical
  cases i with
  | none =>
      obtain ⟨j, h | h⟩ := hxy
      all_goals have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      all_goals subst j
      · refine ⟨0, Or.inl ?_⟩
        funext a
        change mixedBlockVector (unitVector (0 : Fin (2 * k + 1))) a +ᵥ x a = y a
        cases a with
        | none => simpa only [mixedBlockVector_unit_first] using h
        | some a => simpa only [mixedBlockVector_unit_first, zero_vadd] using hrest (some a) (by simp)
      · refine ⟨0, Or.inr ?_⟩
        funext a
        change mixedBlockVector (unitVector (0 : Fin (2 * k + 1))) a +ᵥ y a = x a
        cases a with
        | none => simpa only [mixedBlockVector_unit_first] using h
        | some a => simpa only [mixedBlockVector_unit_first, zero_vadd] using (hrest (some a) (by simp)).symm
  | some i =>
      obtain ⟨j, h | h⟩ := hxy
      · refine ⟨(blockIndex k (i, j)).succ, Or.inl ?_⟩
        funext a
        change mixedBlockVector (unitVector (blockIndex k (i, j)).succ) a +ᵥ x a = y a
        rw [mixedBlockVector_unit_rest]
        cases a with
        | none => simpa only [zero_vadd] using hrest none (by simp)
        | some a =>
            by_cases hai : a = i
            · subst a
              simpa using h
            · simpa [hai] using hrest (some a) (by simpa using hai)
      · refine ⟨(blockIndex k (i, j)).succ, Or.inr ?_⟩
        funext a
        change mixedBlockVector (unitVector (blockIndex k (i, j)).succ) a +ᵥ y a = x a
        rw [mixedBlockVector_unit_rest]
        cases a with
        | none => simpa only [zero_vadd] using (hrest none (by simp)).symm
        | some a =>
            by_cases hai : a = i
            · subst a
              simpa using h
            · simpa [hai] using (hrest (some a) (by simpa using hai)).symm

theorem compact_factor_atom_inClass_dimension
    {d : ℕ} {B : Type*} [TopologicalSpace B] (α : CompactFreeModel d → B)
    (hα : Continuous α)
    (hproper : ∀ x y, (SchreierGraph (compactFreeModel_isFree d)).Adj x y → α x ≠ α y) :
    InClass d (AtomGraph (SchreierGraph (compactFreeModel_isFree d)) α hproper) := by
  obtain ⟨f, hf, hequiv⟩ := exists_continuous_equivariant_compactFreeModel
    (freeShift_zeroDimensional d) (freeShift_isFree d)
  refine ⟨fun x => codeAtom α (f x), (continuous_codeAtom α hα).comp hf, ?_⟩
  intro x y hxy
  exact ⟨f x, f y, standardEdge_map f hequiv hxy, rfl, rfl⟩

/-- The compactness part of the odd-dimensional source extraction produces
finite target factors in `𝓗₁,𝓗₂,...,𝓗₂`, and a homomorphism from their product.
The subsequent odd-cycle and twelve-tile substitutions are separate. -/
theorem odd_dimension_finite_factor_graphs
    {V : Type*} [TopologicalSpace V] [Fintype V] [DiscreteTopology V]
    (H : SimpleGraph V) (k : ℕ) (hH : InClass (2 * k + 1) H) :
    ∃ N : ℕ, ∃ α : (i : Option (Fin k)) → CompactFreeModel (mixedDimension i) → (Fin N → Bool),
      (∀ i, Continuous (α i)) ∧
      ∃ hproper : ∀ i x y, (SchreierGraph (compactFreeModel_isFree (mixedDimension i))).Adj x y →
        α i x ≠ α i y,
      (∀ i, InClass (mixedDimension i)
        (AtomGraph (SchreierGraph (compactFreeModel_isFree (mixedDimension i))) (α i) (hproper i))) ∧
      Nonempty (CartesianGraph (fun i =>
        AtomGraph (SchreierGraph (compactFreeModel_isFree (mixedDimension i))) (α i) (hproper i)) →g H) := by
  classical
  have huni := References.bernshteyn_theorem_1_12 H (2 * k + 1) (by omega) hH
  obtain ⟨c, hc, hcolor⟩ := huni (MixedCompactModel k)
    (mixedCompactModel_zeroDimensional k) (mixedCompactModel_isFree k)
  let G := fun i : Option (Fin k) => SchreierGraph (compactFreeModel_isFree (mixedDimension i))
  let cHom : CartesianGraph G →g H := ⟨c, by
    rintro x y ⟨i, hi, hrest⟩
    exact hcolor x y (mixed_standardEdge_of_coordinate i hi hrest)⟩
  obtain ⟨N, α, hα, hproper, hf⟩ := compact_cartesian_finite_quotient
    (fun i => compactFreeModel_zeroDimensional (mixedDimension i)) G H cHom hc
  exact ⟨N, α, hα, hproper, fun i => compact_factor_atom_inClass_dimension (α i) (hα i) (hproper i), hf⟩

/-- Substitute maps into the first and the remaining factors of an optional
index family. The source is the usual binary box product with a Cartesian graph. -/
def optionCartesianHom {ι : Type*} {X : Option ι → Type*}
    (J : ∀ i, SimpleGraph (X i)) {A : Type*} (C : SimpleGraph A)
    {B : ι → Type*} (T : ∀ i, SimpleGraph (B i))
    (f₀ : C →g J none) (f : ∀ i, T i →g J (some i)) :
    (C □ CartesianGraph T) →g CartesianGraph J where
  toFun x i := match i with | none => f₀ x.1 | some i => f i (x.2 i)
  map_rel' := by
    rintro x y (⟨hxy, hrest⟩ | ⟨⟨i, hi, hrest⟩, hfirst⟩)
    · refine ⟨none, f₀.map_adj hxy, ?_⟩
      intro a ha
      cases a with
      | none => exact False.elim (ha rfl)
      | some a => exact congrArg (f a) (congrFun hrest a)
    · refine ⟨some i, (f i).map_adj hi, ?_⟩
      intro a ha
      cases a with
      | none => exact congrArg f₀ hfirst
      | some a => exact congrArg (f a) (hrest a (by simpa using ha))

end AbelianTargets
