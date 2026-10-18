import AbelianTargets.Actions
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Fintype.Card

/-!
# Compact finite-product colorings factor through finite coordinate codes

This file proves the compactness argument in Lemma 7.5 of
arXiv:2609.39824. The argument uses finite clopen product rectangles and
their characteristic functions; it introduces no reference axioms.
-/

namespace AbelianTargets

open Set

universe u v w

/-- The Cartesian product graph, for an arbitrary family of factors. -/
def CartesianGraph {ι : Type u} {X : ι → Type v}
    (G : ∀ i, SimpleGraph (X i)) : SimpleGraph (∀ i, X i) where
  Adj x y := ∃ i, (G i).Adj (x i) (y i) ∧ ∀ j, j ≠ i → x j = y j
  symm x y := by
    rintro ⟨i, hi, hrest⟩
    exact ⟨i, hi.symm, fun j hj => (hrest j hj).symm⟩
  loopless := ⟨by rintro x ⟨i, hi, _⟩; exact (G i).irrefl hi⟩

@[simp] theorem cartesianGraph_adj {ι : Type u} {X : ι → Type v}
    (G : ∀ i, SimpleGraph (X i)) (x y : ∀ i, X i) :
    (CartesianGraph G).Adj x y ↔
      ∃ i, (G i).Adj (x i) (y i) ∧ ∀ j, j ≠ i → x j = y j := Iff.rfl

/-- A continuous finite-valued function on a compact finite product of
zero-dimensional spaces depends on finitely many clopen tests in each factor. -/
theorem compact_finite_product_factorization
    {ι : Type u} [Fintype ι] {X : ι → Type v}
    [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    (hzero : ∀ i, ZeroDimensional (X i))
    {V : Type w} [TopologicalSpace V] [DiscreteTopology V]
    (c : (∀ i, X i) → V) (hc : Continuous c) :
    ∃ N : ℕ, ∃ α : ∀ i, X i → (Fin N → Bool),
      (∀ i, Continuous (α i)) ∧
      ∀ x y : ∀ i, X i, (∀ i, α i (x i) = α i (y i)) → c x = c y := by
  classical
  have hrect : ∀ x : ∀ i, X i, ∃ U : ∀ i, Set (X i),
      (∀ i, IsClopen (U i) ∧ x i ∈ U i) ∧
      ∀ y : ∀ i, X i, (∀ i, y i ∈ U i) → c y = c x := by
    intro x
    have hopen : IsOpen (c ⁻¹' {c x}) := (isOpen_discrete _).preimage hc
    obtain ⟨O, hO, hsub⟩ := isOpen_pi_iff'.mp hopen x rfl
    have hnarrow : ∀ i, ∃ U : Set (X i), IsClopen U ∧ x i ∈ U ∧ U ⊆ O i := by
      intro i
      exact (hzero i).exists_subset_of_mem_open (hO i).2 (hO i).1
    choose U hU hxU hUO using hnarrow
    refine ⟨U, fun i => ⟨hU i, hxU i⟩, ?_⟩
    intro y hy
    exact hsub (fun i _ => hUO i (hy i))
  choose U hU hconstant using hrect
  have hboxopen : ∀ x : ∀ i, X i, IsOpen (Set.univ.pi (U x)) := by
    intro x
    exact isOpen_set_pi Set.finite_univ (fun i _ => (hU x i).1.isOpen)
  have hcover : (Set.univ : Set (∀ i, X i)) ⊆ ⋃ x, Set.univ.pi (U x) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, fun i _ => (hU x i).2⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hboxopen hcover
  let N := Fintype.card {x : ∀ i, X i // x ∈ t}
  let e : Fin N ≃ {x : ∀ i, X i // x ∈ t} := (Fintype.equivFin _).symm
  let α : ∀ i, X i → (Fin N → Bool) :=
    fun i a j => (U (e j).val i).boolIndicator a
  refine ⟨N, α, ?_, ?_⟩
  · intro i
    apply continuous_pi
    intro j
    exact (continuous_boolIndicator_iff_isClopen _).mpr (hU (e j).val i).1
  · intro x y hxy
    obtain ⟨z, hzt, hxz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    let j : Fin N := e.symm ⟨z, hzt⟩
    have hej : (e j).val = z := by simp [j]
    have hyz : ∀ i, y i ∈ U z i := by
      intro i
      have htest := congrFun (hxy i) j
      change (U (e j).val i).boolIndicator (x i) =
        (U (e j).val i).boolIndicator (y i) at htest
      rw [hej] at htest
      apply ((U z i).mem_iff_boolIndicator (y i)).mpr
      rw [← htest]
      exact ((U z i).mem_iff_boolIndicator (x i)).mp (hxz i (Set.mem_univ i))
    exact (hconstant z x (fun i => hxz i (Set.mem_univ i))).trans
      (hconstant z y hyz).symm

/-- Nonempty atoms of a finite-valued coordinate code. -/
abbrev CodeAtom {X B : Type*} (α : X → B) := {b : B // b ∈ Set.range α}

/-- Send a point to the atom of the code partition which contains it. -/
def codeAtom {X B : Type*} (α : X → B) (x : X) : CodeAtom α := ⟨α x, ⟨x, rfl⟩⟩

noncomputable def codeRepresentative {X B : Type*} {α : X → B}
    (a : CodeAtom α) : X := a.property.choose

@[simp] theorem codeAtom_representative {X B : Type*} {α : X → B} (a : CodeAtom α) :
    codeAtom α (codeRepresentative a) = a := by
  apply Subtype.ext
  exact a.property.choose_spec

theorem codeAtom_surjective {X B : Type*} (α : X → B) : Function.Surjective (codeAtom α) :=
  fun a => ⟨codeRepresentative a, codeAtom_representative a⟩

/-- Two atoms are joined when an actual factor edge witnesses their adjacency.
The explicit no-edge-inside-an-atom premise makes this a simple graph. -/
def AtomGraph {X B : Type*} (G : SimpleGraph X) (α : X → B)
    (hproper : ∀ x y, G.Adj x y → α x ≠ α y) : SimpleGraph (CodeAtom α) where
  Adj a b := ∃ x y, G.Adj x y ∧ codeAtom α x = a ∧ codeAtom α y = b
  symm a b := by
    rintro ⟨x, y, hxy, hxa, hyb⟩
    exact ⟨y, x, hxy.symm, hyb, hxa⟩
  loopless := ⟨by
    rintro a ⟨x, y, hxy, hxa, hya⟩
    exact hproper x y hxy (congrArg Subtype.val (hxa.trans hya.symm))⟩

/-- The atom projection is a graph homomorphism. -/
def atomProjection {X B : Type*} (G : SimpleGraph X) (α : X → B)
    (hproper : ∀ x y, G.Adj x y → α x ≠ α y) : G →g AtomGraph G α hproper where
  toFun := codeAtom α
  map_rel' hxy := ⟨_, _, hxy, rfl, rfl⟩

/-- Factorwise graph homomorphisms give a homomorphism on Cartesian products. -/
def cartesianGraphMap {ι : Type u} {X : ι → Type v} {Y : ι → Type w}
    {G : ∀ i, SimpleGraph (X i)} {J : ∀ i, SimpleGraph (Y i)}
    (f : ∀ i, G i →g J i) : CartesianGraph G →g CartesianGraph J where
  toFun x i := f i (x i)
  map_rel' := by
    rintro x y ⟨i, hi, hrest⟩
    exact ⟨i, (f i).map_adj hi, fun j hj => congrArg (f j) (hrest j hj)⟩

/-- A color factorization forces each coordinate atom to contain no graph edge:
fix the other coordinates and use the absence of target loops. -/
theorem coordinate_code_proper {ι : Type u} {X : ι → Type v}
    [∀ i, Nonempty (X i)] {B : ι → Type w}
    (G : ∀ i, SimpleGraph (X i)) {V : Type*} (H : SimpleGraph V)
    (c : CartesianGraph G →g H) (α : ∀ i, X i → B i)
    (hfactor : ∀ x y : ∀ i, X i,
      (∀ i, α i (x i) = α i (y i)) → c x = c y) :
    ∀ i x y, (G i).Adj x y → α i x ≠ α i y := by
  classical
  intro i a b hadj hab
  let z : ∀ j, X j := fun j => Classical.choice (inferInstance : Nonempty (X j))
  let x := Function.update z i a
  let y := Function.update z i b
  have hcart : (CartesianGraph G).Adj x y := by
    refine ⟨i, ?_, ?_⟩
    · simpa [x, y] using hadj
    · intro j hji
      simp [x, y, hji]
  have hcodes : ∀ j, α j (x j) = α j (y j) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [x, y] using hab
    · simp [x, y, hji]
  exact H.ne_of_adj (c.map_adj hcart) (hfactor x y hcodes)

/-- Color a tuple of partition atoms by choosing representatives in its factors. -/
noncomputable def atomColor {ι : Type u} {X : ι → Type v} {B : ι → Type w}
    {V : Type*} (c : (∀ i, X i) → V) (α : ∀ i, X i → B i)
    (a : ∀ i, CodeAtom (α i)) : V := c (fun i => codeRepresentative (a i))

theorem atomColor_code {ι : Type u} {X : ι → Type v} {B : ι → Type w}
    {V : Type*} (c : (∀ i, X i) → V) (α : ∀ i, X i → B i)
    (hfactor : ∀ x y : ∀ i, X i,
      (∀ i, α i (x i) = α i (y i)) → c x = c y) (x : ∀ i, X i) :
    atomColor c α (fun i => codeAtom (α i) (x i)) = c x := by
  apply hfactor
  intro i
  exact congrArg Subtype.val (codeAtom_representative (codeAtom (α i) (x i)))

/-- The atom-tuple coloring is a graph homomorphism on the Cartesian product
of factor atom graphs. This is the finite graph in the compactness argument. -/
noncomputable def atomColorHom {ι : Type u} {X : ι → Type v} {B : ι → Type w}
    (G : ∀ i, SimpleGraph (X i)) {V : Type*} (H : SimpleGraph V)
    (c : CartesianGraph G →g H) (α : ∀ i, X i → B i)
    (hfactor : ∀ x y : ∀ i, X i,
      (∀ i, α i (x i) = α i (y i)) → c x = c y)
    (hproper : ∀ i x y, (G i).Adj x y → α i x ≠ α i y) :
    CartesianGraph (fun i => AtomGraph (G i) (α i) (hproper i)) →g H where
  toFun := atomColor c α
  map_rel' := by
    classical
    rintro a b ⟨i, ⟨p, q, hpq, hpa, hqb⟩, hrest⟩
    let z : ∀ j, X j := fun j => codeRepresentative (a j)
    let x := Function.update z i p
    let y := Function.update z i q
    have hx : (fun j => codeAtom (α j) (x j)) = a := by
      funext j
      by_cases hji : j = i
      · subst j
        simpa [x] using hpa
      · simp [x, z, hji]
    have hy : (fun j => codeAtom (α j) (y j)) = b := by
      funext j
      by_cases hji : j = i
      · subst j
        simpa [y] using hqb
      · simp [y, z, hji, ← hrest j hji]
    have hxy : (CartesianGraph G).Adj x y := by
      refine ⟨i, ?_, ?_⟩
      · simpa [x, y] using hpq
      · intro j hji
        simp [x, y, hji]
    have hca : atomColor c α a = c x := by rw [← hx]; exact atomColor_code c α hfactor x
    have hcb : atomColor c α b = c y := by rw [← hy]; exact atomColor_code c α hfactor y
    rw [hca, hcb]
    exact c.map_adj hxy

theorem continuous_codeAtom {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]
    (α : X → B) (hα : Continuous α) : Continuous (codeAtom α) :=
  hα.subtype_mk (fun x => ⟨x, rfl⟩)

/-- The complete finite-quotient compactness statement: a continuous coloring
of the product produces finite factor atom graphs and a homomorphism from
their Cartesian product to the target. -/
theorem compact_cartesian_finite_quotient
    {ι : Type u} [Fintype ι] {X : ι → Type v}
    [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
    (hzero : ∀ i, ZeroDimensional (X i))
    (G : ∀ i, SimpleGraph (X i))
    {V : Type w} [TopologicalSpace V] [DiscreteTopology V] (H : SimpleGraph V)
    (c : CartesianGraph G →g H) (hc : Continuous c) :
    ∃ N : ℕ, ∃ α : ∀ i, X i → (Fin N → Bool),
      (∀ i, Continuous (α i)) ∧
      ∃ hproper : ∀ i x y, (G i).Adj x y → α i x ≠ α i y,
        Nonempty (CartesianGraph (fun i => AtomGraph (G i) (α i) (hproper i)) →g H) := by
  obtain ⟨N, α, hα, hfactor⟩ := compact_finite_product_factorization hzero c hc
  let hproper := coordinate_code_proper G H c α hfactor
  exact ⟨N, α, hα, hproper, ⟨atomColorHom G H c α hfactor hproper⟩⟩

end AbelianTargets
