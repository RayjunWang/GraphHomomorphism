import AbelianTargets.ClopenMarkers
import AbelianTargets.MarkerMap
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.Discrete
import Mathlib.Data.Countable.Basic

/-!
# Existence of clopen separated covering orbit markers

This file completes the positive membership of the concrete graph in
Lemma 7.3. A countable clopen independent cover is built from freeness,
zero-dimensionality, and second countability. The greedy clopen maximal
independent set then supplies the required orbit markers.
-/

namespace AbelianTargets

universe u

noncomputable section

def nearDisplacements (d L : ℕ) : Finset (Lattice d) :=
  (Fintype.piFinset fun _ => Finset.Icc (-(L : ℤ)) (L : ℤ)).filter (· ≠ 0)

theorem mem_nearDisplacements {d L : ℕ} (g : Lattice d) :
    g ∈ nearDisplacements d L ↔ (∀ i, |g i| ≤ (L : ℤ)) ∧ g ≠ 0 := by
  simp only [nearDisplacements, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_Icc, abs_le]

theorem neg_mem_nearDisplacements {d L : ℕ} {g : Lattice d}
    (hg : g ∈ nearDisplacements d L) : -g ∈ nearDisplacements d L := by
  rcases (mem_nearDisplacements _).1 hg with ⟨hbound, hne⟩
  apply (mem_nearDisplacements _).2
  exact ⟨by simpa only [Pi.neg_apply, abs_neg] using hbound, neg_ne_zero.mpr hne⟩

variable {d L : ℕ} {X : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]

/-- The finite-displacement graph used in Lemmas 3.1 and 7.3. -/
def displacementGraph (free : IsFree (G := Lattice d) (X := X)) : SimpleGraph X where
  Adj x y := ∃ g ∈ nearDisplacements d L, g +ᵥ x = y
  symm := by
    rintro x y ⟨g, hg, hxy⟩
    refine ⟨-g, neg_mem_nearDisplacements hg, ?_⟩
    rw [← hxy, ← add_vadd, neg_add_cancel, zero_vadd]
  loopless := by
    constructor
    rintro x ⟨g, hg, hfix⟩
    exact ((mem_nearDisplacements _).1 hg).2 (free g x hfix)

variable [ContinuousVAdd (Lattice d) X]

omit [TopologicalSpace X] [ContinuousVAdd (Lattice d) X] in
/-- The neighbor set is a finite union of translates of the original set. -/
theorem neighborSet_displacementGraph (free : IsFree (G := Lattice d) (X := X))
    (S : Set X) :
    NeighborSet (displacementGraph (L := L) free) S =
      ⋃ g ∈ nearDisplacements d L, {y : X | (-g) +ᵥ y ∈ S} := by
  ext y
  constructor
  · rintro ⟨x, hx, g, hg, hxy⟩
    apply Set.mem_iUnion.mpr
    refine ⟨g, Set.mem_iUnion.mpr ⟨hg, ?_⟩⟩
    change (-g) +ᵥ y ∈ S
    rw [← hxy, ← add_vadd, neg_add_cancel, zero_vadd]
    exact hx
  · intro hy
    obtain ⟨g, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨hg, hy⟩ := Set.mem_iUnion.mp hy
    refine ⟨(-g) +ᵥ y, hy, g, hg, ?_⟩
    rw [← add_vadd, add_neg_cancel, zero_vadd]

theorem neighbor_clopen_displacementGraph
    (free : IsFree (G := Lattice d) (X := X))
    (S : Set X) (hS : IsClopen S) :
    IsClopen (NeighborSet (displacementGraph (L := L) free) S) := by
  rw [neighborSet_displacementGraph]
  apply isClopen_biUnion_finset
  intro g _hg
  exact hS.preimage (continuous_const_vadd (-g))

variable [T1Space X]

/-- A local clopen neighborhood disjoint from its translate by a fixed
nonzero group element. -/
theorem exists_clopen_shift_independent
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X))
    (x : X) (g : Lattice d) (hg : g ≠ 0) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ ∀ y ∈ U, g +ᵥ y ∉ U := by
  have hxg : x ≠ g +ᵥ x := by
    intro h
    exact hg (free g x h.symm)
  obtain ⟨B, hB, hxB, hBsub⟩ := zeroDim.exists_subset_of_mem_open
    (show x ∈ ({g +ᵥ x} : Set X)ᶜ by simpa using hxg)
    isClosed_singleton.isOpen_compl
  have hgB : g +ᵥ x ∉ B := by
    intro h
    exact hBsub h (Set.mem_singleton _)
  refine ⟨B ∩ (fun y : X => g +ᵥ y) ⁻¹' Bᶜ,
    hB.inter (hB.compl.preimage (continuous_const_vadd g)), ⟨hxB, hgB⟩, ?_⟩
  intro y hy hgy
  exact hy.2 hgy.1

/-- Every point has a clopen independent neighborhood for the complete
finite-displacement graph. -/
theorem exists_clopen_displacement_independent
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X))
    (x : X) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧
      GraphIndependent (displacementGraph (L := L) free) U := by
  classical
  let I := {g : Lattice d // g ∈ nearDisplacements d L}
  have hlocal : ∀ g : I, ∃ U : Set X,
      IsClopen U ∧ x ∈ U ∧ ∀ y ∈ U, g.val +ᵥ y ∉ U := by
    intro g
    exact exists_clopen_shift_independent zeroDim free x g.val
      ((mem_nearDisplacements _).1 g.property).2
  choose U hclopen hx hshift using hlocal
  refine ⟨⋂ g : I, U g, isClopen_iInter_of_finite hclopen,
    Set.mem_iInter.mpr hx, ?_⟩
  intro y hy z hz hadj
  obtain ⟨g, hg, hgyz⟩ := hadj
  have hyU := Set.mem_iInter.mp hy (⟨g, hg⟩ : I)
  have hzU := Set.mem_iInter.mp hz (⟨g, hg⟩ : I)
  exact hshift ⟨g, hg⟩ y hyU (hgyz.symm ▸ hzU)

variable [SecondCountableTopology X]

/-- Second countability turns the local independent neighborhoods into
a countable clopen independent cover. -/
theorem exists_countable_clopen_independent_cover
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X)) :
    ∃ C : ℕ → Set X, (∀ n, IsClopen (C n)) ∧
      (∀ n, GraphIndependent (displacementGraph (L := L) free) (C n)) ∧
      ∀ x, ∃ n, x ∈ C n := by
  classical
  by_cases hX : Nonempty X
  · letI : Nonempty X := hX
    choose U hclopen hx hindep using
      exists_clopen_displacement_independent (L := L) zeroDim free
    obtain ⟨f, hcov⟩ := isLindelof_univ.indexed_countable_subcover
      U (fun x => (hclopen x).isOpen) (by
        intro x _hx
        exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
    refine ⟨fun n => U (f n), fun n => hclopen (f n), fun n => hindep (f n), ?_⟩
    intro x
    exact Set.mem_iUnion.mp (hcov (Set.mem_univ x))
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    refine ⟨fun _ => ∅, fun _ => isClopen_empty, ?_, ?_⟩
    · intro n x
      exact isEmptyElim x
    · intro x
      exact isEmptyElim x

/-- A free action on a zero-dimensional second-countable T1 space has
an actual clopen separated covering marker set at every finite scale. -/
theorem exists_clopenMarkers
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X)) :
    Nonempty (ClopenMarkers d L X) := by
  classical
  obtain ⟨C, hclopen, hindep, hcover⟩ :=
    exists_countable_clopen_independent_cover (L := L) zeroDim free
  obtain ⟨A, hA, hAi, hmax⟩ := exists_clopen_maximal_independent
    (displacementGraph (L := L) free) C hclopen hindep hcover
    (neighbor_clopen_displacementGraph free)
  refine ⟨⟨A, hA, ?_, ?_⟩⟩
  · intro x u v hu hv hne
    by_contra hnone
    have hg : v - u ∈ nearDisplacements d L := by
      apply (mem_nearDisplacements _).2
      constructor
      · intro i
        have hi : |u i - v i| ≤ (L : ℤ) :=
          le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
        simpa only [Pi.sub_apply, abs_sub_comm] using hi
      · exact sub_ne_zero.mpr hne.symm
    apply hAi (u +ᵥ x) hu (v +ᵥ x) hv
    refine ⟨v - u, hg, ?_⟩
    rw [← add_vadd, sub_add_cancel]
  · intro x u
    by_cases hu : u +ᵥ x ∈ A
    · exact ⟨u, hu, by intro i; simp⟩
    · obtain ⟨b, hb, g, hg, hgb⟩ := hmax (u +ᵥ x) hu
      have hab : (u - g) +ᵥ x = b := by
        have hlat : u - g = -g + u := by rw [sub_eq_add_neg, add_comm]
        rw [hlat, add_vadd, ← hgb, ← add_vadd, neg_add_cancel, zero_vadd]
      refine ⟨u - g, hab.symm ▸ hb, ?_⟩
      intro i
      simpa only [Pi.sub_apply, sub_sub_cancel] using
        ((mem_nearDisplacements _).1 hg).1 i

/-- The concrete finite marker graph receives a continuous homomorphism
from every free zero-dimensional Polish lattice action. -/
theorem markerGraph_universalTarget
    (hL : 4 ≤ L) : UniversalTarget.{u} d (MarkerGraph d L hL) := by
  intro X _ _ _ _ zeroDim free
  obtain ⟨markers⟩ := exists_clopenMarkers (L := L) zeroDim free
  exact markers.hasContinuousHom hL

/-- A subspace of the full binary shift inherits its basis of clopen sets. -/
theorem freeShift_zeroDimensional (d : ℕ) : ZeroDimensional (FreeShift d) := by
  have hb := (isTopologicalBasis_isClopen (X := ShiftSpace d)).induced
    (fun x : FreeShift d => x.val)
  apply TopologicalSpace.IsTopologicalBasis.of_isOpen_of_subset
    (fun U hU => hU.isOpen) hb
  rintro U ⟨W, hW, rfl⟩
  exact hW.preimage continuous_induced_dom

instance freeShiftT1Space (d : ℕ) : T1Space (FreeShift d) :=
  inferInstanceAs (T1Space {x : ShiftSpace d //
    ∀ g : Lattice d, shift g x = x → g = 0})

instance freeShiftSecondCountableTopology (d : ℕ) : SecondCountableTopology (FreeShift d) :=
  TopologicalSpace.secondCountableTopology_induced (FreeShift d) (ShiftSpace d)
    (fun x : FreeShift d => x.val)

/-- The finite graph in Lemma 7.3 actually belongs to the paper's target class. -/
theorem markerGraph_inClass (d L : ℕ) (hL : 4 ≤ L) :
    InClass d (MarkerGraph d L hL) := by
  obtain ⟨markers⟩ := exists_clopenMarkers (L := L)
    (freeShift_zeroDimensional d) (freeShift_isFree d)
  exact markers.hasContinuousHom hL

end

end AbelianTargets
