import AbelianTargets.Actions
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Checked parts of the dimension argument

This file proves the finite-axis counting step of Lemma 7.4, the odd-sum
step and invariant-coloring step of Lemma 7.6, and the final parity split
in Proposition 7.7 of arXiv:2609.39824v1.

`proposition7_7_of_finite_source_obstructions` is explicitly conditional:
the marker graph construction, twelve-tile source extraction, full
rigidity lemma and odd-product obstruction are inputs. They are not
asserted as axioms, and this file does not prove those inputs.
The actual inputs are established in the later marker, twelve-tile,
source-extraction, and odd-product modules. The complete requested result
is `proposition7_7` in `Proposition77.lean`.
-/

namespace AbelianTargets

open scoped BigOperators Pointwise

/-- A signed standard direction, together with its unsigned target axis. -/
structure SignedDirection (m : ℕ) where
  axis : Fin m
  positive : Bool
  deriving DecidableEq

/-- The integer vector corresponding to a signed direction. -/
def SignedDirection.vector {m : ℕ} (s : SignedDirection m) : Lattice m :=
  if s.positive then unitVector s.axis else -unitVector s.axis

/-- The signed-axis representation is faithful as an integer vector. -/
theorem SignedDirection.vector_injective {m : ℕ} :
    Function.Injective (SignedDirection.vector (m := m)) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hi := congrFun h i
  have haxis : i = j := by
    by_contra hij
    cases b <;> cases c <;>
      simp [SignedDirection.vector, unitVector, hij] at hi
  subst j
  cases b <;> cases c
  · rfl
  · norm_num [SignedDirection.vector, unitVector] at hi
  · norm_num [SignedDirection.vector, unitVector] at hi
  · rfl

theorem SignedDirection.vector_eq_iff {m : ℕ} {s t : SignedDirection m} :
    s.vector = t.vector ↔ s = t :=
  ⟨fun h => SignedDirection.vector_injective h, congrArg SignedDirection.vector⟩

/-- Distinct unsigned axes cannot outnumber the target coordinates.
This is the pigeonhole conclusion in Lemma 7.4. -/
theorem axes_card_le {n m : ℕ} (axis : Fin n → Fin m)
    (haxis : Function.Injective axis) : n ≤ m := by
  simpa using Fintype.card_le_of_injective axis haxis

/-- The same counting statement for a family of signed unit vectors. -/
theorem signedDirections_card_le {n m : ℕ} (s : Fin n → SignedDirection m)
    (haxis : Function.Injective (fun i => (s i).axis)) : n ≤ m :=
  axes_card_le (fun i => (s i).axis) haxis

/-- In particular, there cannot be `m + 1` pairwise distinct target axes. -/
theorem no_extra_signedDirection {m : ℕ} (s : Fin (m + 1) → SignedDirection m) :
    ¬Function.Injective (fun i => (s i).axis) := by
  intro h
  have := signedDirections_card_le s h
  omega

theorem SignedDirection.sum_coordinates {m : ℕ} (s : SignedDirection m) :
    (∑ i, s.vector i) = if s.positive then (1 : ℤ) else -1 := by
  cases s with
  | mk axis positive =>
    cases positive <;> simp [SignedDirection.vector, unitVector]

/-- Every signed standard vector has coordinate sum one modulo two. -/
theorem SignedDirection.coordinate_parity {m : ℕ} (s : SignedDirection m) :
    ((∑ i, s.vector i : ℤ) : ZMod 2) = 1 := by
  rw [s.sum_coordinates]
  cases s.positive with
  | false => norm_num; decide
  | true => norm_num

/-- An odd number of signed standard directions cannot sum to zero.
This proves the parity assertion `t ≠ 0` in Lemma 7.6. -/
theorem odd_signedDirection_sum_ne_zero {r m : ℕ}
    (hr : Odd r) (s : Fin r → SignedDirection m) :
    (∑ j, (s j).vector : Lattice m) ≠ 0 := by
  intro hzero
  have hparity : ((∑ j, ∑ i, (s j).vector i : ℤ) : ZMod 2) = 1 := by
    rw [Int.cast_sum]
    simp only [SignedDirection.coordinate_parity]
    simpa using hr.natCast_zmod_two
  have hcoord : (∑ j, ∑ i, (s j).vector i : ℤ) = 0 := by
    rw [Finset.sum_comm]
    have hz : ∀ i : Fin m, (∑ j, (s j).vector i) = 0 := by
      intro i
      have := congrFun hzero i
      simpa only [Finset.sum_apply, Pi.zero_apply] using this
    simp [hz]
  rw [hcoord] at hparity
  norm_num at hparity

/-- A continuous coloring with discrete values that is invariant under
a topologically transitive additive action is constant.
This is the final topological step used in Lemma 7.6. -/
theorem invariant_discrete_coloring_constant
    {G X V : Type*} [AddMonoid G] [TopologicalSpace X] [AddAction G X]
    [AddAction.IsTopologicallyTransitive G X]
    [TopologicalSpace V] [DiscreteTopology V]
    (c : X → V) (hc : Continuous c)
    (hinv : ∀ (g : G) (x : X), c (g +ᵥ x) = c x) :
    ∀ x y : X, c x = c y := by
  intro x y
  let U : Set X := c ⁻¹' {c x}
  let W : Set X := c ⁻¹' {c y}
  have hU : IsOpen U := (isOpen_discrete _).preimage hc
  have hW : IsOpen W := (isOpen_discrete _).preimage hc
  obtain ⟨g, z, hzU, hzW⟩ :=
    AddAction.IsTopologicallyTransitive.exists_vadd_inter
      (M := G) hU ⟨x, rfl⟩ hW ⟨y, rfl⟩
  obtain ⟨u, hu, huz⟩ := Set.mem_vadd_set.mp hzU
  have hux : c u = c x := hu
  have hzy : c z = c y := hzW
  calc
    c x = c u := hux.symm
    _ = c (g +ᵥ u) := (hinv g u).symm
    _ = c z := congrArg c huz
    _ = c y := hzy

/-- Edge-direction hypotheses preceding Lemma 7.3. Proof-dependent edge
arguments keep the map defined only on actual oriented graph edges. -/
structure DirectionLaws {V : Type*} (H : SimpleGraph V) (m : ℕ) where
  direction : ∀ {u v : V}, H.Adj u v → SignedDirection m
  reverse : ∀ {u v : V} (h : H.Adj u v),
    (direction h.symm).vector = -(direction h).vector
  four_walk : ∀ {u v w z : V}
    (huv : H.Adj u v) (hvw : H.Adj v w)
    (hwz : H.Adj w z) (hzu : H.Adj z u),
    (direction huv).vector + (direction hvw).vector +
      (direction hwz).vector + (direction hzu).vector = 0
  straight_middle_unique : ∀ {u v v' w : V}
    (huv : H.Adj u v) (hvw : H.Adj v w)
    (huv' : H.Adj u v') (hv'w : H.Adj v' w),
    direction huv = direction hvw →
    direction huv = direction huv' →
    direction huv = direction hv'w → v = v'

/-- The record's equality of signed directions is equivalent to equality
of the actual integer vectors used in the paper. In particular its final
field proves the literal straight-middle uniqueness law. -/
theorem DirectionLaws.straight_middle_unique_of_vectors
    {V : Type*} {H : SimpleGraph V} {m : ℕ} (laws : DirectionLaws H m)
    {u v v' w : V}
    (huv : H.Adj u v) (hvw : H.Adj v w)
    (huv' : H.Adj u v') (hv'w : H.Adj v' w)
    (h₁ : (laws.direction huv).vector = (laws.direction hvw).vector)
    (h₂ : (laws.direction huv).vector = (laws.direction huv').vector)
    (h₃ : (laws.direction huv).vector = (laws.direction hv'w).vector) : v = v' :=
  laws.straight_middle_unique huv hvw huv' hv'w
    (SignedDirection.vector_injective h₁)
    (SignedDirection.vector_injective h₂)
    (SignedDirection.vector_injective h₃)

/-- Conditional final deduction of Proposition 7.7.

`T k` must be instantiated with the Cartesian product of `k` twelve-tile
graphs, using admissible distinct odd prime parameters selected in
Lemma 7.5. `C r` must be the cycle graph of length `r`.

The explicit hypotheses respectively represent the positive part of
Lemma 7.3, Lemma 7.5(1), Lemma 7.4, Lemma 7.5(2), and Lemma 7.6.
The actual finite-source constructions and their obstruction proofs
remain outside the checked scope of this conditional theorem.
-/
theorem proposition7_7_of_finite_source_obstructions
    {V : Type*} [TopologicalSpace V] (M : SimpleGraph V)
    {B : ℕ → Type*} (T : (k : ℕ) → SimpleGraph (B k))
    (C : (r : ℕ) → SimpleGraph (Fin r))
    {d L : ℕ} (hd : 1 ≤ d) (_hL : 4 ≤ L)
    (marker_membership : InClass d M)
    (even_source : ∀ k : ℕ, 1 ≤ k → InClass (2 * k) M →
      Nonempty (T k →g M))
    (axis_rigidity : ∀ k : ℕ, 1 ≤ k → (T k →g M) →
      ∃ axis : Fin (2 * k) → Fin d, Function.Injective axis)
    (odd_source : ∀ k : ℕ, 1 ≤ k → InClass (2 * k + 1) M →
      ∃ r : ℕ, Odd r ∧ 3 ≤ r ∧ Nonempty ((C r □ T k) →g M))
    (odd_product_obstruction : ∀ k : ℕ, 1 ≤ k → d = 2 * k →
      ∀ r : ℕ, Odd r → 3 ≤ r → ((C r □ T k) →g M) → False) :
    InClass d M ∧ ¬InClass (d + 1) M := by
  refine ⟨marker_membership, ?_⟩
  intro hnext
  by_cases heven : d % 2 = 0
  · let k := d / 2
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hdk : d = 2 * k := by dsimp [k]; omega
    have hn : InClass (2 * k + 1) M := by simpa [hdk] using hnext
    obtain ⟨r, hr, hr3, ⟨f⟩⟩ := odd_source k hk hn
    exact odd_product_obstruction k hk hdk r hr hr3 f
  · let k := (d + 1) / 2
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hdk : d + 1 = 2 * k := by dsimp [k]; omega
    have hn : InClass (2 * k) M := by simpa [hdk] using hnext
    obtain ⟨f⟩ := even_source k hk hn
    obtain ⟨axis, hinj⟩ := axis_rigidity k hk f
    have hcount := axes_card_le axis hinj
    omega

end AbelianTargets
