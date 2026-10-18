import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Probability coordinates and exact graph rounding

This file formalizes the numerical part of the proof of Theorem 1.4 in
arXiv:2609.39824, Section 6. It does not assume existence of the geometric
approximate parity field used earlier in that proof.
-/

open scoped BigOperators

namespace AbelianTargets

/-- A probability distribution on a finite vertex type. -/
@[ext] structure Probability (V : Type*) [Fintype V] where
  mass : V → ℝ
  nonneg : ∀ v, 0 ≤ mass v
  sum_one : ∑ v, mass v = 1

namespace Probability

variable {V : Type*} [Fintype V]

/-- Probability distributions carry the topology induced by their coordinates. -/
instance : TopologicalSpace (Probability V) :=
  TopologicalSpace.induced mass inferInstance

theorem continuous_mass : Continuous (mass : Probability V → V → ℝ) :=
  continuous_induced_dom

theorem continuous_mass_apply (v : V) :
    Continuous (fun p : Probability V => p.mass v) :=
  (continuous_apply v).comp continuous_mass

theorem mass_injective : Function.Injective (mass : Probability V → V → ℝ) := by
  intro p q h
  exact Probability.ext h

instance : T1Space (Probability V) :=
  t1Space_of_injective_of_continuous mass_injective continuous_mass

/-- An empty finite type cannot carry a probability distribution. -/
theorem nonempty (p : Probability V) : Nonempty V := by
  classical
  by_contra h
  haveI : IsEmpty V := not_nonempty_iff.mp h
  have hsum : (0 : ℝ) = 1 := by simpa using p.sum_one
  exact zero_ne_one hsum

/-- A finite probability distribution has a maximum of mass at least `1 / |V|`. -/
theorem exists_max_mass (p : Probability V) :
    ∃ v, (∀ w, p.mass w ≤ p.mass v) ∧
      1 / (Fintype.card V : ℝ) ≤ p.mass v := by
  classical
  letI : Nonempty V := p.nonempty
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ p.mass
    Finset.univ_nonempty
  have hmax : ∀ w, p.mass w ≤ p.mass v := fun w => hv w (Finset.mem_univ w)
  have hcard : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty V)
  have hsum : (1 : ℝ) ≤ (Fintype.card V : ℝ) * p.mass v := by
    calc
      1 = ∑ w, p.mass w := p.sum_one.symm
      _ ≤ ∑ _w : V, p.mass v := Finset.sum_le_sum (fun w _ => hmax w)
      _ = (Fintype.card V : ℝ) * p.mass v := by simp
  refine ⟨v, hmax, (div_le_iff₀ hcard).2 ?_⟩
  simpa only [mul_comm] using hsum

/-- A deterministic choice of a vertex with maximum probability mass. -/
noncomputable def chooseMax [Nonempty V] (p : Probability V) : V :=
  Classical.choose p.exists_max_mass

theorem le_chooseMax [Nonempty V] (p : Probability V) (v : V) :
    p.mass v ≤ p.mass (chooseMax p) :=
  (Classical.choose_spec p.exists_max_mass).1 v

theorem chooseMax_bound [Nonempty V] (p : Probability V) :
    1 / (Fintype.card V : ℝ) ≤ p.mass (chooseMax p) :=
  (Classical.choose_spec p.exists_max_mass).2

theorem chooseMax_pos [Nonempty V] (p : Probability V) :
    0 < p.mass (chooseMax p) := by
  have hcard : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty V)
  exact (one_div_pos.mpr hcard).trans_le p.chooseMax_bound

theorem chooseMax_mass_pos [Nonempty V] (p : Probability V) :
    0 < p.mass (chooseMax p) := p.chooseMax_pos

end Probability

variable {V : Type*} [Fintype V]

/-- Every positive-mass vertex in one shore is adjacent to every positive-mass
vertex in the other shore; this is the support condition defining `𝒟(H)`. -/
def Compatible (H : SimpleGraph V) (p q : Probability V) : Prop :=
  ∀ u v, 0 < p.mass u → 0 < q.mass v → H.Adj u v

/-- The precise rounding implication in Section 6: an approximation with error
less than `1 / (2 * |V|)` gives an exact graph edge between maximum-mass choices. -/
theorem rounding_edge [Nonempty V] (H : SimpleGraph V)
    (p q p' : Probability V) (hcompat : Compatible H p q)
    (hclose : ∀ v,
      |p'.mass v - q.mass v| < 1 / (2 * (Fintype.card V : ℝ))) :
    H.Adj (Probability.chooseMax p) (Probability.chooseMax p') := by
  have hcard : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty V)
  have hhalf : 1 / (2 * (Fintype.card V : ℝ)) <
      1 / (Fintype.card V : ℝ) :=
    one_div_lt_one_div_of_lt hcard (by linarith)
  have hdiff := (abs_lt.mp (hclose (Probability.chooseMax p'))).2
  have hmass := p'.chooseMax_bound
  have hq : 0 < q.mass (Probability.chooseMax p') := by linarith
  exact hcompat _ _ p.chooseMax_pos hq

end AbelianTargets
