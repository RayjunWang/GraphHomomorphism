import AbelianTargets.SupportGeometry
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Pushforward of probability support pairs

Graph homomorphisms induce continuous maps of the concrete support spaces,
commuting with the shore swaps. This permits removal of isolated vertices
without adding a neighbor-choice hypothesis to the target statements.
-/

open scoped BigOperators

namespace AbelianTargets

noncomputable section

namespace Probability

variable {V W : Type*} [Fintype V] [Fintype W]

attribute [local instance] Classical.propDecidable

def push (f : V → W) (p : Probability V) : Probability W := by
  classical
  exact {
    mass := fun w => ∑ v, if f v = w then p.mass v else 0
    nonneg := fun w => Finset.sum_nonneg (fun v _ => by split <;> simp [p.nonneg v])
    sum_one := by rw [Finset.sum_comm]; simpa using p.sum_one }

theorem push_mass (f : V → W) (p : Probability V) (w : W) :
    (push f p).mass w = ∑ v, if f v = w then p.mass v else 0 := rfl

theorem continuous_push (f : V → W) : Continuous (push f) := by
  classical
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro w
  change Continuous (fun p : Probability V => ∑ v, if f v = w then p.mass v else 0)
  apply continuous_finsetSum
  intro v _
  by_cases h : f v = w
  · simpa only [h, if_true] using continuous_mass_apply v
  · simp only [h, if_false]
    exact continuous_const

theorem push_pos_iff (f : V → W) (p : Probability V) (w : W) :
    0 < (push f p).mass w ↔ ∃ v, f v = w ∧ 0 < p.mass v := by
  classical
  rw [push_mass, Finset.sum_pos_iff_of_nonneg]
  · simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv⟩
      by_cases h : f v = w
      · exact ⟨v, h, by simpa only [h, if_true] using hv⟩
      · simp only [h, if_false, lt_self_iff_false] at hv
    · rintro ⟨v, hv, hp⟩
      exact ⟨v, by simpa only [hv, if_true] using hp⟩
  · intro v _
    split <;> simp [p.nonneg v]

end Probability

namespace SupportPair

variable {V W : Type*} [Fintype V] [Fintype W]
  {H : SimpleGraph V} {J : SimpleGraph W}

def map (f : H →g J) (z : SupportPair H) : SupportPair J :=
  ⟨(Probability.push f z.left, Probability.push f z.right), by
    intro a b ha hb
    obtain ⟨u, hu, hpu⟩ := (Probability.push_pos_iff f z.left a).mp ha
    obtain ⟨v, hv, hpv⟩ := (Probability.push_pos_iff f z.right b).mp hb
    subst a
    subst b
    exact f.map_adj (compatible H z u v hpu hpv)⟩

theorem continuous_map (f : H →g J) : Continuous (map f) :=
  (((Probability.continuous_push f).comp (continuous_left H)).prodMk
    ((Probability.continuous_push f).comp (continuous_right H))).subtype_mk _

@[simp] theorem map_swap (f : H →g J) (z : SupportPair H) :
    map f (swap H z) = swap J (map f z) := by
  apply Subtype.ext
  rfl

def continuousMap (f : H →g J) : ContinuousMap (SupportPair H) (SupportPair J) :=
  ⟨map f, continuous_map f⟩

end SupportPair

end

end AbelianTargets
