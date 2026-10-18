import AbelianTargets.OddCycleSources
import AbelianTargets.ShiftTransitivity

/-!
# Straight-middle transfers around an odd cycle

This proves the final algebraic and dynamical mechanism of Lemma 7.6.
Equal signed edge directions yield equal straight middle vertices; an odd
cycle then yields invariance under a nonzero lattice translation.
-/

namespace AbelianTargets

open scoped BigOperators
open Fin.NatCast

theorem signedDirection_preimage_of_axis_injective {d : ℕ}
    (s : Fin d → SignedDirection d)
    (hinj : Function.Injective (fun a => (s a).axis)) (δ : SignedDirection d) :
    ∃ e : SignedDirection d,
      (if e.positive then (s e.axis).vector else -(s e.axis).vector) = δ.vector := by
  classical
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective hinj δ.axis
  refine ⟨⟨a, if (s a).positive = δ.positive then true else false⟩, ?_⟩
  cases hs : (s a).positive <;> cases hd : δ.positive <;>
    simp [hs, hd, SignedDirection.vector, ha]

theorem signed_coordinate_step
    {d m : ℕ} {X V : Type*} [AddAction (Lattice d) X]
    {H : SimpleGraph V} (laws : DirectionLaws H m)
    (c : X → V) (s : Fin d → SignedDirection m)
    (hpositive : ∀ a x, H.Adj (c x) (c (unitVector a +ᵥ x)))
    (hdir : ∀ a x, (laws.direction (hpositive a x)).vector = (s a).vector)
    (e : SignedDirection d) (x : X) :
    ∃ h : H.Adj (c x) (c (e.vector +ᵥ x)),
      (laws.direction h).vector =
        if e.positive then (s e.axis).vector else -(s e.axis).vector := by
  cases e with
  | mk a b =>
    cases b with
    | true => exact ⟨hpositive a x, hdir a x⟩
    | false =>
      have hx : unitVector a +ᵥ (-unitVector a +ᵥ x) = x := by
        rw [← add_vadd, add_neg_cancel, zero_vadd]
      have h := (hpositive a (-unitVector a +ᵥ x)).symm
      have he := laws.reverse (hpositive a (-unitVector a +ᵥ x))
      rw [hdir] at he
      rw [hx] at h
      simp only [hx] at he
      exact ⟨h, he⟩

/-- The straight-middle law is the exact equality-of-colors step in
Lemma 7.6; it does not require an additional outgoing-edge uniqueness law. -/
theorem straight_middle_color_transfer
    {d m : ℕ} {X V : Type*} [AddAction (Lattice d) X]
    {H : SimpleGraph V} (laws : DirectionLaws H m)
    (c₀ c₁ : X → V) (g : Lattice d) (δ : SignedDirection m)
    (cross : ∀ x, H.Adj (c₀ x) (c₁ x))
    (hcross : ∀ x, (laws.direction (cross x)).vector = δ.vector)
    (step₀ : ∀ x, H.Adj (c₀ x) (c₀ (g +ᵥ x)))
    (step₁ : ∀ x, H.Adj (c₁ x) (c₁ (g +ᵥ x)))
    (hstep₀ : ∀ x, (laws.direction (step₀ x)).vector = δ.vector)
    (hstep₁ : ∀ x, (laws.direction (step₁ x)).vector = δ.vector) :
    ∀ x, c₁ x = c₀ (g +ᵥ x) := by
  intro x
  apply laws.straight_middle_unique_of_vectors
    (cross x) (step₁ x) (step₀ x) (cross (g +ᵥ x))
  · rw [hcross, hstep₁]
  · rw [hcross, hstep₀]
  · rw [hcross, hcross]

/-- Compose all transfers around a literal finite cycle. -/
theorem cyclic_transfers_translation_invariant
    {r d : ℕ} [NeZero r] {X V : Type*} [AddAction (Lattice d) X]
    (c : Fin r → X → V) (e : Fin r → SignedDirection d)
    (htransfer : ∀ j x, c (j + 1) x = c j ((e j).vector +ᵥ x)) :
    ∀ x, c 0 ((∑ j, (e j).vector : Lattice d) +ᵥ x) = c 0 x := by
  classical
  have hiterate : ∀ n : ℕ, ∀ x,
      c (↑n : Fin r) x = c 0 ((∑ j ∈ Finset.range n, (e (↑j : Fin r)).vector) +ᵥ x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [show (n + 1 : ℕ) = n + 1 from rfl, Nat.cast_add, Nat.cast_one,
        htransfer, ih, ← add_vadd, Finset.sum_range_succ]
  have hsum : (∑ j ∈ Finset.range r, (e (↑j : Fin r)).vector : Lattice d) =
      ∑ j : Fin r, (e j).vector := by
    rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => (e (↑j : Fin r)).vector) r]
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    exact Fin.cast_val_eq_self j
  intro x
  have h := hiterate r x
  rw [Fin.natCast_self, hsum] at h
  exact h.symm

theorem odd_cyclic_transfers_no_proper_freeShift_coloring
    {r d : ℕ} [NeZero r] (hr : Odd r) (hd : 1 ≤ d)
    {V : Type*} [TopologicalSpace V] [DiscreteTopology V] (H : SimpleGraph V)
    (c : Fin r → FreeShift d → V) (hc : Continuous (c 0))
    (e : Fin r → SignedDirection d)
    (htransfer : ∀ j x, c (j + 1) x = c j ((e j).vector +ᵥ x))
    (hproper : ∀ (a : Fin d) x, H.Adj (c 0 x) (c 0 (unitVector a +ᵥ x))) : False := by
  have ht := odd_signedDirection_sum_ne_zero hr e
  have hconstant := freeShift_invariant_nezero_constant hd _ ht (c 0) hc
    (cyclic_transfers_translation_invariant c e htransfer)
  let a : Fin d := ⟨0, hd⟩
  let x : FreeShift d := originFreeConfiguration d
  exact (hproper a x).ne (hconstant x (unitVector a +ᵥ x))

end AbelianTargets
