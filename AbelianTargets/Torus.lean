import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Coprime torus collapse

This file proves the torus contradiction in Lemma 7.4 of
arXiv:2609.39824v1. The Chinese remainder theorem makes translation
by `(1,-1)` transitive on `ZMod p × ZMod q` for positive coprime
`p,q`. Equality of the two middle vertices therefore forces the
map to be constant, which is incompatible with a graph edge in a
loopless target. Both signs of the vertical direction are handled.

This is a complete local obstruction. It does not construct or
prove rigidity of the twelve-tile graphs surrounding this step.
-/

namespace AbelianTargets

/-- The orbit of zero under translation by `(1,-1)` reaches every point
of a torus with positive coprime side lengths. -/
theorem coprime_torus_translation_reaches {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hcop : p.Coprime q)
    (i : ZMod p) (j : ZMod q) :
    ∃ n : ℕ, (n : ZMod p) = i ∧ -(n : ZMod q) = j := by
  letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  obtain ⟨n, hnp, hnq⟩ := Nat.chineseRemainder hcop i.val (-j).val
  have hpi : (n : ZMod p) = i := by
    calc
      (n : ZMod p) = (i.val : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hnp
      _ = i := ZMod.natCast_zmod_val i
  have hqj : (n : ZMod q) = -j := by
    calc
      (n : ZMod q) = ((-j).val : ZMod q) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hnq
      _ = -j := ZMod.natCast_zmod_val (-j)
  exact ⟨n, hpi, by rw [hqj, neg_neg]⟩

/-- Invariance under the diagonal translation forces constancy on the
whole coprime torus. No continuity or finiteness assumption on the
value type is needed for this finite orbit argument. -/
theorem coprime_torus_invariant_constant {p q : ℕ} {V : Type*}
    (hp : 0 < p) (hq : 0 < q) (hcop : p.Coprime q)
    (f : ZMod p × ZMod q → V)
    (hinv : ∀ (i : ZMod p) (j : ZMod q), f (i + 1, j - 1) = f (i, j)) :
    ∀ z, f z = f (0, 0) := by
  have hiter : ∀ n : ℕ, f ((n : ZMod p), -(n : ZMod q)) = f (0, 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        f ((n + 1 : ℕ), -(n + 1 : ℕ)) =
            f ((n : ZMod p), -(n : ZMod q)) := by
          simpa only [Nat.cast_add, Nat.cast_one, neg_add, sub_eq_add_neg]
            using hinv (n : ZMod p) (-(n : ZMod q))
        _ = f (0, 0) := ih
  rintro ⟨i, j⟩
  obtain ⟨n, hni, hnj⟩ := coprime_torus_translation_reaches hp hq hcop i j
  simpa only [hni, hnj] using hiter n

/-- The two straight routes have the same middle vertex only when the
color map is constant on a torus with coprime side lengths. -/
theorem coprime_torus_diagonal_constant {p q : ℕ} {V : Type*}
    (hp : 0 < p) (hq : 0 < q) (hcop : p.Coprime q)
    (f : ZMod p × ZMod q → V)
    (hdiag : ∀ (i : ZMod p) (j : ZMod q), f (i + 1, j) = f (i, j + 1)) :
    ∀ z, f z = f (0, 0) := by
  apply coprime_torus_invariant_constant hp hq hcop f
  intro i j
  simpa only [sub_add_cancel] using hdiag i (j - 1)

/-- The torus-collapse conclusion also holds when the two coordinate
directions use opposite signs on their common target axis. -/
theorem coprime_torus_signedDiagonal_constant {p q : ℕ} {V : Type*}
    (hp : 0 < p) (hq : 0 < q) (hcop : p.Coprime q)
    (f : ZMod p × ZMod q → V) (ε : ZMod q)
    (hε : ε = 1 ∨ ε = -1)
    (hdiag : ∀ (i : ZMod p) (j : ZMod q), f (i + 1, j) = f (i, j + ε)) :
    ∀ z, f z = f (0, 0) := by
  rcases hε with rfl | rfl
  · exact coprime_torus_diagonal_constant hp hq hcop f hdiag
  · let F : ZMod p × ZMod q → V := fun z => f (z.1, -z.2)
    have hF : ∀ (i : ZMod p) (j : ZMod q), F (i + 1, j) = F (i, j + 1) := by
      intro i j
      simpa only [F, neg_add] using hdiag i (-j)
    have hconstant := coprime_torus_diagonal_constant hp hq hcop F hF
    rintro ⟨i, j⟩
    simpa only [F, neg_neg, neg_zero] using hconstant (i, -j)

/-- A collapsed torus map cannot take even one pair of source vertices
to an edge of a simple graph, since a simple graph has no loops. -/
theorem coprime_torus_signedDiagonal_no_edge {p q : ℕ} {V : Type*}
    (hp : 0 < p) (hq : 0 < q) (hcop : p.Coprime q)
    (H : SimpleGraph V) (f : ZMod p × ZMod q → V) (ε : ZMod q)
    (hε : ε = 1 ∨ ε = -1)
    (hdiag : ∀ (i : ZMod p) (j : ZMod q), f (i + 1, j) = f (i, j + ε))
    (x y : ZMod p × ZMod q) : ¬ H.Adj (f x) (f y) := by
  have hconstant := coprime_torus_signedDiagonal_constant hp hq hcop f ε hε hdiag
  rw [hconstant x, hconstant y]
  exact H.irrefl

/-- Consequently a map satisfying the collapsed-axis relation cannot
preserve a horizontal standard edge into a loopless graph. -/
theorem coprime_torus_no_collapsed_horizontal_edge {p q : ℕ} {V : Type*}
    (hp : 0 < p) (hq : 0 < q) (hcop : p.Coprime q)
    (H : SimpleGraph V) (f : ZMod p × ZMod q → V) (ε : ZMod q)
    (hε : ε = 1 ∨ ε = -1)
    (hdiag : ∀ (i : ZMod p) (j : ZMod q), f (i + 1, j) = f (i, j + ε))
    (hedge : ∃ (i : ZMod p) (j : ZMod q), H.Adj (f (i, j)) (f (i + 1, j))) :
    False := by
  obtain ⟨i, j, hij⟩ := hedge
  exact coprime_torus_signedDiagonal_no_edge hp hq hcop H f ε hε hdiag
    (i, j) (i + 1, j) hij

end AbelianTargets
