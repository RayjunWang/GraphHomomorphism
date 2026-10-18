import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# Base-m compressed Baumslag--Solitar words

The words here are the actual recursive digit words used in Sections 4
and 7: `pₙ = t p_(n/m) t⁻¹ a^(n % m)`, with the bottom-digit case
`pₙ = aⁿ`. Their group value and explicit logarithmic edge-length bound
are proved from the single Baumslag--Solitar relation.
-/

namespace AbelianTargets

inductive BSLetter where
  | a | t | tInv
  deriving DecidableEq, Repr

def BSLetter.value {G : Type*} [Group G] (a t : G) : BSLetter → G
  | .a => a
  | .t => t
  | .tInv => t⁻¹

def bsWordValue {G : Type*} [Group G] (a t : G) (w : List BSLetter) : G :=
  (w.map (BSLetter.value a t)).prod

@[simp] theorem bsWordValue_nil {G : Type*} [Group G] (a t : G) :
    bsWordValue a t [] = 1 := rfl

@[simp] theorem bsWordValue_cons {G : Type*} [Group G] (a t : G) (s : BSLetter) (w : List BSLetter) :
    bsWordValue a t (s :: w) = s.value a t * bsWordValue a t w := rfl

@[simp] theorem bsWordValue_append {G : Type*} [Group G] (a t : G) (w z : List BSLetter) :
    bsWordValue a t (w ++ z) = bsWordValue a t w * bsWordValue a t z := by
  simp [bsWordValue]

@[simp] theorem bsWordValue_replicate_a {G : Type*} [Group G] (a t : G) (n : ℕ) :
    bsWordValue a t (List.replicate n BSLetter.a) = a ^ n := by
  simp [bsWordValue, BSLetter.value]

def compressedWord (m : ℕ) (hm : 2 ≤ m) (n : ℕ) : List BSLetter :=
  if _h : n < m then List.replicate n BSLetter.a
  else BSLetter.t :: (compressedWord m hm (n / m) ++
    BSLetter.tInv :: List.replicate (n % m) BSLetter.a)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

@[simp] theorem compressedWord_zero (m : ℕ) (hm : 2 ≤ m) :
    compressedWord m hm 0 = [] := by
  rw [compressedWord]
  simp only [show 0 < m by omega, dif_pos, List.replicate_zero]

theorem compressedWord_of_lt (m : ℕ) (hm : 2 ≤ m) {n : ℕ} (hn : n < m) :
    compressedWord m hm n = List.replicate n BSLetter.a := by
  rw [compressedWord, dif_pos hn]

theorem compressedWord_of_ge (m : ℕ) (hm : 2 ≤ m) {n : ℕ} (hn : m ≤ n) :
    compressedWord m hm n = BSLetter.t :: (compressedWord m hm (n / m) ++
      BSLetter.tInv :: List.replicate (n % m) BSLetter.a) := by
  rw [compressedWord, dif_neg (by omega)]

theorem bs_conjugate_power {G : Type*} [Group G] {m : ℕ}
    (a t : G) (hrel : t * a * t⁻¹ = a ^ m) (q : ℕ) :
    t * a ^ q * t⁻¹ = a ^ (m * q) := by
  rw [← conj_pow, hrel, pow_mul]

/-- The literal compressed word runs to the bottom vertex `aⁿ` in every
group satisfying the displayed presentation relation. -/
theorem compressedWord_value {G : Type*} [Group G] (m : ℕ) (hm : 2 ≤ m)
    (a t : G) (hrel : t * a * t⁻¹ = a ^ m) (n : ℕ) :
    bsWordValue a t (compressedWord m hm n) = a ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < m
      · rw [compressedWord_of_lt m hm hn, bsWordValue_replicate_a]
      · rw [compressedWord_of_ge m hm (by omega)]
        rw [bsWordValue_cons, bsWordValue_append, bsWordValue_cons,
          bsWordValue_replicate_a, ih (n/m) (Nat.div_lt_self (by omega) (by omega))]
        simp only [BSLetter.value]
        calc
          t * (a ^ (n / m) * (t⁻¹ * a ^ (n % m))) =
              (t * a ^ (n/m) * t⁻¹) * a ^ (n%m) := by simp only [mul_assoc]
          _ = a ^ (m * (n/m)) * a ^ (n%m) := by rw [bs_conjugate_power a t hrel]
          _ = a ^ n := by
            rw [← pow_add]
            congr 1
            simpa only [Nat.add_comm] using Nat.mod_add_div n m

/-- A concrete version of the paper's `Oₘ(log(n+1))` edge bound. -/
theorem compressedWord_length_le (m : ℕ) (hm : 2 ≤ m) (n : ℕ) :
    (compressedWord m hm n).length ≤ (m + 1) * (Nat.log m n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < m
      · rw [compressedWord_of_lt m hm hn, List.length_replicate]
        calc
          n ≤ m + 1 := by omega
          _ = (m + 1) * 1 := by simp
          _ ≤ (m + 1) * (Nat.log m n + 1) :=
            Nat.mul_le_mul_left _ (by omega)
      · rw [compressedWord_of_ge m hm (by omega)]
        simp only [List.length_cons, List.length_append, List.length_replicate]
        have hq := ih (n/m) (Nat.div_lt_self (by omega) (by omega))
        have hlog : 1 ≤ Nat.log m n := by
          apply Nat.le_log_of_pow_le (by omega)
          simpa only [Nat.pow_one] using (show m ≤ n by omega)
        have hlogq : Nat.log m (n/m) + 1 = Nat.log m n := by
          rw [Nat.log_div_base]
          omega
        rw [hlogq] at hq
        have hmod := Nat.mod_lt n (show 0 < m by omega)
        rw [Nat.mul_add, Nat.mul_one]
        omega

theorem compressedWord_interval_uniform_length (m : ℕ) (hm : 2 ≤ m) (R n : ℕ)
    (hn : n ≤ R) :
    (compressedWord m hm n).length ≤ (m + 1) * (Nat.log m R + 1) :=
  (compressedWord_length_le m hm n).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.log_mono_right hn) 1))

/-- Equality of the two sides of a carry, derived from actual compressed
word evaluation rather than assumed as a carrier axiom. -/
theorem compressedWord_carry_value {G : Type*} [Group G] (m : ℕ) (hm : 2 ≤ m)
    (a t : G) (hrel : t * a * t⁻¹ = a ^ m) (n : ℕ) :
    bsWordValue a t (compressedWord m hm n ++ [BSLetter.a]) =
      bsWordValue a t (compressedWord m hm (n + 1)) := by
  simp [compressedWord_value m hm a t hrel, BSLetter.value, pow_succ]

end AbelianTargets
