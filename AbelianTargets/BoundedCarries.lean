import AbelianTargets.CompressedWords
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

/-!
# Bounded cellular moves on compressed words

The relation records actual presentation-cell moves and backtrack
cancellations in word contexts. Its length index bounds every word in
the finite sequence. This is stronger than equality after evaluation in
the Baumslag--Solitar group.
-/

namespace AbelianTargets

def aWord (n : ℕ) : List BSLetter := List.replicate n BSLetter.a
def conjugateWord (w : List BSLetter) : List BSLetter := [BSLetter.t] ++ w ++ [BSLetter.tInv]

inductive BSCellMove (m : ℕ) : List BSLetter → List BSLetter → Prop
  | relation : BSCellMove m [BSLetter.t,BSLetter.a,BSLetter.tInv] (aWord m)
  | cancelDownUp : BSCellMove m [BSLetter.tInv,BSLetter.t] []
  | cancelUpDown : BSCellMove m [BSLetter.t,BSLetter.tInv] []
  | symm {w z} : BSCellMove m w z → BSCellMove m z w

inductive BoundedBSHomotopic (m B : ℕ) : List BSLetter → List BSLetter → Prop
  | refl (w) (hlen : w.length ≤ B) : BoundedBSHomotopic m B w w
  | cell {w z} (h : BSCellMove m w z) (p s : List BSLetter)
      (hw : (p++w++s).length ≤ B) (hz : (p++z++s).length ≤ B) :
      BoundedBSHomotopic m B (p++w++s) (p++z++s)
  | symm {w z} : BoundedBSHomotopic m B w z → BoundedBSHomotopic m B z w
  | trans {u v w} : BoundedBSHomotopic m B u v → BoundedBSHomotopic m B v w →
      BoundedBSHomotopic m B u w

theorem BoundedBSHomotopic.mono {m B C : ℕ} {w z : List BSLetter}
    (h : BoundedBSHomotopic m B w z) (hBC : B ≤ C) : BoundedBSHomotopic m C w z := by
  induction h with
  | refl w hw => exact .refl w (hw.trans hBC)
  | cell h p s hw hz => exact .cell h p s (hw.trans hBC) (hz.trans hBC)
  | symm h ih => exact .symm ih
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem BoundedBSHomotopic.context {m B : ℕ} {w z : List BSLetter}
    (h : BoundedBSHomotopic m B w z) (p s : List BSLetter) :
    BoundedBSHomotopic m (B+p.length+s.length) (p++w++s) (p++z++s) := by
  induction h with
  | refl w hw =>
      apply BoundedBSHomotopic.refl
      simp only [List.length_append]
      omega
  | @cell w₀ z₀ h p₀ s₀ hw hz =>
      have hw' : ((p++p₀)++w₀++(s₀++s)).length ≤ B+p.length+s.length := by
        simp only [List.length_append] at hw ⊢
        omega
      have hz' : ((p++p₀)++z₀++(s₀++s)).length ≤ B+p.length+s.length := by
        simp only [List.length_append] at hz ⊢
        omega
      simpa only [List.append_assoc] using BoundedBSHomotopic.cell h (p++p₀) (s₀++s) hw' hz'
  | symm h ih => exact .symm ih
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem BoundedBSHomotopic.of_eq {m B : ℕ} {w z : List BSLetter}
    (heq : w = z) (hw : w.length ≤ B) : BoundedBSHomotopic m B w z := by
  subst z
  exact .refl _ hw

theorem BoundedBSHomotopic.bounds {m B : ℕ} {w z : List BSLetter}
    (h : BoundedBSHomotopic m B w z) : w.length ≤ B ∧ z.length ≤ B := by
  induction h with
  | refl w hw => exact ⟨hw,hw⟩
  | cell h p s hw hz => exact ⟨hw,hz⟩
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ⟨ih₁.1,ih₂.2⟩

theorem BSCellMove.value_eq {G : Type*} [Group G] {m : ℕ}
    (a t : G) (hrel : t*a*t⁻¹ = a^m) {w z : List BSLetter}
    (h : BSCellMove m w z) : bsWordValue a t w = bsWordValue a t z := by
  induction h with
  | relation => simpa [aWord, BSLetter.value, mul_assoc] using hrel
  | cancelDownUp => simp [BSLetter.value]
  | cancelUpDown => simp [BSLetter.value]
  | symm h ih => exact ih.symm

theorem BoundedBSHomotopic.value_eq {G : Type*} [Group G] {m B : ℕ}
    (a t : G) (hrel : t*a*t⁻¹ = a^m) {w z : List BSLetter}
    (h : BoundedBSHomotopic m B w z) : bsWordValue a t w = bsWordValue a t z := by
  induction h with
  | refl w hw => rfl
  | cell h p s hw hz => simp only [bsWordValue_append, h.value_eq a t hrel]
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem compressedWord_conjugate (m : ℕ) (hm : 2 ≤ m) {n : ℕ} (hn : m ≤ n) :
    compressedWord m hm n = conjugateWord (compressedWord m hm (n/m)) ++ aWord (n%m) := by
  rw [compressedWord_of_ge m hm hn]
  simp only [conjugateWord, aWord, List.cons_append, List.nil_append, List.append_assoc]

theorem aWord_succ (n : ℕ) : aWord (n+1) = aWord n ++ [BSLetter.a] := by
  simp only [aWord, List.replicate_add, List.replicate_one]

def carryLengthBound (m n : ℕ) : ℕ := (m+1)*(Nat.log m (n+1)+1)+m+3

theorem compressedWord_append_a_length_le (m : ℕ) (hm : 2 ≤ m) (n : ℕ) :
    (compressedWord m hm n ++ [BSLetter.a]).length ≤ carryLengthBound m n := by
  have hlen := compressedWord_interval_uniform_length m hm (n+1) n (by omega)
  simp only [List.length_append, List.length_cons, List.length_nil]
  dsimp [carryLengthBound]
  omega

theorem quotient_remainder_succ_no_carry {m n : ℕ} (hm : 2 ≤ m) (hr : n%m+1 < m) :
    (n+1)/m = n/m ∧ (n+1)%m = n%m+1 := by
  have hnum : n+1 = m*(n/m)+(n%m+1) := by
    have := Nat.mod_add_div n m
    omega
  rw [hnum, Nat.mul_add_div (by omega), Nat.mul_add_mod,
    Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr]
  simp

theorem quotient_remainder_succ_carry {m n : ℕ} (hm : 2 ≤ m) (hr : n%m+1 = m) :
    n+1 = m*(n/m+1) ∧ (n+1)/m = n/m+1 ∧ (n+1)%m = 0 := by
  have hnum : n+1 = m*(n/m+1) := by
    rw [Nat.mul_add, Nat.mul_one]
    have := Nat.mod_add_div n m
    omega
  refine ⟨hnum, ?_, ?_⟩
  · rw [hnum, Nat.mul_div_cancel_left _ (show 0 < m by omega)]
  · rw [hnum, Nat.mul_mod_right]

/-- Base-m carrying is a finite sequence of actual presentation-cell
and backtrack moves, with a uniform logarithmic bound on every
intermediate edge word. -/
theorem compressedWord_bounded_carry (m : ℕ) (hm : 2 ≤ m) (n : ℕ) :
    BoundedBSHomotopic m (carryLengthBound m n)
      (compressedWord m hm n ++ [BSLetter.a]) (compressedWord m hm (n+1)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hlen := compressedWord_append_a_length_le m hm n
    by_cases hn : n < m
    · by_cases hn' : n+1 < m
      · apply BoundedBSHomotopic.of_eq _ hlen
        rw [compressedWord_of_lt m hm hn, compressedWord_of_lt m hm hn']
        exact (aWord_succ n).symm
      · have hnm : n+1 = m := by omega
        have hleft : compressedWord m hm n ++ [BSLetter.a] = aWord m := by
          rw [compressedWord_of_lt m hm hn]
          change aWord n ++ [BSLetter.a] = aWord m
          rw [← aWord_succ n, hnm]
        have hright : compressedWord m hm (n+1) = [BSLetter.t,BSLetter.a,BSLetter.tInv] := by
          rw [hnm, compressedWord_conjugate m hm le_rfl]
          rw [Nat.div_self (by omega), Nat.mod_self, compressedWord_of_lt m hm (show 1 < m by omega)]
          simp [conjugateWord, aWord]
        rw [hleft,hright]
        simpa using BoundedBSHomotopic.cell (B := carryLengthBound m n)
          (BSCellMove.symm (BSCellMove.relation (m := m))) [] []
          (by simpa [hleft] using hlen)
          (by simp only [List.nil_append, List.append_nil, List.length_cons, List.length_nil];
              dsimp [carryLengthBound]; omega)
    · by_cases hrem : n%m+1 < m
      · obtain ⟨hquot,hmod⟩ := quotient_remainder_succ_no_carry hm hrem
        apply BoundedBSHomotopic.of_eq _ hlen
        rw [compressedWord_conjugate m hm (n := n) (by omega),
          compressedWord_conjugate m hm (n := n+1) (by omega), hquot,hmod,
          aWord_succ]
        simp only [List.append_assoc]
      · have hrem' : n%m+1 = m := by
          have := Nat.mod_lt n (show 0 < m by omega)
          omega
        obtain ⟨hnum,hquot,hmod⟩ := quotient_remainder_succ_carry hm hrem'
        let q := n/m
        let w := compressedWord m hm q
        let B := carryLengthBound m n
        let C := (m+1)*(Nat.log m (q+1)+1)
        have hq : q < n := Nat.div_lt_self (by omega) (by omega)
        have hw : w.length ≤ C := compressedWord_interval_uniform_length m hm (q+1) q (by omega)
        have hlog : Nat.log m (n+1) = Nat.log m (q+1)+1 := by
          rw [hnum, Nat.mul_comm]
          exact Nat.log_mul_base (b := m) (n := q+1) (by omega) (Nat.succ_ne_zero q)
        have hB : B = C+(m+1)+m+3 := by
          dsimp [B, C, carryLengthBound]
          rw [hlog]
          ring
        have hleft : compressedWord m hm n ++ [BSLetter.a] = conjugateWord w ++ aWord m := by
          rw [compressedWord_conjugate m hm (by omega), List.append_assoc, ← aWord_succ, hrem']
        have hright : compressedWord m hm (n+1) = conjugateWord (compressedWord m hm (q+1)) := by
          rw [compressedWord_conjugate m hm (by omega), hquot,hmod]
          simp only [aWord, List.replicate_zero, List.append_nil]
          rfl
        rw [hleft,hright]
        let expanded := [BSLetter.t] ++ w ++ [BSLetter.tInv,BSLetter.t,BSLetter.a,BSLetter.tInv]
        have h₁ : BoundedBSHomotopic m B (conjugateWord w ++ aWord m) expanded := by
          have h := BoundedBSHomotopic.cell (B := B) (BSCellMove.symm (BSCellMove.relation (m := m)))
            ([BSLetter.t]++w++[BSLetter.tInv]) []
            (by simp only [List.length_append, List.length_cons, List.length_nil, aWord, List.length_replicate];
                rw [hB]; omega)
            (by simp only [List.length_append, List.length_cons, List.length_nil]; rw [hB]; omega)
          simpa only [conjugateWord, expanded, List.append_assoc, List.append_nil, List.cons_append,
            List.nil_append] using h
        have h₂ : BoundedBSHomotopic m B expanded (conjugateWord (w++[BSLetter.a])) := by
          have h := BoundedBSHomotopic.cell (B := B) (BSCellMove.cancelDownUp (m := m))
            ([BSLetter.t]++w) [BSLetter.a,BSLetter.tInv]
            (by simp only [List.length_append, List.length_cons, List.length_nil]; rw [hB]; omega)
            (by simp only [List.length_append, List.length_cons, List.length_nil]; rw [hB]; omega)
          simpa only [conjugateWord, expanded, List.append_assoc, List.cons_append, List.nil_append] using h
        have h₃ : BoundedBSHomotopic m B (conjugateWord (w++[BSLetter.a]))
            (conjugateWord (compressedWord m hm (q+1))) := by
          have h := (ih q hq).context [BSLetter.t] [BSLetter.tInv]
          have hbound : carryLengthBound m q+[BSLetter.t].length+[BSLetter.tInv].length ≤ B := by
            simp only [List.length_cons, List.length_nil]
            dsimp [carryLengthBound]
            change C+m+3+1+1 ≤ B
            rw [hB]
            omega
          exact h.mono hbound
        exact h₁.trans (h₂.trans h₃)

/-- One length budget works for all carries in a finite horizontal interval. -/
theorem compressedWord_interval_bounded_carry (m : ℕ) (hm : 2 ≤ m)
    (R n : ℕ) (hn : n < R) :
    BoundedBSHomotopic m ((m+1)*(Nat.log m R+1)+m+3)
      (compressedWord m hm n ++ [BSLetter.a]) (compressedWord m hm (n+1)) := by
  apply (compressedWord_bounded_carry m hm n).mono
  have hlog := Nat.log_mono_right (b := m) (show n+1 ≤ R by omega)
  dsimp [carryLengthBound]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1)) m) 3

end AbelianTargets
