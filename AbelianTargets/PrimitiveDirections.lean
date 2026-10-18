import AbelianTargets.DirectionSaturation
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

/-!
# Coprime odd cycle totals determine one signed direction

The boundary relations in Lemma 7.4 imply integer divisibility by Bézout.
The `ℓ¹` bound and oddness force the common primitive vector to be a signed
unit vector. The previously proved saturation lemma then applies.
-/

namespace AbelianTargets

open scoped BigOperators

theorem SignedDirection.sum_abs_coordinates {m : ℕ} (s : SignedDirection m) :
    (∑ i, |s.vector i| : ℤ) = 1 := by
  cases s with
  | mk axis positive =>
    cases positive <;> simp [SignedDirection.vector, unitVector, apply_ite]

theorem signedDirection_sum_l1_bound {n m : ℕ} (s : Fin n → SignedDirection m) :
    (∑ i, |(∑ j, (s j).vector : Lattice m) i| : ℤ) ≤ n := by
  simp only [Finset.sum_apply]
  calc
    (∑ i, |∑ j, (s j).vector i| : ℤ) ≤ ∑ i, ∑ j, |(s j).vector i| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ j, ∑ i, |(s j).vector i| := Finset.sum_comm
    _ = n := by simp [SignedDirection.sum_abs_coordinates]

theorem signedDirection_of_small_l1 {m : ℕ} (u : Lattice m) (hu : u ≠ 0)
    (hbound : (∑ i, |u i| : ℤ) ≤ 1) : ∃ s : SignedDirection m, u = s.vector := by
  classical
  have haxis : ∃ a, u a ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  obtain ⟨a, ha⟩ := haxis
  have hsingle : |u a| ≤ ∑ i, |u i| :=
    Finset.single_le_sum (fun i _ => abs_nonneg (u i)) (Finset.mem_univ a)
  have habs : |u a| = 1 := by
    have hpos : 0 < |u a| := abs_pos.mpr ha
    omega
  have he : (∑ j ∈ Finset.univ.erase a, |u j| : ℤ) + |u a| = ∑ j, |u j| :=
    Finset.sum_erase_add _ _ (Finset.mem_univ a)
  have henonneg : (0 : ℤ) ≤ ∑ j ∈ Finset.univ.erase a, |u j| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg (u j))
  have hezero : (∑ j ∈ Finset.univ.erase a, |u j| : ℤ) = 0 := by omega
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_hj : j ∈ Finset.univ.erase a) => abs_nonneg (u j))).mp hezero
  have hother : ∀ j, j ≠ a → u j = 0 := by
    intro j hja
    exact abs_eq_zero.mp (hz j (Finset.mem_erase.mpr ⟨hja, Finset.mem_univ j⟩))
  have hsign : u a = 1 ∨ u a = -1 := by
    have hle := abs_le.mp (le_of_eq habs)
    omega
  rcases hsign with hsign | hsign
  · refine ⟨⟨a, true⟩, ?_⟩
    funext j
    by_cases hja : j = a
    · subst j
      simp [SignedDirection.vector, unitVector, hsign]
    · simp [SignedDirection.vector, unitVector, hja, hother j hja]
  · refine ⟨⟨a, false⟩, ?_⟩
    funext j
    by_cases hja : j = a
    · subst j
      simp [SignedDirection.vector, unitVector, hsign]
    · simp [SignedDirection.vector, unitVector, hja, hother j hja]

/-- Bézout gives a common integer vector for two coprime proportional
boundary totals. This statement does not impose a norm or parity condition. -/
theorem coprime_vector_totals {p q m : ℕ} (hc : p.Coprime q)
    (A B : Lattice m) (hrel : q • A = p • B) :
    ∃ u : Lattice m, A = p • u ∧ B = q • u := by
  let r : ℤ := Nat.gcdA p q
  let s : ℤ := Nat.gcdB p q
  have hbez : (p : ℤ) * r + (q : ℤ) * s = 1 := by
    simpa [r, s, hc.gcd_eq_one] using (Nat.gcd_eq_gcd_ab p q).symm
  let u : Lattice m := fun i => r * A i + s * B i
  refine ⟨u, ?_, ?_⟩
  · funext i
    have hi := congrFun hrel i
    simp only [Pi.smul_apply, Int.nsmul_eq_mul] at hi
    change A i = (p : ℤ) * (r * A i + s * B i)
    calc
      A i = ((p : ℤ) * r + (q : ℤ) * s) * A i := by rw [hbez, one_mul]
      _ = (p : ℤ) * r * A i + s * ((q : ℤ) * A i) := by ring
      _ = (p : ℤ) * r * A i + s * ((p : ℤ) * B i) := by rw [hi]
      _ = (p : ℤ) * (r * A i + s * B i) := by ring
  · funext i
    have hi := congrFun hrel i
    simp only [Pi.smul_apply, Int.nsmul_eq_mul] at hi
    change B i = (q : ℤ) * (r * A i + s * B i)
    calc
      B i = ((p : ℤ) * r + (q : ℤ) * s) * B i := by rw [hbez, one_mul]
      _ = r * ((p : ℤ) * B i) + (q : ℤ) * s * B i := by ring
      _ = r * ((q : ℤ) * A i) + (q : ℤ) * s * B i := by rw [hi]
      _ = (q : ℤ) * (r * A i + s * B i) := by ring

/-- The exact coprime-period arithmetic step used in Lemma 7.4. -/
theorem signedDirection_coprime_periods {p q m : ℕ}
    (hp : Odd p) (hc : p.Coprime q)
    (a : Fin p → SignedDirection m) (b : Fin q → SignedDirection m)
    (hrel : q • (∑ j, (a j).vector : Lattice m) =
      p • (∑ j, (b j).vector : Lattice m)) :
    ∃ u : SignedDirection m,
      (∑ j, (a j).vector : Lattice m) = p • u.vector ∧
      (∑ j, (b j).vector : Lattice m) = q • u.vector := by
  obtain ⟨u, hA, hB⟩ := coprime_vector_totals hc _ _ hrel
  have hu : u ≠ 0 := by
    intro h
    apply odd_signedDirection_sum_ne_zero hp a
    simpa [h] using hA
  have hp0 : (0 : ℤ) < p := by
    obtain ⟨k, hk⟩ := hp
    omega
  have hn : (p : ℤ) * (∑ i, |u i| : ℤ) ≤ p := by
    have hh := signedDirection_sum_l1_bound a
    rw [hA] at hh
    simpa only [Pi.smul_apply, Int.nsmul_eq_mul, abs_mul,
      abs_of_pos hp0, Finset.mul_sum] using hh
  have hbound : (∑ i, |u i| : ℤ) ≤ 1 := by
    exact le_of_mul_le_mul_left (by simpa only [mul_one] using hn) hp0
  obtain ⟨s, hs⟩ := signedDirection_of_small_l1 u hu hbound
  exact ⟨s, hs ▸ hA, hs ▸ hB⟩

end AbelianTargets
