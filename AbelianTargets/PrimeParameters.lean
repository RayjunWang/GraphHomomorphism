import AbelianTargets.EvenFiniteSources
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Basic

/-!
# Distinct odd prime parameters above any finite-source threshold

Euclid's theorem supplies arbitrarily large primes; finite induction
chooses an injective family. This closes the elementary parameter-choice
step in Lemma 7.5.
-/

namespace AbelianTargets

theorem exists_injective_prime_family (n N : ℕ) :
    ∃ p : Fin n → ℕ, Function.Injective p ∧ ∀ i, Nat.Prime (p i) ∧ N ≤ p i := by
  classical
  induction n with
  | zero => exact ⟨Fin.elim0, (fun a => a.elim0), (fun i => i.elim0)⟩
  | succ n ih =>
      obtain ⟨p, hinj, hp⟩ := ih
      obtain ⟨q, hqN, hqprime⟩ := Nat.exists_infinite_primes (max N (Finset.univ.sup p + 1))
      have hq : ∀ i, p i < q := by
        intro i
        have hi : p i ≤ Finset.univ.sup p := Finset.le_sup (Finset.mem_univ i)
        have := le_max_right N (Finset.univ.sup p + 1)
        omega
      refine ⟨Fin.cases q p, ?_, ?_⟩
      · intro a
        refine Fin.cases ?_ (fun a => ?_) a
        · intro b
          refine Fin.cases ?_ (fun b => ?_) b
          · intro _; rfl
          · intro hab
            have h : q = p b := hab
            exact False.elim (by have := hq b; omega)
        · intro b
          refine Fin.cases ?_ (fun b => ?_) b
          · intro hab
            have h : p a = q := hab
            exact False.elim (by have := hq a; omega)
          · intro hab
            exact congrArg Fin.succ (hinj hab)
      · intro i
        refine Fin.cases ?_ (fun i => hp i) i
        exact ⟨hqprime, (le_max_left N _).trans hqN⟩

theorem exists_distinct_odd_prime_blocks (k N : ℕ) :
    ∃ p q : Fin k → ℕ,
      (∀ i, Nat.Prime (p i) ∧ Odd (p i) ∧ 5 ≤ p i ∧ N ≤ p i) ∧
      (∀ i, Nat.Prime (q i) ∧ Odd (q i) ∧ 5 ≤ q i ∧ N ≤ q i) ∧
      Function.Injective (fun a : Fin k × Fin 2 => if a.2 = 0 then p a.1 else q a.1) := by
  classical
  obtain ⟨f, hf, hprime⟩ := exists_injective_prime_family (2 * k) (max N 5)
  let p := fun i => f (blockIndex k (i, 0))
  let q := fun i => f (blockIndex k (i, 1))
  have hprops : ∀ j, Nat.Prime (f j) ∧ Odd (f j) ∧ 5 ≤ f j ∧ N ≤ f j := by
    intro j
    obtain ⟨hp, hN⟩ := hprime j
    have h5 := (le_max_right N 5).trans hN
    exact ⟨hp, hp.odd_of_ne_two (by omega), h5, (le_max_left N 5).trans hN⟩
  refine ⟨p, q, (fun i => hprops _), (fun i => hprops _), ?_⟩
  have heq : (fun a : Fin k × Fin 2 => if a.2 = 0 then p a.1 else q a.1) =
      fun a => f (blockIndex k a) := by
    funext ⟨i,j⟩
    have hj : j = 0 ∨ j = 1 := by
      have := j.isLt
      have : j.val = 0 ∨ j.val = 1 := by omega
      exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
    obtain hj | hj := hj
    · subst j; simp [p]
    · subst j; simp [q]
  rw [heq]
  exact hf.comp (blockIndex k).injective

theorem prime_block_coprime_conditions {k : ℕ}
    (p q : Fin k → ℕ) (hp : ∀ i, Nat.Prime (p i)) (hq : ∀ i, Nat.Prime (q i))
    (hinj : Function.Injective (fun a : Fin k × Fin 2 => if a.2 = 0 then p a.1 else q a.1)) :
    (∀ i, (p i).Coprime (q i)) ∧ (∀ i j, i ≠ j → (p i).Coprime (p j)) := by
  constructor
  · intro i
    apply (Nat.coprime_primes (hp i) (hq i)).mpr
    intro heq
    have hpair : (i, (0 : Fin 2)) = (i, (1 : Fin 2)) := hinj (by simpa using heq)
    have hval := congrArg (fun a : Fin k × Fin 2 => a.2.val) hpair
    norm_num at hval
  · intro i j hij
    apply (Nat.coprime_primes (hp i) (hp j)).mpr
    intro heq
    have hpair : (i, (0 : Fin 2)) = (j, (0 : Fin 2)) := hinj (by simpa using heq)
    exact hij (congrArg Prod.fst hpair)

end AbelianTargets
