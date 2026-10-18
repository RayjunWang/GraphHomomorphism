import AbelianTargets.MarkerExistence
import AbelianTargets.OddFiniteSources
import AbelianTargets.PrimeParameters
import AbelianTargets.OddProductObstruction
import AbelianTargets.FiniteCodes

/-!
# Proposition 7.7 and strict decrease of the finite target classes

The marker-window graph is the literal graph of equation (9). The positive
membership is provided by the clopen marker construction. For the negative
membership, the even-dimensional finite source contradicts the checked
axis count, and the odd-dimensional source contradicts Lemma 7.6.

The reference assumptions used by source extraction are named explicitly
in `FiniteSourceReferences` and `References`.
-/

namespace AbelianTargets

open SimpleGraph TwelveTiles

/-- Large distinct odd primes satisfy the exact coprimality hypotheses
used in the two twelve-tile obstructions. -/
theorem exists_admissible_prime_blocks (k N : ℕ) :
    ∃ p q : Fin k → ℕ,
      (∀ i, 5 ≤ p i) ∧ (∀ i, 5 ≤ q i) ∧
      (∀ i, N ≤ p i) ∧ (∀ i, N ≤ q i) ∧
      (∀ i, Odd (p i)) ∧ (∀ i, (p i).Coprime (q i)) ∧
      (∀ i j, i ≠ j → (p i).Coprime (p j)) := by
  classical
  obtain ⟨p,q,hp,hq,hinj⟩ := exists_distinct_odd_prime_blocks k N
  refine ⟨p,q,(fun i => (hp i).2.2.1),(fun i => (hq i).2.2.1),
    (fun i => (hp i).2.2.2),(fun i => (hq i).2.2.2),
    (fun i => (hp i).2.1),?_,?_⟩
  · intro i
    apply (Nat.coprime_primes (hp i).1 (hq i).1).mpr
    intro heq
    have h : (i,(0 : Fin 2)) = (i,(1 : Fin 2)) := hinj (by simpa using heq)
    have : (0 : Fin 2) = 1 := congrArg Prod.snd h
    exact (by decide : (0 : Fin 2) ≠ 1) this
  · intro i j hij
    apply (Nat.coprime_primes (hp i).1 (hp j).1).mpr
    intro heq
    have h : (i,(0 : Fin 2)) = (j,(0 : Fin 2)) := hinj (by simpa using heq)
    exact hij (congrArg Prod.fst h)

/-- The complete requested Proposition 7.7 for every positive dimension
and every marker scale `L ≥ 4`. -/
theorem proposition7_7 : Proposition77Statement := by
  intro d L hd hL
  refine ⟨markerGraph_inClass d L hL, ?_⟩
  intro hnext
  by_cases heven : d % 2 = 0
  · let k := d / 2
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hdk : d = 2 * k := by dsimp [k]; omega
    have hn : InClass (2 * k + 1) (MarkerGraph d L hL) := by
      simpa [hdk] using hnext
    obtain ⟨r,hr,hr₃,N,hsource⟩ := odd_dimension_eventual_finite_sources
      (MarkerGraph d L hL) k hn
    obtain ⟨p,q,hp,hq,hNp,hNq,hodd,hcop,hpair⟩ := exists_admissible_prime_blocks k N
    have hhom := hsource p q hp hq hNp hNq hcop
    have laws : DirectionLaws (MarkerGraph d L hL) (2 * k) :=
      hdk ▸ markerDirectionLaws d L hL
    exact lemma7_6 hk hr hr₃ hp hq hodd hcop hpair laws hhom
  · let k := (d + 1) / 2
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hdk : d + 1 = 2 * k := by dsimp [k]; omega
    have hn : InClass (2 * k) (MarkerGraph d L hL) := by
      simpa [hdk] using hnext
    obtain ⟨N,hsource⟩ := even_dimension_eventual_finite_sources
      (MarkerGraph d L hL) k hk hn
    obtain ⟨p,q,hp,hq,hNp,hNq,hodd,hcop,hpair⟩ := exists_admissible_prime_blocks k N
    obtain ⟨f⟩ := hsource p q hp hq hNp hNq hcop
    have hbound := lemma7_4_dimension_bound (markerDirectionLaws d L hL)
      f hodd hcop hpair
    omega

/-- The classes of finite continuous targets strictly decrease as the
positive dimension increases. -/
theorem finiteGraphClasses_strictDecrease :
    ∀ d : ℕ, 1 ≤ d → finiteGraphClass (d + 1) ⊂ finiteGraphClass d :=
  strictDecrease_of_proposition7_7 proposition7_7

end AbelianTargets
