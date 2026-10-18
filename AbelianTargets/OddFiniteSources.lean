import AbelianTargets.OddCycleSources

/-!
# Odd-dimensional finite source extraction

The compact product supplies a one-dimensional finite factor and
two-dimensional finite factors. Substitute an actual odd cycle into the
first factor and the verified GJKS sources into all the remaining factors.
This proves the finite-source implication needed in Lemmas 7.5 and 7.6.
-/

namespace AbelianTargets

open SimpleGraph

theorem odd_dimension_eventual_finite_sources
    {V : Type*} [TopologicalSpace V] [Fintype V] [DiscreteTopology V]
    (H : SimpleGraph V) (k : ℕ) (hH : InClass (2 * k + 1) H) :
    ∃ r : ℕ, Odd r ∧ 3 ≤ r ∧ ∃ N : ℕ,
      ∀ (p q : Fin k → ℕ) (hp : ∀ i, 5 ≤ p i) (hq : ∀ i, 5 ≤ q i),
        (∀ i, N ≤ p i) → (∀ i, N ≤ q i) →
        (∀ i, Nat.Coprime (p i) (q i)) →
        Nonempty ((SimpleGraph.cycleGraph r □ CartesianGraph (fun i =>
          TwelveTiles.graph (p i) (q i) (hp i) (hq i))) →g H) := by
  classical
  obtain ⟨N₀, α, hα, hproper, hJ, hφ⟩ := odd_dimension_finite_factor_graphs H k hH
  let J := fun i : Option (Fin k) =>
    AtomGraph (SchreierGraph (compactFreeModel_isFree (mixedDimension i))) (α i) (hproper i)
  obtain ⟨r, hr, hr₃, hfirst⟩ := inClass_one_odd_cycle_source (J none) (hJ none)
  have hrest : ∀ i : Fin k, ∃ N : ℕ,
      ∀ (p q : ℕ) (hp : 5 ≤ p) (hq : 5 ≤ q),
        N ≤ p → N ≤ q → Nat.Coprime p q →
        Nonempty (TwelveTiles.graph p q hp hq →g J (some i)) := by
    intro i
    exact References.gjks_eventual_twelve_tile_source (J (some i)) (hJ (some i))
  choose N hN using hrest
  let M := Finset.univ.sup N
  refine ⟨r, hr, hr₃, M, ?_⟩
  intro p q hp hq hpM hqM hcoprime
  have hfactor : ∀ i : Fin k,
      Nonempty (TwelveTiles.graph (p i) (q i) (hp i) (hq i) →g J (some i)) := by
    intro i
    have hi : N i ≤ M := Finset.le_sup (Finset.mem_univ i)
    exact hN i (p i) (q i) (hp i) (hq i) (hi.trans (hpM i)) (hi.trans (hqM i))
      (hcoprime i)
  let f : ∀ i : Fin k,
      TwelveTiles.graph (p i) (q i) (hp i) (hq i) →g J (some i) :=
    fun i => Classical.choice (hfactor i)
  exact ⟨(Classical.choice hφ).comp
    (optionCartesianHom J (SimpleGraph.cycleGraph r)
      (fun i => TwelveTiles.graph (p i) (q i) (hp i) (hq i))
      (Classical.choice hfirst) f)⟩

end AbelianTargets
