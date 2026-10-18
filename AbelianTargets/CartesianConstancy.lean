import AbelianTargets.CompactFactorization

/-!
# Propagation across a finite Cartesian product

An edge-invariant function on a Cartesian product is constant when each
factor has this property. The proof replaces one coordinate at a time.
-/

namespace AbelianTargets

theorem cartesian_edge_invariant_constant
    {I : Type*} [Fintype I] {V : I → Type*} {A : Type*}
    (G : (i : I) → SimpleGraph (V i)) (base : (i : I) → V i)
    (hfactor : ∀ i, ∀ g : V i → A,
      (∀ u v, (G i).Adj u v → g u = g v) → ∀ x, g x = g (base i))
    (f : ((i : I) → V i) → A)
    (hedge : ∀ x y, (CartesianGraph G).Adj x y → f x = f y) :
    ∀ x, f x = f base := by
  classical
  have hcoordinate : ∀ x i a,
      f (Function.update x i a) = f (Function.update x i (base i)) := by
    intro x i a
    apply hfactor i (fun a => f (Function.update x i a))
    intro u v huv
    apply hedge
    refine ⟨i, ?_, ?_⟩
    · simpa using huv
    · intro j hji
      simp [Function.update_of_ne hji]
  have hsubset : ∀ S : Finset I, ∀ x : (i : I) → V i,
      (∀ i, i ∉ S → x i = base i) → f x = f base := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x hx
      have hxb : x = base := funext (fun i => hx i (Finset.notMem_empty i))
      rw [hxb]
    | @insert i S hi ih =>
      intro x hx
      calc
        f x = f (Function.update x i (base i)) := by
          simpa using hcoordinate x i (x i)
        _ = f base := by
          apply ih
          intro j hj
          by_cases hji : j = i
          · subst j
            simp
          · rw [Function.update_of_ne hji]
            exact hx j (by simp [hji, hj])
  intro x
  exact hsubset Finset.univ x (by simp)

end AbelianTargets
