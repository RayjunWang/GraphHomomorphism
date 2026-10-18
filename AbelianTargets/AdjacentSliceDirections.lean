import AbelianTargets.TwelveTileDirections
import AbelianTargets.CartesianConstancy

namespace AbelianTargets

/-- Equation (11) with equal slice directions forces a constant cross
direction along each source edge. -/
theorem adjacent_slice_cross_direction_eq {W V : Type*}
    {G : SimpleGraph W} {H : SimpleGraph V} {m : ℕ}
    (laws : DirectionLaws H m) (f₀ f₁ : G →g H)
    (cross : ∀ w, H.Adj (f₀ w) (f₁ w)) {u v : W} (h : G.Adj u v)
    (heq : (laws.direction (f₀.map_adj h)).vector = (laws.direction (f₁.map_adj h)).vector) :
    laws.direction (cross u) = laws.direction (cross v) := by
  have hw := laws.four_walk (f₀.map_adj h) (cross v) (f₁.map_adj h).symm (cross u).symm
  rw [laws.reverse (f₁.map_adj h), laws.reverse (cross u), heq] at hw
  apply SignedDirection.vector_injective
  ext i
  have hi := congrFun hw i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hi
  omega

namespace TwelveTiles

variable {k m : ℕ} {p q : Fin k → ℕ}
variable {hp : ∀ i, 5 ≤ p i} {hq : ∀ i, 5 ≤ q i}
variable {V : Type*} {H : SimpleGraph V}

/-- Equality on positive raw grid steps is enough for equality on every
undirected product edge; reverse orientations use the reverse law. -/
theorem product_edge_directions_eq_of_positive_steps (laws : DirectionLaws H m)
    (f₀ f₁ : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H)
    (hh : ∀ (i : Fin k) (x y : (j : Fin k) → Vertex (p j) (q j)) (h : HorizontalStep (hp i) (hq i) (x i) (y i))
      (hr : ∀ j, j ≠ i → x j = y j),
      (laws.direction (f₀.map_adj ⟨i,h.adj,hr⟩)).vector =
        (laws.direction (f₁.map_adj ⟨i,h.adj,hr⟩)).vector)
    (hv : ∀ (i : Fin k) (x y : (j : Fin k) → Vertex (p j) (q j)) (h : VerticalStep (hp i) (hq i) (x i) (y i))
      (hr : ∀ j, j ≠ i → x j = y j),
      (laws.direction (f₀.map_adj ⟨i,h.adj,hr⟩)).vector =
        (laws.direction (f₁.map_adj ⟨i,h.adj,hr⟩)).vector) :
    ∀ u v (h : (CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i))).Adj u v),
      (laws.direction (f₀.map_adj h)).vector = (laws.direction (f₁.map_adj h)).vector := by
  intro u v huv
  obtain ⟨i,hi,hr⟩ := huv
  rcases hi with ⟨_, hfor | hrev⟩
  · rcases hfor with h | h
    · exact hh i u v h hr
    · exact hv i u v h hr
  · have hre : ∀ j, j ≠ i → v j = u j := fun j hj => (hr j hj).symm
    have hback : (CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i))).Adj v u := by
      rcases hrev with h | h
      · exact ⟨i,h.adj,hre⟩
      · exact ⟨i,h.adj,hre⟩
    change (laws.direction (f₀.map_adj hback).symm).vector =
      (laws.direction (f₁.map_adj hback).symm).vector
    rw [laws.reverse (f₀.map_adj hback), laws.reverse (f₁.map_adj hback)]
    congr 1
    rcases hrev with h | h
    · exact hh i v u h hre
    · exact hv i v u h hre

/-- The cross direction between equal-direction product slices is
independent of the entire literal finite twelve-tile product. -/
theorem adjacent_product_slices_cross_constant (laws : DirectionLaws H m)
    (f₀ f₁ : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H)
    (cross : ∀ w, H.Adj (f₀ w) (f₁ w))
    (heq : ∀ u v (h : (CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i))).Adj u v),
      (laws.direction (f₀.map_adj h)).vector = (laws.direction (f₁.map_adj h)).vector) :
    ∀ w, laws.direction (cross w) = laws.direction (cross (fun i => base (p i) (q i))) := by
  apply cartesian_edge_invariant_constant
    (fun i => graph (p i) (q i) (hp i) (hq i)) (fun i => base (p i) (q i))
    (fun i => constant_of_edge_invariant (hp i) (hq i))
  intro u v huv
  exact adjacent_slice_cross_direction_eq laws f₀ f₁ cross huv (heq u v huv)

end TwelveTiles
end AbelianTargets
