import AbelianTargets.TwelveTileDirections
import AbelianTargets.CartesianConstancy

/-!
# Direction independence across Cartesian factor slices

The four-walk identity telescopes around a closed cycle in two adjacent
slices. A nonzero cycle length forces their constant directions to agree.
Cartesian connectivity then propagates the equality across all contexts.
-/

namespace AbelianTargets

open scoped BigOperators

theorem adjacent_closed_cycle_directions_eq
    {W V : Type*} {H : SimpleGraph V} {m r : ℕ}
    (laws : DirectionLaws H m) (hr : 0 < r) (c : ℕ → W) (hc : c r = c 0)
    (f₀ f₁ : W → V)
    (cross : ∀ w, H.Adj (f₀ w) (f₁ w))
    (edge₀ : ∀ n, H.Adj (f₀ (c n)) (f₀ (c (n + 1))))
    (edge₁ : ∀ n, H.Adj (f₁ (c n)) (f₁ (c (n + 1))))
    (u v : SignedDirection m)
    (hu : ∀ n < r, (laws.direction (edge₀ n)).vector = u.vector)
    (hv : ∀ n < r, (laws.direction (edge₁ n)).vector = v.vector) : u = v := by
  let δ : ℕ → Lattice m := fun n => (laws.direction (cross (c n))).vector
  have hcurl : ∀ n < r, v.vector - u.vector = δ (n + 1) - δ n := by
    intro n hn
    have h := laws.four_walk (edge₀ n) (cross (c (n + 1)))
      (edge₁ n).symm (cross (c n)).symm
    rw [laws.reverse (edge₁ n), laws.reverse (cross (c n)), hu n hn, hv n hn] at h
    ext a
    have hh := congrFun h a
    simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.zero_apply] at hh ⊢
    change _ = (laws.direction (cross (c (n + 1)))).vector a -
      (laws.direction (cross (c n))).vector a
    omega
  have hsum : r • (v.vector - u.vector) = 0 := by
    have hh : (∑ n ∈ Finset.range r, (v.vector - u.vector)) =
        ∑ n ∈ Finset.range r, (δ (n + 1) - δ n) :=
      Finset.sum_congr rfl (fun n hn => hcurl n (Finset.mem_range.mp hn))
    rw [TwelveTiles.sum_range_difference] at hh
    have hd : δ r = δ 0 := congrArg (fun w => (laws.direction (cross w)).vector) hc
    simpa only [Finset.sum_const, Finset.card_range, hd, sub_self] using hh
  apply SignedDirection.vector_injective
  ext a
  have hh := congrFun hsum a
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, Int.nsmul_eq_mul] at hh
  have hr0 : (r : ℤ) ≠ 0 := by omega
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hr0)).symm

namespace TwelveTiles

variable {k m : ℕ} {p q : Fin k → ℕ}
variable (hp : ∀ i, 5 ≤ p i) (hq : ∀ i, 5 ≤ q i)

abbrev ProductVertex (p q : Fin k → ℕ) := (i : Fin k) → Vertex (p i) (q i)

def ProductHorizontalStep (i : Fin k) (x y : ProductVertex p q) : Prop :=
  HorizontalStep (hp i) (hq i) (x i) (y i) ∧ ∀ j, j ≠ i → x j = y j

def ProductVerticalStep (i : Fin k) (x y : ProductVertex p q) : Prop :=
  VerticalStep (hp i) (hq i) (x i) (y i) ∧ ∀ j, j ≠ i → x j = y j

theorem ProductHorizontalStep.adj {i : Fin k} {x y : ProductVertex p q}
    (h : ProductHorizontalStep hp hq i x y) :
    (CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i))).Adj x y :=
  ⟨i, h.1.adj, h.2⟩

theorem ProductVerticalStep.adj {i : Fin k} {x y : ProductVertex p q}
    (h : ProductVerticalStep hp hq i x y) :
    (CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i))).Adj x y :=
  ⟨i, h.1.adj, h.2⟩

variable {hp hq}
variable {V : Type*} {H : SimpleGraph V}

def productSliceHom
    (f : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H)
    (i : Fin k) (x : ProductVertex p q) : graph (p i) (q i) (hp i) (hq i) →g H where
  toFun a := f (Function.update x i a)
  map_rel' := by
    intro a b hab
    apply f.map_adj
    refine ⟨i, ?_, ?_⟩
    · simpa using hab
    · intro j hji
      simp [Function.update_of_ne hji]

noncomputable def sliceUniformDirections (laws : DirectionLaws H m)
    (f : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H)
    (hpodd : ∀ i, Odd (p i)) (hcop : ∀ i, (p i).Coprime (q i))
    (i : Fin k) (x : ProductVertex p q) : UniformDirections laws (productSliceHom f i x) :=
  Classical.choice (exists_uniformDirections laws (productSliceHom f i x) (hpodd i) (hcop i))

theorem sliceUniformDirections_edge_invariant (laws : DirectionLaws H m)
    (f : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H)
    (hpodd : ∀ i, Odd (p i)) (hcop : ∀ i, (p i).Coprime (q i)) (i : Fin k)
    {x y : ProductVertex p q}
    (hxy : (CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i))).Adj x y) :
    (sliceUniformDirections laws f hpodd hcop i x).horizontal =
        (sliceUniformDirections laws f hpodd hcop i y).horizontal ∧
      (sliceUniformDirections laws f hpodd hcop i x).vertical =
        (sliceUniformDirections laws f hpodd hcop i y).vertical := by
  classical
  let D₀ := sliceUniformDirections laws f hpodd hcop i x
  let D₁ := sliceUniformDirections laws f hpodd hcop i y
  obtain ⟨j, hj, hrest⟩ := hxy
  by_cases hji : j = i
  · subst j
    have hupdate : ∀ a, Function.update x i a = Function.update y i a := by
      intro a
      funext l
      by_cases hli : l = i
      · subst l; simp
      · simp only [Function.update_of_ne hli]
        exact hrest l hli
    have hf : productSliceHom f i x = productSliceHom f i y := by
      ext a
      exact congrArg f (hupdate a)
    constructor
    · apply SignedDirection.vector_injective
      calc
        D₀.horizontal.vector = cycleVector laws (productSliceHom f i x) 2 0 :=
          (D₀.cycleVector_horizontal laws _ 2 (by decide) 0).symm
        _ = cycleVector laws (productSliceHom f i y) 2 0 := by rw [hf]
        _ = D₁.horizontal.vector := D₁.cycleVector_horizontal laws _ 2 (by decide) 0
    · apply SignedDirection.vector_injective
      calc
        D₀.vertical.vector = cycleVector laws (productSliceHom f i x) 0 0 :=
          (D₀.cycleVector_vertical laws _ 0 (by decide) 0).symm
        _ = cycleVector laws (productSliceHom f i y) 0 0 := by rw [hf]
        _ = D₁.vertical.vector := D₁.cycleVector_vertical laws _ 0 (by decide) 0
  · have cross : ∀ a, H.Adj ((productSliceHom f i x) a) ((productSliceHom f i y) a) := by
      intro a
      apply f.map_adj
      refine ⟨j, ?_, ?_⟩
      · simpa only [Function.update_of_ne hji] using hj
      · intro l hlj
        by_cases hli : l = i
        · subst l; simp
        · simp only [Function.update_of_ne hli]
          exact hrest l hlj
    have hc (l : Fin 4) : cycleAt (hp i) (hq i) l (cycleLength (p i) (q i) l) =
        cycleAt (hp i) (hq i) l 0 := by
      simp
    constructor
    · apply adjacent_closed_cycle_directions_eq laws (cycleLength_pos (hp i) (hq i) 2)
        (cycleAt (hp i) (hq i) 2) (hc 2)
        (productSliceHom f i x) (productSliceHom f i y) cross
        (fun n => (productSliceHom f i x).map_adj (cycle_adj_all (hp i) (hq i) 2 n))
        (fun n => (productSliceHom f i y).map_adj (cycle_adj_all (hp i) (hq i) 2 n))
      · intro n _hn
        exact D₀.cycleVector_horizontal laws _ 2 (by decide) n
      · intro n _hn
        exact D₁.cycleVector_horizontal laws _ 2 (by decide) n
    · apply adjacent_closed_cycle_directions_eq laws (cycleLength_pos (hp i) (hq i) 0)
        (cycleAt (hp i) (hq i) 0) (hc 0)
        (productSliceHom f i x) (productSliceHom f i y) cross
        (fun n => (productSliceHom f i x).map_adj (cycle_adj_all (hp i) (hq i) 0 n))
        (fun n => (productSliceHom f i y).map_adj (cycle_adj_all (hp i) (hq i) 0 n))
      · intro n _hn
        exact D₀.cycleVector_vertical laws _ 0 (by decide) n
      · intro n _hn
        exact D₁.cycleVector_vertical laws _ 0 (by decide) n

structure ProductUniformDirections (laws : DirectionLaws H m)
    (f : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H) where
  direction : Fin k × Fin 2 → SignedDirection m
  horizontal_eq : ∀ {i x y} (h : ProductHorizontalStep hp hq i x y),
    (laws.direction (f.map_adj h.adj)).vector = (direction (i, 0)).vector
  vertical_eq : ∀ {i x y} (h : ProductVerticalStep hp hq i x y),
    (laws.direction (f.map_adj h.adj)).vector = (direction (i, 1)).vector

/-- The constant-direction part of Lemma 7.4 on the entire literal
Cartesian source, with independence of all other factor coordinates. -/
theorem exists_productUniformDirections (laws : DirectionLaws H m)
    (f : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H)
    (hpodd : ∀ i, Odd (p i)) (hcop : ∀ i, (p i).Coprime (q i)) :
    Nonempty (ProductUniformDirections laws f) := by
  classical
  let G := fun i => graph (p i) (q i) (hp i) (hq i)
  let b : ProductVertex p q := fun i => base (p i) (q i)
  let D := sliceUniformDirections laws f hpodd hcop
  have hh : ∀ i x, (D i x).horizontal = (D i b).horizontal := by
    intro i
    apply cartesian_edge_invariant_constant G b
      (fun a g hg => constant_of_edge_invariant (hp a) (hq a) g hg)
    intro x y hxy
    exact (sliceUniformDirections_edge_invariant laws f hpodd hcop i hxy).1
  have hv : ∀ i x, (D i x).vertical = (D i b).vertical := by
    intro i
    apply cartesian_edge_invariant_constant G b
      (fun a g hg => constant_of_edge_invariant (hp a) (hq a) g hg)
    intro x y hxy
    exact (sliceUniformDirections_edge_invariant laws f hpodd hcop i hxy).2
  let dir : Fin k × Fin 2 → SignedDirection m := fun z =>
    if z.2 = 0 then (D z.1 b).horizontal else (D z.1 b).vertical
  refine ⟨⟨dir, ?_, ?_⟩⟩
  · intro i x y h
    have hupdate : Function.update x i (y i) = y := by
      funext j
      by_cases hji : j = i
      · subst j; simp
      · simp only [Function.update_of_ne hji]
        exact h.2 j hji
    have he := (D i x).horizontal_step_eq laws (productSliceHom f i x) h.1
    rw [hh i x] at he
    simpa [edgeVector, productSliceHom, hupdate, dir] using he
  · intro i x y h
    have hupdate : Function.update x i (y i) = y := by
      funext j
      by_cases hji : j = i
      · subst j; simp
      · simp only [Function.update_of_ne hji]
        exact h.2 j hji
    have he := (D i x).vertical_step_eq laws (productSliceHom f i x) h.1
    rw [hv i x] at he
    simpa [edgeVector, productSliceHom, hupdate, dir] using he

def productPCycle (hp : ∀ i, 5 ≤ p i) (hq : ∀ i, 5 ≤ q i)
    (i : Fin k) (s : Fin 2) (n : ℕ) : ProductVertex p q :=
  Function.update (fun j => base (p j) (q j)) i
    (cycleAt (hp i) (hq i) (if s = 0 then 2 else 0) n)

theorem productPCycle_closed (i : Fin k) (s : Fin 2) :
    productPCycle hp hq i s (p i) = productPCycle hp hq i s 0 := by
  fin_cases s <;> simp [productPCycle, cycleAt, cycleLength, cyclePoint]

theorem productPCycle_adj (i : Fin k) (s : Fin 2) (n : ℕ) :
    (CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i))).Adj
      (productPCycle hp hq i s n) (productPCycle hp hq i s (n + 1)) := by
  refine ⟨i, ?_, ?_⟩
  · simpa only [productPCycle, Function.update_self] using
      cycle_adj_all (hp i) (hq i) (if s = 0 then 2 else 0) n
  · intro j hji
    simp [productPCycle, hji]

theorem productPCycle_horizontal (i : Fin k) (n : ℕ) (hn : n < p i) :
    ProductHorizontalStep hp hq i
      (productPCycle hp hq i 0 n) (productPCycle hp hq i 0 (n + 1)) := by
  constructor
  · simpa only [productPCycle, if_pos rfl, Function.update_self] using
      cycle_horizontalStep (hp i) (hq i) 2 (by decide) n hn
  · intro j hji
    simp [productPCycle, hji]

theorem productPCycle_vertical (i : Fin k) (n : ℕ) (hn : n < p i) :
    ProductVerticalStep hp hq i
      (productPCycle hp hq i 1 n) (productPCycle hp hq i 1 (n + 1)) := by
  constructor
  · simpa [productPCycle] using
      cycle_verticalStep (hp i) (hq i) 0 (by decide) n hn
  · intro j hji
    simp [productPCycle, hji]

theorem ProductUniformDirections.productPCycle_direction (laws : DirectionLaws H m)
    (f : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H)
    (D : ProductUniformDirections laws f) (i : Fin k) (s : Fin 2)
    (n : ℕ) (hn : n < p i) :
    (laws.direction (f.map_adj (productPCycle_adj i s n))).vector =
      (D.direction (i, s)).vector := by
  fin_cases s
  · exact D.horizontal_eq (productPCycle_horizontal i n hn)
  · exact D.vertical_eq (productPCycle_vertical i n hn)

/-- Adjacent copies of the full source have identical global directions.
This compares consecutive odd-cycle layers in Lemma 7.6. -/
theorem ProductUniformDirections.adjacent_eq (laws : DirectionLaws H m)
    (f₀ f₁ : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H)
    (D₀ : ProductUniformDirections laws f₀) (D₁ : ProductUniformDirections laws f₁)
    (cross : ∀ x, H.Adj (f₀ x) (f₁ x)) : D₀.direction = D₁.direction := by
  funext z
  obtain ⟨i, s⟩ := z
  apply adjacent_closed_cycle_directions_eq laws (by have := hp i; omega)
    (productPCycle hp hq i s) (productPCycle_closed i s) f₀ f₁ cross
    (fun n => f₀.map_adj (productPCycle_adj i s n))
    (fun n => f₁.map_adj (productPCycle_adj i s n))
  · intro n hn
    exact D₀.productPCycle_direction laws f₀ i s n hn
  · intro n hn
    exact D₁.productPCycle_direction laws f₁ i s n hn
end TwelveTiles

end AbelianTargets
