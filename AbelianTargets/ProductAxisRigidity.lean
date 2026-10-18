import AbelianTargets.TwelveTileAxisCycles
import AbelianTargets.CompactFactorization
import AbelianTargets.ProductSliceRigidity

namespace AbelianTargets.TwelveTiles

variable {k : ℕ} {p q : Fin k → ℕ}
variable {hp : ∀ i, 5 ≤ p i} {hq : ∀ i, 5 ≤ q i}
variable {m : ℕ} {V : Type*} {H : SimpleGraph V}

def ProductAxisStep (hp : ∀ i, 5 ≤ p i) (hq : ∀ i, 5 ≤ q i)
    (i : Fin k) (s : Fin 2) (x y : ProductVertex p q) : Prop :=
  AxisStep (hp i) (hq i) s (x i) (y i) ∧ ∀ j, j ≠ i → x j = y j

theorem ProductAxisStep.adj {i : Fin k} {s : Fin 2} {x y : ProductVertex p q}
    (h : ProductAxisStep hp hq i s x y) :
    (CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i))).Adj x y :=
  ⟨i,h.1.adj,h.2⟩

noncomputable def twoCycleVertex (hp : ∀ i, 5 ≤ p i) (hq : ∀ i, 5 ≤ q i)
    (i j : Fin k) (s t : Fin 2) (z : ZMod (p i) × ZMod (p j)) : ProductVertex p q := by
  classical
  exact Function.update (Function.update (fun r => base (p r) (q r)) i
    (axisCyclePoint (hp i) (hq i) s z.1)) j (axisCyclePoint (hp j) (hq j) t z.2)

theorem twoCycleVertex_horizontal_step (hp : ∀ i, 5 ≤ p i) (hq : ∀ i, 5 ≤ q i)
    (i j : Fin k) (hij : i ≠ j) (s t : Fin 2) (a : ZMod (p i)) (b : ZMod (p j)) :
    ProductAxisStep hp hq i s (twoCycleVertex hp hq i j s t (a,b))
      (twoCycleVertex hp hq i j s t (a+1,b)) := by
  classical
  constructor
  · simpa [twoCycleVertex, hij] using axisCyclePoint_step (hp i) (hq i) s a
  · intro r hri
    by_cases hrj : r = j
    · subst r; simp [twoCycleVertex]
    · simp [twoCycleVertex, hri, hrj]

theorem twoCycleVertex_vertical_step (hp : ∀ i, 5 ≤ p i) (hq : ∀ i, 5 ≤ q i)
    (i j : Fin k) (hij : i ≠ j) (s t : Fin 2) (a : ZMod (p i)) (b : ZMod (p j)) :
    ProductAxisStep hp hq j t (twoCycleVertex hp hq i j s t (a,b))
      (twoCycleVertex hp hq i j s t (a,b+1)) := by
  classical
  constructor
  · simpa [twoCycleVertex] using axisCyclePoint_step (hp j) (hq j) t b
  · intro r hrj
    by_cases hri : r = i
    · subst r; simp [twoCycleVertex, hij]
    · simp [twoCycleVertex, hri, hrj]

/-- Global constant edge directions in a product cannot share axes
between different factors: the actual pair of based source cycles is
a coprime finite torus, so the straight-middle law gives a contradiction. -/
theorem product_directions_distinct_factors (laws : DirectionLaws H m)
    (f : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H)
    (d : Fin k × Fin 2 → SignedDirection m)
    (hdir : ∀ i s x y (h : ProductAxisStep hp hq i s x y),
      (laws.direction (f.map_adj h.adj)).vector = (d (i,s)).vector)
    (i j : Fin k) (hij : i ≠ j) (hcop : (p i).Coprime (p j)) (s t : Fin 2) :
    (d (i,s)).axis ≠ (d (j,t)).axis := by
  apply coprime_torus_directions_distinct_axes (by have := hp i; omega)
    (by have := hp j; omega) hcop laws
    (fun z => f (twoCycleVertex hp hq i j s t z)) (d (i,s)) (d (j,t))
    (fun a b => f.map_adj (twoCycleVertex_horizontal_step hp hq i j hij s t a b).adj)
    (fun a b => f.map_adj (twoCycleVertex_vertical_step hp hq i j hij s t a b).adj)
  · intro a b
    exact hdir i s _ _ (twoCycleVertex_horizontal_step hp hq i j hij s t a b)
  · intro a b
    exact hdir j t _ _ (twoCycleVertex_vertical_step hp hq i j hij s t a b)

theorem product_direction_axes_injective (laws : DirectionLaws H m)
    (f : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H)
    (d : Fin k × Fin 2 → SignedDirection m)
    (hdir : ∀ i s x y (h : ProductAxisStep hp hq i s x y),
      (laws.direction (f.map_adj h.adj)).vector = (d (i,s)).vector)
    (hsame : ∀ i, (d (i,0)).axis ≠ (d (i,1)).axis)
    (hcop : ∀ i j, i ≠ j → (p i).Coprime (p j)) :
    Function.Injective (fun a => (d a).axis) := by
  rintro ⟨i,s⟩ ⟨j,t⟩ heq
  have hij : i = j := by
    by_contra hn
    exact product_directions_distinct_factors laws f d hdir i j hn (hcop i j hn) s t heq
  subst j
  congr 1
  fin_cases s <;> fin_cases t
  · rfl
  · exact (hsame i heq).elim
  · exact (hsame i heq.symm).elim
  · rfl

theorem ProductUniformDirections.axis_step_eq (laws : DirectionLaws H m)
    (f : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H)
    (D : ProductUniformDirections laws f) {i : Fin k} {s : Fin 2} {x y : ProductVertex p q}
    (h : ProductAxisStep hp hq i s x y) :
    (laws.direction (f.map_adj h.adj)).vector = (D.direction (i,s)).vector := by
  fin_cases s
  · exact D.horizontal_eq h
  · exact D.vertical_eq h

def ProductUniformDirections.factor (laws : DirectionLaws H m)
    (f : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H)
    (D : ProductUniformDirections laws f) (i : Fin k) (b : ProductVertex p q) :
    UniformDirections laws (productSliceHom f i b) where
  horizontal := D.direction (i,0)
  vertical := D.direction (i,1)
  horizontal_eq := by
    intro t x y hx hy
    have hs : HorizontalStep (hp i) (hq i)
        (tileVertex (hp i) (hq i) t x y) (tileVertex (hp i) (hq i) t (x+1) y) :=
      ⟨t,x,y,hx,hy,rfl,rfl⟩
    have hprod : ProductHorizontalStep hp hq i
        (Function.update b i (tileVertex (hp i) (hq i) t x y))
        (Function.update b i (tileVertex (hp i) (hq i) t (x+1) y)) := by
      constructor
      · simpa using hs
      · intro j hj; simp [Function.update_of_ne hj]
    have he := D.horizontal_eq hprod
    simpa only [horizontalVector, dif_pos (show x < width (p i) (q i) t ∧
      y ≤ height (p i) (q i) t from ⟨hx,hy⟩), edgeVector, productSliceHom] using he
  vertical_eq := by
    intro t x y hx hy
    have hs : VerticalStep (hp i) (hq i)
        (tileVertex (hp i) (hq i) t x y) (tileVertex (hp i) (hq i) t x (y+1)) :=
      ⟨t,x,y,hx,hy,rfl,rfl⟩
    have hprod : ProductVerticalStep hp hq i
        (Function.update b i (tileVertex (hp i) (hq i) t x y))
        (Function.update b i (tileVertex (hp i) (hq i) t x (y+1))) := by
      constructor
      · simpa using hs
      · intro j hj; simp [Function.update_of_ne hj]
    have he := D.vertical_eq hprod
    simpa only [verticalVector, dif_pos (show x ≤ width (p i) (q i) t ∧
      y < height (p i) (q i) t from ⟨hx,hy⟩), edgeVector, productSliceHom] using he

theorem ProductUniformDirections.axis_injective (laws : DirectionLaws H m)
    (f : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H)
    (D : ProductUniformDirections laws f)
    (hcop : ∀ i, (p i).Coprime (q i))
    (hcopPair : ∀ i j, i ≠ j → (p i).Coprime (p j)) :
    Function.Injective (fun a => (D.direction a).axis) := by
  apply product_direction_axes_injective laws f D.direction
    (fun i s x y h => D.axis_step_eq laws f h) _ hcopPair
  intro i
  exact (D.factor laws f i (fun j => base (p j) (q j))).distinct_axes laws _ (hcop i)

/-- Lemma 7.4 on the literal product, with the weaker exact arithmetic
hypotheses actually used by its proof. Distinct odd prime parameters
from the paper satisfy all three displayed parameter conditions. -/
theorem lemma7_4 (laws : DirectionLaws H m)
    (f : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H)
    (hpodd : ∀ i, Odd (p i)) (hcop : ∀ i, (p i).Coprime (q i))
    (hcopPair : ∀ i j, i ≠ j → (p i).Coprime (p j)) :
    ∃ D : ProductUniformDirections laws f,
      Function.Injective (fun a => (D.direction a).axis) := by
  obtain ⟨D⟩ := exists_productUniformDirections laws f hpodd hcop
  exact ⟨D,D.axis_injective laws f hcop hcopPair⟩

theorem lemma7_4_dimension_bound (laws : DirectionLaws H m)
    (f : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H)
    (hpodd : ∀ i, Odd (p i)) (hcop : ∀ i, (p i).Coprime (q i))
    (hcopPair : ∀ i j, i ≠ j → (p i).Coprime (p j)) : 2*k ≤ m := by
  obtain ⟨D,hinj⟩ := lemma7_4 laws f hpodd hcop hcopPair
  have hc := Fintype.card_le_of_injective (fun a => (D.direction a).axis) hinj
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using hc

end AbelianTargets.TwelveTiles
