import AbelianTargets.ProductAxisRigidity
import AbelianTargets.AdjacentSliceDirections
import AbelianTargets.ProductShift
import AbelianTargets.CyclicTransfers

/-!
# The actual odd-cycle product obstruction (Lemma 7.6)

The finite source is the literal cycle graph and the literal twelve-tile
Cartesian product. Its homomorphism is pulled back to the product of
two-dimensional free shifts using the cited directed GJKS maps. Direction
rigidity, the four-walk identity and straight-middle uniqueness then
produce the nonzero odd-cycle translation ruled out by active-factor
transitivity.
-/

namespace AbelianTargets

open SimpleGraph TwelveTiles
open scoped BigOperators

theorem edge_invariant_constant_of_preconnected
    {W A : Type*} (G : SimpleGraph W) (hG : G.Preconnected)
    (c : W → A) (hedge : ∀ u v, G.Adj u v → c u = c v) :
    ∀ u v, c u = c v := by
  have hw : ∀ {u v} (p : G.Walk u v), c u = c v := by
    intro u v p
    induction p with
    | nil => rfl
    | @cons u v w h p ih => exact (hedge _ _ h).trans ih
  intro u v
  exact hw (hG u v).some

theorem cycleGraph_adj_succ {r : ℕ} [NeZero r] (hr : 2 ≤ r) (j : Fin r) :
    (SimpleGraph.cycleGraph r).Adj j (j + 1) := by
  cases r with
  | zero => exact j.elim0
  | succ r =>
    cases r with
    | zero => omega
    | succ n => exact SimpleGraph.cycleGraph_adj.mpr (Or.inr (by simp))

def cycleProductSliceHom
    {r k : ℕ} {p q : Fin k → ℕ} {hp : ∀ i, 5 ≤ p i} {hq : ∀ i, 5 ≤ q i}
    {V : Type*} {H : SimpleGraph V}
    (f : (SimpleGraph.cycleGraph r □ CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i))) →g H)
    (j : Fin r) : CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i)) →g H where
  toFun x := f (j,x)
  map_rel' := fun h => f.map_adj (Or.inr ⟨h,rfl⟩)

theorem lemma7_6
    {r k : ℕ} (_hk : 1 ≤ k) (hr : Odd r) (hr₃ : 3 ≤ r)
    {p q : Fin k → ℕ} (hp : ∀ i, 5 ≤ p i) (hq : ∀ i, 5 ≤ q i)
    (hpodd : ∀ i, Odd (p i)) (hcop : ∀ i, (p i).Coprime (q i))
    (hcopPair : ∀ i j, i ≠ j → (p i).Coprime (p j))
    {V : Type*} [TopologicalSpace V] [Fintype V] [DiscreteTopology V]
    {H : SimpleGraph V} (laws : DirectionLaws H (2 * k)) :
    ¬Nonempty ((SimpleGraph.cycleGraph r □ CartesianGraph
      (fun i => graph (p i) (q i) (hp i) (hq i))) →g H) := by
  classical
  rintro ⟨f⟩
  letI : NeZero r := ⟨by omega⟩
  let T := CartesianGraph (fun i => graph (p i) (q i) (hp i) (hq i))
  let f' : Fin r → T →g H := fun j => cycleProductSliceHom f j
  let D : (j : Fin r) → ProductUniformDirections laws (f' j) :=
    fun j => Classical.choice (exists_productUniformDirections laws (f' j) hpodd hcop)
  have hD : ∀ j, (D j).direction = (D 0).direction := by
    intro j
    apply edge_invariant_constant_of_preconnected (SimpleGraph.cycleGraph r)
      SimpleGraph.cycleGraph_preconnected (fun j => (D j).direction) _ j 0
    intro a b hab
    exact (D a).adjacent_eq laws (f' a) (f' b) (D b)
      (fun x => f.map_adj (Or.inl ⟨hab,rfl⟩))
  let s : Fin (2 * k) → SignedDirection (2 * k) :=
    fun a => (D 0).direction ((blockIndex k).symm a)
  have hs : Function.Injective (fun a => (s a).axis) := by
    exact ((D 0).axis_injective laws (f' 0) hcop hcopPair).comp (blockIndex k).symm.injective
  let cross : ∀ j : Fin r, ∀ x : ProductVertex p q, H.Adj (f' j x) (f' (j+1) x) :=
    fun j x => f.map_adj (Or.inl ⟨cycleGraph_adj_succ (by omega) j,rfl⟩)
  let δ : Fin r → SignedDirection (2 * k) :=
    fun j => laws.direction (cross j (fun i => base (p i) (q i)))
  have hδ : ∀ j x, laws.direction (cross j x) = δ j := by
    intro j
    apply adjacent_product_slices_cross_constant laws (f' j) (f' (j+1)) (cross j)
    apply product_edge_directions_eq_of_positive_steps laws (f' j) (f' (j+1))
    · intro i x y h hrest
      rw [(D j).horizontal_eq ⟨h,hrest⟩, (D (j+1)).horizontal_eq ⟨h,hrest⟩,
        hD j, hD (j+1)]
    · intro i x y h hrest
      rw [(D j).vertical_eq ⟨h,hrest⟩, (D (j+1)).vertical_eq ⟨h,hrest⟩,
        hD j, hD (j+1)]
  have hsource : ∀ i : Fin k, ∃ θ : FreeShift 2 → Vertex (p i) (q i), Continuous θ ∧
      (∀ x, HorizontalStep (hp i) (hq i) (θ x) (θ (unitVector (0 : Fin 2) +ᵥ x))) ∧
      (∀ x, VerticalStep (hp i) (hq i) (θ x) (θ (unitVector (1 : Fin 2) +ᵥ x))) :=
    fun i => References.gjks_direction_preserving_twelve_tiles (p i) (q i) (hp i) (hq i) (hcop i)
  choose θ hθ hhor hver using hsource
  let Θ : ProductShift k → ProductVertex p q := fun x i => θ i (x i)
  have hΘ : Continuous Θ := continuous_pi (fun i => (hθ i).comp (continuous_apply i))
  let c : Fin r → ProductShift k → V := fun j x => f' j (Θ x)
  have hc : Continuous (c 0) := continuous_of_discreteTopology.comp hΘ
  have hhorProd : ∀ i x, ProductHorizontalStep hp hq i (Θ x)
      (Θ (unitVector (blockIndex k (i,(0 : Fin 2))) +ᵥ x)) := by
    intro i x
    constructor
    · change HorizontalStep (hp i) (hq i) (θ i (x i))
        (θ i (blockVector (unitVector (blockIndex k (i,(0 : Fin 2)))) i +ᵥ x i))
      simpa only [blockVector_unit, if_pos rfl] using hhor i (x i)
    · intro a hai
      change θ a (x a) = θ a (blockVector (unitVector (blockIndex k (i,(0 : Fin 2)))) a +ᵥ x a)
      simp only [blockVector_unit, if_neg hai, zero_vadd]
  have hverProd : ∀ i x, ProductVerticalStep hp hq i (Θ x)
      (Θ (unitVector (blockIndex k (i,(1 : Fin 2))) +ᵥ x)) := by
    intro i x
    constructor
    · change VerticalStep (hp i) (hq i) (θ i (x i))
        (θ i (blockVector (unitVector (blockIndex k (i,(1 : Fin 2)))) i +ᵥ x i))
      simpa only [blockVector_unit, if_pos rfl] using hver i (x i)
    · intro a hai
      change θ a (x a) = θ a (blockVector (unitVector (blockIndex k (i,(1 : Fin 2)))) a +ᵥ x a)
      simp only [blockVector_unit, if_neg hai, zero_vadd]
  have hpositive : ∀ (j : Fin r) (a : Fin (2*k)) (x : ProductShift k),
      ∃ h : H.Adj (c j x) (c j (unitVector a +ᵥ x)),
        (laws.direction h).vector = (s a).vector := by
    intro j a x
    obtain ⟨⟨i,l⟩, rfl⟩ := (blockIndex k).surjective a
    fin_cases l
    · refine ⟨(f' j).map_adj (hhorProd i x).adj, ?_⟩
      calc
        _ = ((D j).direction (i,0)).vector := (D j).horizontal_eq (hhorProd i x)
        _ = (s (blockIndex k (i,0))).vector := by simp only [s, hD j, Equiv.symm_apply_apply]
    · refine ⟨(f' j).map_adj (hverProd i x).adj, ?_⟩
      calc
        _ = ((D j).direction (i,1)).vector := (D j).vertical_eq (hverProd i x)
        _ = (s (blockIndex k (i,1))).vector := by simp only [s, hD j, Equiv.symm_apply_apply]
  choose positive hdir using hpositive
  have he : ∀ j : Fin r, ∃ e : SignedDirection (2*k),
      (if e.positive then (s e.axis).vector else -(s e.axis).vector) = (δ j).vector :=
    fun j => signedDirection_preimage_of_axis_injective s hs (δ j)
  choose e he using he
  have htransfer : ∀ j x, c (j+1) x = c j ((e j).vector +ᵥ x) := by
    intro j
    have h₀ : ∀ x, ∃ h : H.Adj (c j x) (c j ((e j).vector +ᵥ x)),
        (laws.direction h).vector = (δ j).vector := by
      intro x
      obtain ⟨h,hh⟩ := signed_coordinate_step laws (c j) s (positive j) (hdir j) (e j) x
      exact ⟨h,hh.trans (he j)⟩
    have h₁ : ∀ x, ∃ h : H.Adj (c (j+1) x) (c (j+1) ((e j).vector +ᵥ x)),
        (laws.direction h).vector = (δ j).vector := by
      intro x
      obtain ⟨h,hh⟩ := signed_coordinate_step laws (c (j+1)) s (positive (j+1)) (hdir (j+1)) (e j) x
      exact ⟨h,hh.trans (he j)⟩
    choose step₀ hstep₀ using h₀
    choose step₁ hstep₁ using h₁
    apply straight_middle_color_transfer laws (c j) (c (j+1)) (e j).vector (δ j)
      (fun x => cross j (Θ x)) (fun x => congrArg SignedDirection.vector (hδ j (Θ x)))
      step₀ step₁ hstep₀ hstep₁
  exact productShift_no_nonzero_invariant_proper_coloring H _
    (odd_signedDirection_sum_ne_zero hr e) (c 0) hc
    (cyclic_transfers_translation_invariant c e htransfer) (positive 0)

end AbelianTargets
