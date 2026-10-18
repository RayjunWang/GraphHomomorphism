import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite

/-!
Definitions for arXiv:2609.39824v1, Sections 2.1 and 7.2.
The action convention is `(g +ᵥ x)(u) = x(u + g)`.
-/

namespace AbelianTargets

abbrev Lattice (d : ℕ) := Fin d → ℤ

def unitVector {d : ℕ} (i : Fin d) : Lattice d :=
  fun j => if j = i then 1 else 0

def IsFree {G X : Type*} [AddGroup G] [AddAction G X] : Prop :=
  ∀ (g : G) (x : X), g +ᵥ x = x → g = 0

def ZeroDimensional (X : Type*) [TopologicalSpace X] : Prop :=
  TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s}

def StandardEdge {d : ℕ} {X : Type*} [AddAction (Lattice d) X]
    (x y : X) : Prop :=
  ∃ i : Fin d, unitVector i +ᵥ x = y ∨ unitVector i +ᵥ y = x

theorem unitVector_ne_zero {d : ℕ} (i : Fin d) : unitVector i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [unitVector] at hi

theorem StandardEdge.symm {d : ℕ} {X : Type*} [AddAction (Lattice d) X]
    {x y : X} (h : StandardEdge (d := d) x y) : StandardEdge (d := d) y x := by
  obtain ⟨i, h | h⟩ := h
  · exact ⟨i, Or.inr h⟩
  · exact ⟨i, Or.inl h⟩

/-- The literal standard simple Schreier graph of a free lattice action. -/
def standardSchreierGraph {d : ℕ} {X : Type*} [AddAction (Lattice d) X]
    (free : IsFree (G := Lattice d) (X := X)) : SimpleGraph X where
  Adj := StandardEdge (d := d)
  symm := fun _ _ h => h.symm
  loopless := by
    constructor
    rintro x ⟨i, h | h⟩ <;> exact unitVector_ne_zero i (free _ _ h)

def HasContinuousHom {d : ℕ} {X V : Type*}
    [AddAction (Lattice d) X] [TopologicalSpace X] [TopologicalSpace V]
    (H : SimpleGraph V) : Prop :=
  ∃ c : X → V, Continuous c ∧ ∀ x y, StandardEdge (d := d) x y → H.Adj (c x) (c y)

/-- The adjacency formulation used below is equivalent to an actual continuous
mathlib graph homomorphism from the standard Schreier graph. -/
theorem hasContinuousHom_iff_graphHom {d : ℕ} {X V : Type*}
    [AddAction (Lattice d) X] [TopologicalSpace X] [TopologicalSpace V]
    (H : SimpleGraph V) (free : IsFree (G := Lattice d) (X := X)) :
    HasContinuousHom (d := d) (X := X) H ↔
      ∃ c : standardSchreierGraph free →g H, Continuous (c : X → V) := by
  constructor
  · rintro ⟨c, hc, he⟩
    exact ⟨⟨c, fun h => he _ _ h⟩, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc, fun _ _ h => c.map_rel h⟩

theorem hasContinuousHom_of_positive {d : ℕ} {X V : Type*}
    [AddAction (Lattice d) X] [TopologicalSpace X] [TopologicalSpace V]
    {H : SimpleGraph V} (c : X → V) (hc : Continuous c)
    (he : ∀ x (i : Fin d), H.Adj (c x) (c (unitVector i +ᵥ x))) :
    HasContinuousHom (d := d) (X := X) H := by
  refine ⟨c, hc, ?_⟩
  rintro x y ⟨i, h | h⟩
  · simpa [h] using he x i
  · simpa [h] using (he y i).symm

abbrev ShiftSpace (d : ℕ) := Lattice d → Bool

def shift {d : ℕ} (g : Lattice d) (x : ShiftSpace d) : ShiftSpace d :=
  fun u => x (u + g)

instance shiftAction (d : ℕ) : AddAction (Lattice d) (ShiftSpace d) where
  vadd := shift
  zero_vadd x := by
    change shift 0 x = x
    ext u
    simp [shift]
  add_vadd g h x := by
    change shift (g + h) x = shift g (shift h x)
    ext u
    simp [shift, add_comm, add_left_comm]

def FreeShift (d : ℕ) :=
  {x : ShiftSpace d // ∀ g : Lattice d, shift g x = x → g = 0}

instance freeShiftTopology (d : ℕ) : TopologicalSpace (FreeShift d) :=
  TopologicalSpace.induced (fun x : FreeShift d => x.val) inferInstance

instance freeShiftAction (d : ℕ) : AddAction (Lattice d) (FreeShift d) where
  vadd g x := ⟨shift g x.val, by
    intro h hh
    apply x.property h
    funext u
    have hp := congrFun hh (u - g)
    change x.val ((u - g + h) + g) = x.val ((u - g) + g) at hp
    rw [add_right_comm (u - g) h g, sub_add_cancel] at hp
    exact hp⟩
  zero_vadd x := by
    apply Subtype.ext
    change shift 0 x.val = x.val
    ext u
    simp [shift]
  add_vadd g h x := by
    apply Subtype.ext
    change shift (g + h) x.val = shift g (shift h x.val)
    ext u
    simp [shift, add_comm, add_left_comm]

theorem freeShift_isFree (d : ℕ) : IsFree (G := Lattice d) (X := FreeShift d) := by
  intro g x hx
  exact x.property g (congrArg Subtype.val hx)

theorem continuous_shift {d : ℕ} (g : Lattice d) :
    Continuous (shift g : ShiftSpace d → ShiftSpace d) := by
  apply continuous_pi
  intro u
  exact continuous_apply (u + g)

instance shiftContinuousVAdd (d : ℕ) : ContinuousVAdd (Lattice d) (ShiftSpace d) where
  continuous_vadd := continuous_prod_of_discrete_left.mpr (fun g => continuous_shift g)

instance freeShiftContinuousVAdd (d : ℕ) : ContinuousVAdd (Lattice d) (FreeShift d) where
  continuous_vadd := by
    apply continuous_induced_rng.mpr
    have hf : Continuous (fun x : FreeShift d => x.val) := continuous_induced_dom
    exact (continuous_vadd (M := Lattice d) (X := ShiftSpace d)).comp
      (continuous_fst.prodMk (hf.comp continuous_snd))

/-- The paper's class `𝓗_d`, for a fixed finite discrete target carrier. -/
def InClass (d : ℕ) {V : Type*} [TopologicalSpace V] (H : SimpleGraph V) : Prop :=
  HasContinuousHom (d := d) (X := FreeShift d) H

/-- Conclusion common to Theorem 1.4 and Proposition 7.1, at universe `u`. -/
def UniversalTarget.{u} (d : ℕ) {V : Type*} [TopologicalSpace V]
    (H : SimpleGraph V) : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [PolishSpace X]
    [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X],
    ZeroDimensional X → IsFree (G := Lattice d) (X := X) →
      HasContinuousHom (d := d) (X := X) H

end AbelianTargets
