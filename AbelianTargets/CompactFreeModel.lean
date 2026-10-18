import AbelianTargets.FreeShiftTopology
import AbelianTargets.ThreeColoring
import Mathlib.Topology.Compactness.Compact

/-!
# A compact free lattice action recording displacement three-colorings

The space in Lemma 7.5 is constructed as a product of closed proper-coloring
subshifts, one layer for each nonzero displacement. The topology, action,
freeness and coding-map construction below are proved without new axioms.
-/

namespace AbelianTargets

open Topology

/-- A proper three-coloring of all edges of one displacement in a lattice. -/
abbrev DisplacementLayer {d : ℕ} (g : Lattice d) :=
  {z : Lattice d → Fin 3 // ∀ h, z h ≠ z (h + g)}

theorem displacementLayer_isClosed {d : ℕ} (g : Lattice d) :
    IsClosed {z : Lattice d → Fin 3 | ∀ h, z h ≠ z (h + g)} := by
  have heq : {z : Lattice d → Fin 3 | ∀ h, z h ≠ z (h + g)} =
      ⋂ h, (fun z : Lattice d → Fin 3 => (z h, z (h + g))) ⁻¹'
        {p : Fin 3 × Fin 3 | p.1 ≠ p.2} := by
    ext z
    simp
  rw [heq]
  apply isClosed_iInter
  intro h
  exact (isClosed_discrete _).preimage
    ((continuous_apply h).prodMk (continuous_apply (h + g)))

instance displacementLayerCompactSpace {d : ℕ} (g : Lattice d) :
    CompactSpace (DisplacementLayer g) :=
  isCompact_iff_compactSpace.mp (displacementLayer_isClosed g).isCompact

instance displacementLayerPolishSpace {d : ℕ} (g : Lattice d) :
    PolishSpace (DisplacementLayer g) := by
  letI : PolishSpace (Lattice d → Fin 3) := by constructor
  exact (displacementLayer_isClosed g).polishSpace

def displacementLayerShift {d : ℕ} {g : Lattice d}
    (k : Lattice d) (z : DisplacementLayer g) : DisplacementLayer g :=
  ⟨fun h => z.val (h + k), by
    intro h
    simpa only [add_assoc, add_comm, add_left_comm] using z.property (h + k)⟩

instance displacementLayerAction {d : ℕ} (g : Lattice d) :
    AddAction (Lattice d) (DisplacementLayer g) where
  vadd := displacementLayerShift
  zero_vadd z := by
    apply Subtype.ext
    funext h
    change z.val (h + 0) = z.val h
    rw [add_zero]
  add_vadd k l z := by
    apply Subtype.ext
    funext h
    change z.val (h + (k + l)) = z.val ((h + k) + l)
    rw [add_assoc]

theorem continuous_displacementLayerShift {d : ℕ} {g : Lattice d} (k : Lattice d) :
    Continuous (displacementLayerShift (g := g) k) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro h
  exact (continuous_apply (h + k)).comp continuous_subtype_val

instance displacementLayerContinuousVAdd {d : ℕ} (g : Lattice d) :
    ContinuousVAdd (Lattice d) (DisplacementLayer g) where
  continuous_vadd := continuous_prod_of_discrete_left.mpr
    (fun k => continuous_displacementLayerShift k)

/-- All nonzero displacement proper-coloring layers, as in Lemma 7.5. -/
abbrev CompactFreeModel (d : ℕ) :=
  (g : {g : Lattice d // g ≠ 0}) → DisplacementLayer g.val

instance compactFreeModelCompactSpace (d : ℕ) : CompactSpace (CompactFreeModel d) :=
  inferInstance

instance compactFreeModelPolishSpace (d : ℕ) : PolishSpace (CompactFreeModel d) := by
  constructor

theorem compactFreeModel_zeroDimensional (d : ℕ) : ZeroDimensional (CompactFreeModel d) :=
  isTopologicalBasis_isClopen

theorem compactFreeModel_isFree (d : ℕ) :
    IsFree (G := Lattice d) (X := CompactFreeModel d) := by
  intro g z hfix
  by_contra hg
  let i : {g : Lattice d // g ≠ 0} := ⟨g, hg⟩
  have heq := congrArg (fun p : CompactFreeModel d => (p i).val 0) hfix
  change (z i).val (0 + g) = (z i).val 0 at heq
  have hvalue : (z i).val g = (z i).val 0 := by
    simpa only [zero_add] using heq
  exact (z i).property 0 (by simpa only [zero_add] using hvalue.symm)

section Coding

variable {d : ℕ} {X : Type*} [TopologicalSpace X]
  [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]

/-- Convert one displacement coloring into its orbit-label layer. -/
def displacementLayerCoding {g : Lattice d} (c : X → Fin 3)
    (hproper : ∀ x, c (g +ᵥ x) ≠ c x) (x : X) : DisplacementLayer g :=
  ⟨fun h => c (h +ᵥ x), by
    intro h
    simpa only [add_vadd, add_comm] using (hproper (h +ᵥ x)).symm⟩

theorem continuous_displacementLayerCoding {g : Lattice d} (c : X → Fin 3)
    (hproper : ∀ x, c (g +ᵥ x) ≠ c x) (hc : Continuous c) :
    Continuous (displacementLayerCoding c hproper) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro h
  exact hc.comp (continuous_const_vadd h)

omit [TopologicalSpace X] [ContinuousVAdd (Lattice d) X] in
theorem displacementLayerCoding_equivariant {g : Lattice d} (c : X → Fin 3)
    (hproper : ∀ x, c (g +ᵥ x) ≠ c x) (k : Lattice d) (x : X) :
    displacementLayerCoding c hproper (k +ᵥ x) = k +ᵥ displacementLayerCoding c hproper x := by
  apply Subtype.ext
  funext h
  change c (h +ᵥ (k +ᵥ x)) = c ((h + k) +ᵥ x)
  rw [add_vadd]

/-- The map from a free zero-dimensional action to the compact model, when
its continuous proper three-colorings are supplied for each displacement. -/
def compactFreeCoding
    (c : (g : {g : Lattice d // g ≠ 0}) → X → Fin 3)
    (hproper : ∀ g x, c g (g.val +ᵥ x) ≠ c g x) : X → CompactFreeModel d :=
  fun x g => displacementLayerCoding (c g) (hproper g) x

theorem continuous_compactFreeCoding
    (c : (g : {g : Lattice d // g ≠ 0}) → X → Fin 3)
    (hproper : ∀ g x, c g (g.val +ᵥ x) ≠ c g x)
    (hc : ∀ g, Continuous (c g)) : Continuous (compactFreeCoding c hproper) := by
  exact continuous_pi (fun g => continuous_displacementLayerCoding (c g) (hproper g) (hc g))

omit [TopologicalSpace X] [ContinuousVAdd (Lattice d) X] in
theorem compactFreeCoding_equivariant
    (c : (g : {g : Lattice d // g ≠ 0}) → X → Fin 3)
    (hproper : ∀ g x, c g (g.val +ᵥ x) ≠ c g x) (k : Lattice d) (x : X) :
    compactFreeCoding c hproper (k +ᵥ x) = k +ᵥ compactFreeCoding c hproper x := by
  funext g
  exact displacementLayerCoding_equivariant (c g) (hproper g) k x

end Coding

/-- The delta configuration at the origin has no nonzero period. -/
def originFreeConfiguration (d : ℕ) : FreeShift d :=
  ⟨fun u => decide (u = 0), by
    intro g hfix
    have h := congrFun hfix 0
    have htrue : decide (g = 0) = true := by
      simpa only [shift, zero_add, decide_true] using h
    exact of_decide_eq_true htrue⟩

instance freeShiftNonempty (d : ℕ) : Nonempty (FreeShift d) := ⟨originFreeConfiguration d⟩

/-- Every free zero-dimensional Polish lattice action continuously and
equivariantly maps into the compact free model. This uses the proved
displacement three-coloring construction, rather than a reference axiom. -/
theorem exists_continuous_equivariant_compactFreeModel
    {d : ℕ} {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
    (hzero : ZeroDimensional X) (hfree : IsFree (G := Lattice d) (X := X)) :
    ∃ f : X → CompactFreeModel d, Continuous f ∧
      ∀ (g : Lattice d) (x : X), f (g +ᵥ x) = g +ᵥ f x := by
  classical
  have hcolor : ∀ g : {g : Lattice d // g ≠ 0},
      ∃ c : X → Fin 3, Continuous c ∧ ∀ x, c (g.val +ᵥ x) ≠ c x :=
    fun g => exists_continuous_displacement_three_coloring hzero hfree g.val g.property
  choose c hc hp using hcolor
  exact ⟨compactFreeCoding c hp, continuous_compactFreeCoding c hp hc,
    compactFreeCoding_equivariant c hp⟩

instance compactFreeModelNonempty (d : ℕ) : Nonempty (CompactFreeModel d) := by
  obtain ⟨f, _, _⟩ := exists_continuous_equivariant_compactFreeModel
    (freeShift_zeroDimensional d) (freeShift_isFree d)
  exact ⟨f (originFreeConfiguration d)⟩

end AbelianTargets
