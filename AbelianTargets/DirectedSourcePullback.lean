import AbelianTargets.EvenFiniteSources

/-!
# Directed twelve-tile sources on coordinate subgroup actions

The full `2k`-dimensional free shift restricts to a free action of each
two-dimensional coordinate subgroup. The finite-pattern version of
Bernshteyn's universality theorem transfers GJKS's directed source map to
these genuine subgroup actions. All coordinate and freeness bookkeeping
below is proved in Lean.
-/

namespace AbelianTargets

def blockEmbedding {k : ℕ} (i : Fin k) (g : Lattice 2) : Lattice (2 * k) :=
  fun a => if ((blockIndex k).symm a).1 = i then g ((blockIndex k).symm a).2 else 0

@[simp] theorem blockEmbedding_apply {k : ℕ} (i a : Fin k) (g : Lattice 2) (j : Fin 2) :
    blockEmbedding i g (blockIndex k (a, j)) = if a = i then g j else 0 := by
  simp [blockEmbedding]

@[simp] theorem blockEmbedding_zero {k : ℕ} (i : Fin k) :
    blockEmbedding i (0 : Lattice 2) = 0 := by
  funext a
  simp [blockEmbedding]

@[simp] theorem blockEmbedding_add {k : ℕ} (i : Fin k) (g h : Lattice 2) :
    blockEmbedding i (g + h) = blockEmbedding i g + blockEmbedding i h := by
  funext a
  unfold blockEmbedding
  simp only [Pi.add_apply]
  split_ifs <;> simp

@[simp] theorem blockVector_blockEmbedding {k : ℕ} (i : Fin k) (g : Lattice 2) :
    blockVector (blockEmbedding i g) i = g := by
  funext j
  simp [blockVector]

theorem blockEmbedding_eq_zero {k : ℕ} (i : Fin k) (g : Lattice 2)
    (h : blockEmbedding i g = 0) : g = 0 := by
  have hg := congrArg (fun t => blockVector t i) h
  simpa using hg

@[simp] theorem blockEmbedding_unit {k : ℕ} (i : Fin k) (j : Fin 2) :
    blockEmbedding i (unitVector j) = unitVector (blockIndex k (i, j)) := by
  classical
  funext a
  obtain ⟨⟨b, l⟩, rfl⟩ := (blockIndex k).surjective a
  simp [unitVector, (blockIndex k).injective.eq_iff]
  by_cases hbi : b = i
  · subst b
    simp
  · simp [hbi]

/-- A type synonym distinguishes the restricted subgroup action from
the original full-lattice action on the same topological space. -/
def BlockRestriction {k : ℕ} (X : Type*) (_i : Fin k) := X

def blockAct {k : ℕ} {X : Type*} [AddAction (Lattice (2 * k)) X]
    (i : Fin k) (g : Lattice 2) (x : X) : X := blockEmbedding i g +ᵥ x

instance blockRestrictionTopology {k : ℕ} {X : Type*} [TopologicalSpace X] (i : Fin k) :
    TopologicalSpace (BlockRestriction X i) := inferInstanceAs (TopologicalSpace X)

instance blockRestrictionPolish {k : ℕ} {X : Type*} [TopologicalSpace X] [PolishSpace X]
    (i : Fin k) : PolishSpace (BlockRestriction X i) := inferInstanceAs (PolishSpace X)

instance blockRestrictionAction {k : ℕ} {X : Type*} [AddAction (Lattice (2 * k)) X]
    (i : Fin k) : AddAction (Lattice 2) (BlockRestriction X i) where
  vadd g x := blockAct (X := X) i g x
  zero_vadd x := by change blockAct (X := X) i 0 x = x; simp [blockAct]
  add_vadd g h x := by
    change blockAct (X := X) i (g + h) x = blockAct (X := X) i g (blockAct (X := X) i h x)
    unfold blockAct
    rw [blockEmbedding_add, add_vadd]

instance blockRestrictionContinuousVAdd {k : ℕ} {X : Type*}
    [TopologicalSpace X] [AddAction (Lattice (2 * k)) X]
    [ContinuousVAdd (Lattice (2 * k)) X] (i : Fin k) :
    ContinuousVAdd (Lattice 2) (BlockRestriction X i) where
  continuous_vadd := continuous_prod_of_discrete_left.mpr (by
    intro g
    change Continuous (fun x : X => blockAct (X := X) i g x)
    exact continuous_const_vadd (blockEmbedding i g))

theorem blockRestriction_isFree {k : ℕ} {X : Type*}
    [AddAction (Lattice (2 * k)) X] (free : IsFree (G := Lattice (2 * k)) (X := X))
    (i : Fin k) : IsFree (G := Lattice 2) (X := BlockRestriction X i) := by
  intro g x hfix
  change blockAct (X := X) i g x = x at hfix
  exact blockEmbedding_eq_zero i g (free (blockEmbedding i g) (show X from x) hfix)

/-- Direction-preserving maps from an actual full free shift into every
twelve-tile factor, with the full standard generator indices displayed. -/
theorem exists_fullShift_directed_twelve_tile_factors
    (k : ℕ) (p q : Fin k → ℕ) (hp : ∀ i, 5 ≤ p i) (hq : ∀ i, 5 ≤ q i)
    (hcop : ∀ i, Nat.Coprime (p i) (q i)) :
    ∃ θ : (i : Fin k) → FreeShift (2 * k) → TwelveTiles.Vertex (p i) (q i),
      (∀ i, Continuous (θ i)) ∧
      (∀ i x, TwelveTiles.HorizontalStep (hp i) (hq i) (θ i x)
        (θ i (unitVector (blockIndex k (i, (0 : Fin 2))) +ᵥ x))) ∧
      (∀ i x, TwelveTiles.VerticalStep (hp i) (hq i) (θ i x)
        (θ i (unitVector (blockIndex k (i, (1 : Fin 2))) +ᵥ x))) := by
  classical
  have hf : ∀ i : Fin k, ∃ θ : FreeShift (2 * k) → TwelveTiles.Vertex (p i) (q i),
      Continuous θ ∧
      (∀ x, TwelveTiles.HorizontalStep (hp i) (hq i) (θ x)
        (θ (unitVector (blockIndex k (i, (0 : Fin 2))) +ᵥ x))) ∧
      (∀ x, TwelveTiles.VerticalStep (hp i) (hq i) (θ x)
        (θ (unitVector (blockIndex k (i, (1 : Fin 2))) +ᵥ x))) := by
    intro i
    obtain ⟨θ, hθ, hhor, hver⟩ :=
      @References.bernshteyn_directed_twelve_tiles_universality
        (p i) (q i) (hp i) (hq i)
        (References.gjks_direction_preserving_twelve_tiles (p i) (q i) (hp i) (hq i) (hcop i))
        (BlockRestriction (FreeShift (2 * k)) i)
        (blockRestrictionTopology i)
        (blockRestrictionPolish (X := FreeShift (2 * k)) i)
        (blockRestrictionAction i)
        (blockRestrictionContinuousVAdd i)
        (freeShift_zeroDimensional (2 * k))
        (blockRestriction_isFree (freeShift_isFree (2 * k)) i)
    refine ⟨θ, hθ, ?_, ?_⟩
    · intro x
      have h := hhor x
      change TwelveTiles.HorizontalStep (hp i) (hq i) (θ x)
        (θ (blockAct (X := FreeShift (2 * k)) i (unitVector (0 : Fin 2)) x)) at h
      simpa only [blockAct, blockEmbedding_unit] using h
    · intro x
      have h := hver x
      change TwelveTiles.VerticalStep (hp i) (hq i) (θ x)
        (θ (blockAct (X := FreeShift (2 * k)) i (unitVector (1 : Fin 2)) x)) at h
      simpa only [blockAct, blockEmbedding_unit] using h
  choose θ hθ hhor hver using hf
  exact ⟨θ, hθ, hhor, hver⟩

end AbelianTargets
