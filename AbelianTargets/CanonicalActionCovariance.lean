import AbelianTargets.CanonicalAtlasCovariance
import AbelianTargets.CanonicalProjectedOrigin
import AbelianTargets.ComputedProjectedCovariance
import AbelianTargets.MarkerAtlasCovariance
import AbelianTargets.ProjectedAtlasEstimates
import AbelianTargets.ParityFields

/-!
# Action covariance and integer-lattice parity closing

The actual canonical atlas projection commutes with repointing by the lattice
shift and the corresponding support-shore parity. Integer-lattice unit edges
suffice for the final generator comparison after the parity shear.
-/

namespace AbelianTargets
noncomputable section
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A tiling has only one data field; the remaining fields are proofs. -/
theorem IntegerRectangularTiling.eq_of_tiles_eq
    {d : ℕ} {K₀ : Fin d → ℕ}
    (T U : IntegerRectangularTiling d K₀) (h : T.tiles = U.tiles) :
    T = U := by
  cases T
  cases U
  cases h
  rfl

/-- Transport the existing canonical covariance theorem along a tiling
identity before projecting. The contraction family is the same on both sides. -/
theorem canonicalProjectedSkeleton_translate
    {d K S : ℕ} {K₀ : Fin d → ℕ}
    {T U : IntegerRectangularTiling d K₀}
    {W : Type*} [Fintype W] {G : SimpleGraph W}
    (D₀ : SupportTorsionData G) {i : Fin d} {J : ℝ≥0}
    (H : IntervalCarriers.NormalizedContractionFamily
      (2 * D₀.power + 1) K S J)
    (hS : K₀ i ≤ S) (δ V : Fin d → ℝ≥0) (hδ : ∀ j, 0 < δ j)
    (hlT : ∀ R, R ∈ T.cells → ∀ j, R.lower j < R.upper j →
      δ j ≤ (R.transverseWidth j).toNNReal)
    (huT : ∀ R, R ∈ T.cells → ∀ j,
      (R.transverseWidth j).toNNReal ≤ V j)
    (hlU : ∀ R, R ∈ U.cells → ∀ j, R.lower j < R.upper j →
      δ j ≤ (R.transverseWidth j).toNNReal)
    (huU : ∀ R, R ∈ U.cells → ∀ j,
      (R.transverseWidth j).toNNReal ≤ V j)
    (a : Lattice d) (hU : U = T.translate a) (z : RealCoordinates d) :
    (actualQuantitativeSkeleton δ V (IntervalCarriers.uniformCarrierSpeed
      (2 * D₀.power + 1) K) J hδ hlU huU
      (canonicalAtlasContractionProvider H U i hS) (d + 1)).toSkeletonCarrierMaps.projectedMap
        D₀ (translateCoordinates a z) =
      SupportPair.paritySwap G (a i)
        ((actualQuantitativeSkeleton δ V (IntervalCarriers.uniformCarrierSpeed
          (2 * D₀.power + 1) K) J hδ hlT huT
          (canonicalAtlasContractionProvider H T i hS) (d + 1)).toSkeletonCarrierMaps.projectedMap
            D₀ z) := by
  subst U
  exact SkeletonCarrierMaps.TranslationCovariant.projectedMap_eq D₀
    (canonicalQuantitativeSkeleton_translate H hS δ V hδ hlT huT a hlU huU
      (d + 1)) z

section Action
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X]
variable [ContinuousVAdd (Lattice d) X]
variable {M₀ : AnisotropicClopenMarkers d L X} {S : ℕ}
variable {W : Type*} [Fintype W] {G : SimpleGraph W}

/-- Repointing by t subtracts t from the pointed atlas; translating back
by t recovers the original tiling, including its dependent proof fields. -/
theorem ContinuousMarkerBoxes.tiling_translate_repoint
    (B : ContinuousMarkerBoxes M₀ S) (hL : ∀ j, 1 ≤ L j) (hS : 6 ≤ S)
    (x : X) (t : Lattice d) :
    (B.tiling hL hS (t +ᵥ x)).translate t = B.tiling hL hS x := by
  apply IntegerRectangularTiling.eq_of_tiles_eq
  exact B.retainedTiles_repoint x t

/-- Covariance of the actual canonical projected map, not an assumed
covariance field of a newly introduced orbit-map structure. -/
theorem ContinuousMarkerBoxes.canonicalProjectedMap_repoint
    (B : ContinuousMarkerBoxes M₀ S) (D₀ : SupportTorsionData G)
    (hL : ∀ j, 1 ≤ L j) (hS : 24 ≤ S) (K : ℕ) (i : Fin d) (J : ℝ≥0)
    (H : IntervalCarriers.NormalizedContractionFamily
      (2 * D₀.power + 1) K (6 * L i) J)
    (x : X) (t : Lattice d) (z : RealCoordinates d) :
    B.canonicalProjectedMap D₀ hL hS K i J H x (translateCoordinates t z) =
      SupportPair.paritySwap G (t i)
        (B.canonicalProjectedMap D₀ hL hS K i J H (t +ᵥ x) z) := by
  let δ : Fin d → ℝ≥0 := fun j => (L j : ℝ≥0) / (32 * ((2 * S + 1) ^ d : ℕ))
  let V : Fin d → ℝ≥0 := fun j => 6 * (L j : ℝ≥0)
  have hδ : ∀ j, 0 < δ j := by
    intro j
    have hj : 0 < L j := by have := hL j; omega
    dsimp [δ]
    positivity
  have hl (y : X) : ∀ R, R ∈ (B.tiling hL (by omega) y).cells →
      ∀ j, R.lower j < R.upper j → δ j ≤ (R.transverseWidth j).toNNReal := by
    intro R hR j hj
    exact (B.atlas_quantitative_widths hL hS y hR j).1 hj
  have hu (y : X) : ∀ R, R ∈ (B.tiling hL (by omega) y).cells →
      ∀ j, (R.transverseWidth j).toNNReal ≤ V j := by
    intro R hR j
    exact (B.atlas_quantitative_widths hL hS y hR j).2
  simpa only [canonicalProjectedMap, canonicalQuantitativeSkeleton, quantitativeSkeleton]
    using canonicalProjectedSkeleton_translate D₀ H (by rfl) δ V hδ
      (hl (t +ᵥ x)) (hu (t +ᵥ x)) (hl x) (hu x) t
      (B.tiling_translate_repoint hL (by omega) x t).symm z

/-- The same identity in the orientation used by the parity-map interface. -/
theorem ContinuousMarkerBoxes.canonicalProjectedMap_repoint_forward
    (B : ContinuousMarkerBoxes M₀ S) (D₀ : SupportTorsionData G)
    (hL : ∀ j, 1 ≤ L j) (hS : 24 ≤ S) (K : ℕ) (i : Fin d) (J : ℝ≥0)
    (H : IntervalCarriers.NormalizedContractionFamily
      (2 * D₀.power + 1) K (6 * L i) J)
    (x : X) (t : Lattice d) (z : RealCoordinates d) :
    B.canonicalProjectedMap D₀ hL hS K i J H (t +ᵥ x) z =
      SupportPair.paritySwap G (t i)
        (B.canonicalProjectedMap D₀ hL hS K i J H x (translateCoordinates t z)) := by
  have hh := B.canonicalProjectedMap_repoint D₀ hL hS K i J H x t z
  by_cases ht : t i % 2 = 0
  · simpa [SupportPair.paritySwap, ht] using hh.symm
  · simpa [SupportPair.paritySwap, ht, SupportPair.swap_swap]
      using (congrArg (SupportPair.swap G) hh).symm

end Action

/-- The existing interval estimate suffices for an edge based at any
integer lattice point; no bound for arbitrary real starting points is needed. -/
theorem QuantitativeEndpointSkeletonCarrierMaps.projected_lattice_step_close
    {d K : ℕ} {K₀ : Fin d → ℕ} {T : IntegerRectangularTiling d K₀}
    {W : Type*} [Fintype W] {G : SimpleGraph W}
    (D₀ : SupportTorsionData G) {i : Fin d} {C : Fin d → ℝ≥0}
    (F : QuantitativeEndpointSkeletonCarrierMaps T (2 * D₀.power + 1) K i (d + 1) C)
    (ε δ : ℝ)
    (hmod : ∀ A B : ℤ,
      ∀ p q : IntervalCarriers.Realization (2 * D₀.power + 1) K A B,
      dist p q < δ →
        dist (D₀.carrierProjection K A B p) (D₀.carrierProjection K A B q) < ε)
    (j : Fin d) (g : Lattice d) (hsmall : (C j : ℝ) < δ) :
    dist (F.toSkeletonCarrierMaps.projectedMap D₀ (fun k => (g k : ℝ)))
      (F.toSkeletonCarrierMaps.projectedMap D₀
        (fun k => ((g + unitVector j) k : ℝ))) < ε := by
  classical
  have h₀ : Function.update (fun k => (g k : ℝ)) j (g j : ℝ) =
      (fun k => (g k : ℝ)) := by
    funext k
    by_cases hk : k = j <;> simp [Function.update, hk]
  have h₁ : Function.update (fun k => (g k : ℝ)) j ((g j : ℝ) + 1) =
      (fun k => ((g + unitVector j) k : ℝ)) := by
    funext k
    by_cases hk : k = j <;> simp [Function.update, unitVector, hk]
  simpa only [h₀, h₁] using
    F.projected_integer_step_close D₀ ε δ hmod j (fun k => (g k : ℝ)) (g j) hsmall


/-- Lattice-only closing: the original generators become either one or two
integer unit steps under the parity shear. This deliberately does not ask
for a global projected Lipschitz estimate or steps from every real point.
The construction premise remains explicit and must still be instantiated. -/
theorem approximateParityMaps_of_latticeOrbitConstruction
    {d : ℕ} {X Y : Type*} [TopologicalSpace X]
    [AddAction (Lattice d) X] [MetricSpace Y]
    {τ : Y → Y} (hd : 1 ≤ d) (hτ : Isometry τ)
    (construction : ∀ ε : ℝ, 0 < ε → ∃ F : X → Lattice d → Y,
      Continuous (fun x => F x 0) ∧
      (Set.range (fun x => F x 0)).Finite ∧
      (∀ x i, F (unitVector i +ᵥ x) 0 =
        τ (F x (shearCoordinates hd (unitVector i)))) ∧
      ∀ x i g, dist (F x (g + unitVector i)) (F x g) < ε) :
    ApproximateParityMaps (d := d) X Y τ := by
  intro ε hε
  obtain ⟨F, hcont, hfinite, hcov, hstep⟩ := construction (ε / 2) (by positivity)
  refine ⟨fun x => F x 0, hcont, hfinite, ?_⟩
  intro x i
  change dist (F (unitVector i +ᵥ x) 0) (τ (F x 0)) < ε
  rw [hcov, hτ.dist_eq]
  have hfirst : dist (F x (unitVector (firstAxis hd))) (F x 0) < ε / 2 := by
    simpa using hstep x (firstAxis hd) 0
  by_cases hi : i = firstAxis hd
  · rw [hi, shearCoordinates_first_generator]
    exact hfirst.trans (by linarith)
  · rw [shearCoordinates_other_generator hd i hi]
    calc
      _ ≤ dist (F x (unitVector (firstAxis hd) + unitVector i))
            (F x (unitVector (firstAxis hd))) +
          dist (F x (unitVector (firstAxis hd))) (F x 0) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hstep x i (unitVector (firstAxis hd))) hfirst
      _ = ε := by ring

end
end AbelianTargets

namespace AbelianTargets

/-- The original space equipped with the lattice action pulled back along
the inverse parity shear. The underlying points and topology are unchanged. -/
def ParitySheared {d : ℕ} (_hd : 1 ≤ d) (X : Type*) := X

namespace ParitySheared

variable {d : ℕ} (hd : 1 ≤ d) {X : Type*}

def ofOriginal (x : X) : ParitySheared hd X := x

def toOriginal (x : ParitySheared hd X) : X := x

@[simp] theorem toOriginal_ofOriginal (x : X) :
    toOriginal hd (ofOriginal hd x) = x := rfl

@[simp] theorem ofOriginal_toOriginal (x : ParitySheared hd X) :
    ofOriginal hd (toOriginal hd x) = x := rfl

instance [TopologicalSpace X] : TopologicalSpace (ParitySheared hd X) :=
  inferInstanceAs (TopologicalSpace X)

instance [TopologicalSpace X] [PolishSpace X] : PolishSpace (ParitySheared hd X) :=
  inferInstanceAs (PolishSpace X)

theorem continuous_ofOriginal [TopologicalSpace X] :
    Continuous (ofOriginal hd : X → ParitySheared hd X) := continuous_id

theorem continuous_toOriginal [TopologicalSpace X] :
    Continuous (toOriginal hd : ParitySheared hd X → X) := continuous_id

theorem zeroDimensional [TopologicalSpace X] (hX : ZeroDimensional X) :
    ZeroDimensional (ParitySheared hd X) := hX

instance [AddAction (Lattice d) X] : AddAction (Lattice d) (ParitySheared hd X) where
  vadd g x := ofOriginal hd ((parityCoordinateEquiv hd).symm g +ᵥ toOriginal hd x)
  zero_vadd x := by
    change ofOriginal hd ((parityCoordinateEquiv hd).symm 0 +ᵥ toOriginal hd x) = x
    simp
  add_vadd g h x := by
    change ofOriginal hd ((parityCoordinateEquiv hd).symm (g+h) +ᵥ toOriginal hd x) =
      ofOriginal hd ((parityCoordinateEquiv hd).symm g +ᵥ
        ((parityCoordinateEquiv hd).symm h +ᵥ toOriginal hd x))
    rw [map_add, add_vadd]

@[simp] theorem toOriginal_vadd [AddAction (Lattice d) X]
    (g : Lattice d) (x : ParitySheared hd X) :
    toOriginal hd (g +ᵥ x) = (parityCoordinateEquiv hd).symm g +ᵥ toOriginal hd x := rfl

@[simp] theorem ofOriginal_vadd [AddAction (Lattice d) X]
    (g : Lattice d) (x : X) :
    ofOriginal hd (g +ᵥ x) = shearCoordinates hd g +ᵥ ofOriginal hd x := by
  change ofOriginal hd (g +ᵥ x) =
    ofOriginal hd ((parityCoordinateEquiv hd).symm (parityCoordinateEquiv hd g) +ᵥ x)
  rw [AddEquiv.symm_apply_apply]

instance [TopologicalSpace X] [AddAction (Lattice d) X]
    [ContinuousVAdd (Lattice d) X] : ContinuousVAdd (Lattice d) (ParitySheared hd X) where
  continuous_vadd := by
    apply continuous_prod_of_discrete_left.mpr
    intro g
    change Continuous (fun x : ParitySheared hd X =>
      ofOriginal hd ((parityCoordinateEquiv hd).symm g +ᵥ toOriginal hd x))
    exact (continuous_ofOriginal hd).comp
      ((continuous_const_vadd ((parityCoordinateEquiv hd).symm g)).comp
        (continuous_toOriginal hd))

theorem isFree [AddAction (Lattice d) X]
    (hX : IsFree (G := Lattice d) (X := X)) :
    IsFree (G := Lattice d) (X := ParitySheared hd X) := by
  intro g x hx
  have hfix : (parityCoordinateEquiv hd).symm g +ᵥ toOriginal hd x = toOriginal hd x :=
    congrArg (toOriginal hd) hx
  have hg := hX ((parityCoordinateEquiv hd).symm g) (toOriginal hd x) hfix
  apply (parityCoordinateEquiv hd).symm.injective
  simpa using hg

end ParitySheared
end AbelianTargets
