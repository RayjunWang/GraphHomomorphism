import AbelianTargets.ParityCoordinates
import AbelianTargets.AnisotropicScales
import AbelianTargets.SupportModel

/-!
# From controlled orbit maps to approximate parity fields

This checks the closing argument of Proposition 6.1. The geometric orbit
map is a visible input; the rectangular atlas and controlled carrier
extensions are not assumed as axioms or claimed to exist here.
-/

namespace AbelianTargets

noncomputable section

abbrev RealCoordinates (d : ℕ) := Fin d → ℝ

def realUnitVector {d : ℕ} (i : Fin d) : RealCoordinates d :=
  fun j => if j = i then 1 else 0

def parityStep {d : ℕ} (hd : 1 ≤ d) (i : Fin d) : RealCoordinates d :=
  if i = firstAxis hd then realUnitVector (firstAxis hd)
  else realUnitVector (firstAxis hd) + realUnitVector i

theorem parityStep_eq_shear_generator {d : ℕ} (hd : 1 ≤ d) (i : Fin d) :
    parityStep hd i = fun j => (shearCoordinates hd (unitVector i) j : ℝ) := by
  by_cases hi : i = firstAxis hd
  · subst i
    rw [shearCoordinates_first_generator]
    ext j
    simp [parityStep, realUnitVector, unitVector]
  · rw [shearCoordinates_other_generator hd i hi]
    ext j
    simp [parityStep, hi, realUnitVector, unitVector]

def anisotropicCoefficient {d : ℕ} (hd : 1 ≤ d)
    (A : ℝ) (B : ℕ → ℝ) (L M : ℕ) (i : Fin d) : ℝ :=
  if i = firstAxis hd then A * Real.log ((L : ℝ) + 2) / (L : ℝ)
  else B L / (M : ℝ)

/-- The actual projected orbit map data needed after Lemma 5.2.
All geometric and regularity obligations are explicit fields. -/
structure ProjectedAnisotropicMap
    {d : ℕ} {X Y : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]
    [MetricSpace Y] (τ : Y → Y) (hd : 1 ≤ d)
    (A : ℝ) (B : ℕ → ℝ) (L M : ℕ) where
  orbitMap : X → RealCoordinates d → Y
  continuous_origin : Continuous (fun x => orbitMap x 0)
  finite_range_origin : (Set.range (fun x => orbitMap x 0)).Finite
  covariance : ∀ x i, orbitMap (unitVector i +ᵥ x) 0 = τ (orbitMap x (parityStep hd i))
  coordinate_bound : ∀ x i u s,
    dist (orbitMap x (u + s • realUnitVector i)) (orbitMap x u) ≤
      anisotropicCoefficient hd A B L M i * |s|

theorem ProjectedAnisotropicMap.generator_error_bound
    {d : ℕ} {X Y : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]
    [MetricSpace Y] {τ : Y → Y} {hd : 1 ≤ d}
    {A : ℝ} {B : ℕ → ℝ} {L M : ℕ}
    (F : ProjectedAnisotropicMap τ hd A B L M) (hτ : Isometry τ)
    (hB : 0 ≤ B L) (hM : 1 ≤ M) (x : X) (i : Fin d) :
    dist (F.orbitMap (unitVector i +ᵥ x) 0) (τ (F.orbitMap x 0)) ≤
      A * Real.log ((L : ℝ) + 2) / (L : ℝ) + B L / (M : ℝ) := by
  rw [F.covariance, hτ.dist_eq]
  have hfirst : dist (F.orbitMap x (realUnitVector (firstAxis hd))) (F.orbitMap x 0) ≤
      A * Real.log ((L : ℝ) + 2) / (L : ℝ) := by
    simpa [anisotropicCoefficient] using F.coordinate_bound x (firstAxis hd) 0 1
  by_cases hi : i = firstAxis hd
  · rw [parityStep, if_pos hi]
    have hnonneg : 0 ≤ B L / (M : ℝ) := div_nonneg hB (by positivity)
    exact hfirst.trans (le_add_of_nonneg_right hnonneg)
  · rw [parityStep, if_neg hi]
    have htrans : dist (F.orbitMap x (realUnitVector (firstAxis hd) + realUnitVector i))
        (F.orbitMap x (realUnitVector (firstAxis hd))) ≤ B L / (M : ℝ) := by
      simpa [anisotropicCoefficient, hi] using
        F.coordinate_bound x i (realUnitVector (firstAxis hd)) 1
    calc
      dist (F.orbitMap x (realUnitVector (firstAxis hd) + realUnitVector i))
          (F.orbitMap x 0) ≤
          dist (F.orbitMap x (realUnitVector (firstAxis hd) + realUnitVector i))
            (F.orbitMap x (realUnitVector (firstAxis hd))) +
          dist (F.orbitMap x (realUnitVector (firstAxis hd))) (F.orbitMap x 0) :=
        dist_triangle _ _ _
      _ ≤ B L / (M : ℝ) + A * Real.log ((L : ℝ) + 2) / (L : ℝ) :=
        add_le_add htrans hfirst
      _ = _ := add_comm _ _

/-- A stronger global-coordinate construction interface, expressed before
graph rounding. The final proofs use integer-step bounds instead. This is
a proposition and is never installed as an axiom. -/
def AnisotropicParityConstruction
    {d : ℕ} (X Y : Type*) [TopologicalSpace X] [AddAction (Lattice d) X]
    [MetricSpace Y] (τ : Y → Y) (hd : 1 ≤ d) : Prop :=
  ∃ (A : ℝ) (B : ℕ → ℝ) (L₀ M₀ : ℕ), (∀ L, 0 ≤ B L) ∧
    ∀ L M, 1 ≤ L → L₀ ≤ L → 1 ≤ M → M₀ ≤ M →
      Nonempty (ProjectedAnisotropicMap (X := X) τ hd A B L M)

/-- Complete closing deduction of Proposition 6.1 from explicit geometric
orbit-map data, using the successive scale choice proved above. -/
theorem approximateParityMaps_of_anisotropicConstruction
    {d : ℕ} {X Y : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]
    [MetricSpace Y] {τ : Y → Y} {hd : 1 ≤ d}
    (hτ : Isometry τ) (construction : AnisotropicParityConstruction X Y τ hd) :
    ApproximateParityMaps (d := d) X Y τ := by
  obtain ⟨A, B, L₀, M₀, hB, hmaps⟩ := construction
  intro ε hε
  obtain ⟨L, M, hL, hL₀, hM, hM₀, herror⟩ := exists_anisotropic_scales A B L₀ M₀ hε
  obtain ⟨F⟩ := hmaps L M hL hL₀ hM hM₀
  refine ⟨fun x => F.orbitMap x 0, F.continuous_origin, F.finite_range_origin, ?_⟩
  intro x i
  exact (F.generator_error_bound hτ (hB L) hM x i).trans_lt herror

end

end AbelianTargets
