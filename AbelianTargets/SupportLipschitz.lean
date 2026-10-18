import AbelianTargets.SupportGeometry
import AbelianTargets.FixedSlotInterpolation

/-!
# Quantitative affine homotopies in support carriers

Probability coordinates isometrically embed the support complex into a
finite real normed space. Interpolation in a biclique carrier does not
increase a common path-time Lipschitz bound.
-/

namespace AbelianTargets.SupportPair

open scoped NNReal

noncomputable section

variable {V : Type*} [Fintype V] (H : SimpleGraph V)

abbrev Ambient := (V → ℝ) × (V → ℝ)

def ambient (z : SupportPair H) : Ambient (V := V) := ((left H z).mass,(right H z).mass)

theorem isometry_ambient : Isometry (ambient H) := by
  intro z w
  rfl

theorem ambient_carrierMix {A B : Set V} (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b)
    (z w : SupportPair H) (hz : InCarrier H A B z) (hw : InCarrier H A B w) (r : unitInterval) :
    ambient H (carrierMix H hAB z w hz hw r) = FixedSlots.mix (ambient H z) (ambient H w) r := by
  apply Prod.ext <;> funext v <;> rfl

theorem carrierMix_dist_le {A B : Set V} (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b)
    (z w z' w' : SupportPair H)
    (hz : InCarrier H A B z) (hw : InCarrier H A B w)
    (hz' : InCarrier H A B z') (hw' : InCarrier H A B w') (r : unitInterval) :
    dist (carrierMix H hAB z w hz hw r) (carrierMix H hAB z' w' hz' hw' r) ≤
      (1-(r : ℝ))*dist z z' + (r : ℝ)*dist w w' := by
  rw [← (isometry_ambient H).dist_eq, ambient_carrierMix, ambient_carrierMix]
  simpa only [(isometry_ambient H).dist_eq] using
    FixedSlots.mix_dist_le (ambient H z) (ambient H z') (ambient H w) (ambient H w') r

theorem carrierMix_parameter_lipschitz {A B : Set V}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b) (z w : SupportPair H)
    (hz : InCarrier H A B z) (hw : InCarrier H A B w) (K : ℝ≥0) (hzw : dist z w ≤ K) :
    LipschitzWith K (carrierMix H hAB z w hz hw) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  rw [← (isometry_ambient H).dist_eq, ambient_carrierMix, ambient_carrierMix]
  exact (FixedSlots.mix_lipschitz (ambient H z) (ambient H w) K
    (by simpa only [(isometry_ambient H).dist_eq] using hzw)).dist_le_mul r s

/-- The explicit carrier homotopy keeps a common Lipschitz constant in
the path parameter at every homotopy parameter. -/
theorem carrierHomotopy_path_time_lipschitz {A B : Set V}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b) {p q : SupportPair H}
    (P Q : Path p q) (hP : ∀ t, InCarrier H A B (P t)) (hQ : ∀ t, InCarrier H A B (Q t))
    (K : ℝ≥0) (hPL : LipschitzWith K P) (hQL : LipschitzWith K Q) (r : unitInterval) :
    LipschitzWith K ((carrierHomotopy H hAB P Q hP hQ).eval r) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hc := carrierMix_dist_le H hAB (P u) (Q u) (P v) (Q v)
    (hP u) (hQ u) (hP v) (hQ v) r
  calc
    _ ≤ (1-(r : ℝ))*dist (P u) (P v) + (r : ℝ)*dist (Q u) (Q v) := hc
    _ ≤ (1-(r : ℝ))*(K*dist u v) + (r : ℝ)*(K*dist u v) :=
      add_le_add (mul_le_mul_of_nonneg_left (hPL.dist_le_mul u v) (sub_nonneg.mpr r.property.2))
        (mul_le_mul_of_nonneg_left (hQL.dist_le_mul u v) r.property.1)
    _ = K*dist u v := by ring

theorem dist_le_one (z w : SupportPair H) : dist z w ≤ 1 := by
  have hp : ∀ p q : Probability V, dist p q ≤ 1 := by
    intro p q
    change dist p.mass q.mass ≤ 1
    apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).2
    intro v
    rw [Real.dist_eq, abs_le]
    constructor
    · have h₀ := p.nonneg v
      have h₁ := q.mass_le_one v
      linarith
    · have h₀ := q.nonneg v
      have h₁ := p.mass_le_one v
      linarith
  change max (dist (left H z) (left H w)) (dist (right H z) (right H w)) ≤ 1
  exact max_le (hp _ _) (hp _ _)

/-- One of the actual product-simplex faces of the support complex. -/
abbrev Face (A B : Set V) := {z : SupportPair H // InCarrier H A B z}

def faceContractionMap {A B : Set V} (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b)
    (p : Face H A B) (z : Face H A B × unitInterval) : Face H A B :=
  ⟨carrierMix H hAB z.1.1 p.1 z.1.2 p.2 z.2,
    carrierMix_inCarrier H hAB z.1.1 p.1 z.1.2 p.2 z.2⟩

theorem faceContractionMap_continuous {A B : Set V}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b) (p : Face H A B) :
    Continuous (faceContractionMap H hAB p) := by
  apply Continuous.subtype_mk
  exact continuous_carrierMix H hAB (fun z => z.1.2) (fun _ => p.2)
    (continuous_subtype_val.comp continuous_fst) continuous_const continuous_snd

theorem faceContractionMap_track {A B : Set V}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b) (p z : Face H A B) :
    LipschitzWith 1 (fun r => faceContractionMap H hAB p (z,r)) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  exact (carrierMix_parameter_lipschitz H hAB z.1 p.1 z.2 p.2 1
    (dist_le_one H z.1 p.1)).dist_le_mul r s

theorem faceContractionMap_joint {A B : Set V}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b) (p : Face H A B) :
    LipschitzWith 2 (faceContractionMap H hAB p) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨z,r⟩ ⟨w,s⟩
  let F := faceContractionMap H hAB p
  have hpoint : dist (F (z,r)) (F (w,r)) ≤ dist z w := by
    have he := carrierMix_dist_le H hAB z.1 p.1 w.1 p.1 z.2 p.2 w.2 p.2 r
    calc
      _ ≤ (1-(r : ℝ))*dist z w + (r : ℝ)*dist p.1 p.1 := he
      _ ≤ dist z w := by
        simp only [dist_self, mul_zero, add_zero]
        have hr := r.property.1
        have hd : 0 ≤ dist z w := dist_nonneg
        nlinarith
  have htime : dist (F (w,r)) (F (w,s)) ≤ dist r s := by
    simpa only [NNReal.coe_one, one_mul] using
      (faceContractionMap_track H hAB p w).dist_le_mul r s
  calc
    _ ≤ dist (F (z,r)) (F (w,r)) + dist (F (w,r)) (F (w,s)) := dist_triangle _ _ _
    _ ≤ dist z w + dist r s := add_le_add hpoint htime
    _ ≤ 2*dist (z,r) (w,s) := by
      change dist z w + dist r s ≤ 2*max (dist z w) (dist r s)
      have h₀ := le_max_left (dist z w) (dist r s)
      have h₁ := le_max_right (dist z w) (dist r s)
      linarith

/-- A concrete controlled contraction, with track speed one and joint
Lipschitz constant two, for every biclique face of the support complex. -/
def faceControlledContraction {A B : Set V}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b) (p : Face H A B) :
    ControlledContraction p 1 2 where
  map := faceContractionMap H hAB p
  continuous := faceContractionMap_continuous H hAB p
  at_zero z := by
    apply Subtype.ext
    exact carrierMix_zero H hAB z.1 p.1 z.2 p.2
  at_one z := by
    apply Subtype.ext
    exact carrierMix_one H hAB z.1 p.1 z.2 p.2
  fixes r := by
    apply Subtype.ext
    exact carrierMix_self H hAB p.1 p.2 p.2 r
  track := faceContractionMap_track H hAB p
  joint := faceContractionMap_joint H hAB p

end

end AbelianTargets.SupportPair
