import AbelianTargets.MarkerAtlasQuantitativeWidths
import AbelianTargets.DeterministicQuantitativeAtlas
import AbelianTargets.AnisotropicRankRates

set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets
noncomputable section
open scoped NNReal
variable {d : ℕ} {L : Fin d→ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M₀ : AnisotropicClopenMarkers d L X} {S : ℕ}

/-- The actual retained marker atlas has a canonical quantitative rank builder.
Its only supplied data are the already constructed interval contractions. -/
def ContinuousMarkerBoxes.quantitativeSkeleton
    (B : ContinuousMarkerBoxes M₀ S) (hL : ∀j,1≤L j) (hS : 24≤S) (x : X)
    (m K : ℕ) (i : Fin d) (D J : ℝ≥0)
    (H : ∀R,R∈(B.tiling hL (by omega) x).cells → R.lower i<R.upper i →
      ControlledContraction (cellLeftPoint m K i R) D J) (n : ℕ) :
    QuantitativeEndpointSkeletonCarrierMaps (B.tiling hL (by omega) x) m K i n
      (atlasRankRates (fun j=>(L j : ℝ≥0)/(32*((2*S+1)^d : ℕ)))
        (fun j=>6*(L j : ℝ≥0)) D J i n) :=
  actualQuantitativeSkeleton _ _ D J (by
    intro j
    have hj : 0<L j := by have := hL j; omega
    positivity)
    (by intro R hR j hj; exact (B.atlas_quantitative_widths hL hS x hR j).1 hj)
    (by intro R hR j; exact (B.atlas_quantitative_widths hL hS x hR j).2) H n

/-- On anisotropic marker scales, the first coordinate loses only D/L;
the other coordinates lose a finite constant divided by M. -/
theorem ContinuousMarkerBoxes.quantitativeSkeleton_anisotropic_bounds
    (B : ContinuousMarkerBoxes M₀ S) (hL : ∀j,1≤L j) (hS : 24≤S) (x : X)
    (m K : ℕ) (i : Fin d) (D J : ℝ≥0)
    (H : ∀R,R∈(B.tiling hL (by omega) x).cells → R.lower i<R.upper i →
      ControlledContraction (cellLeftPoint m K i R) D J)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (hscales : ∀j,L j=if j=i then a else b)
    (n : ℕ) (R : RectangularCell d) (hR : R∈(B.tiling hL (by omega) x).cells)
    (hr : R.rank<n) (j : Fin d) (z z' : CellClosedDomain R)
    (heq : ∀k,k≠j→z.val k=z'.val k) :
    dist ((B.quantitativeSkeleton hL hS x m K i D J H n).map R hR hr z)
      ((B.quantitativeSkeleton hL hS x m K i D J H n).map R hR hr z')≤
      (if j=i then firstRankFactor ((2*S+1)^d : ℕ) n*D/(a : ℝ≥0)
        else transverseRankFactor ((2*S+1)^d : ℕ) d D J n/(b : ℝ≥0))*|z.val j-z'.val j| := by
  have hc := (B.quantitativeSkeleton hL hS x m K i D J H n).coordinate_bounds R hR hr j z z' heq
  have heLower : (fun j=>(L j : ℝ≥0)/(32*((2*S+1)^d : ℕ)))=
      anisotropicLowerRates i ((2*S+1)^d : ℕ) (a : ℝ≥0) (b : ℝ≥0) := by
    funext j
    simp only [anisotropicLowerRates,hscales j]
    split_ifs <;> rfl
  have heUpper : (fun j=>6*(L j : ℝ≥0))=anisotropicUpperRates i (a : ℝ≥0) (b : ℝ≥0) := by
    funext j
    simp only [anisotropicUpperRates,hscales j]
    split_ifs <;> rfl
  have hrates := anisotropic_rank_rates_bound i ((2*S+1)^d : ℕ) (a : ℝ≥0) (b : ℝ≥0) D J
    (by positivity) (by exact_mod_cast ha) (by exact_mod_cast hb) n j
  rw [←heLower,←heUpper] at hrates
  have hratesReal :
      (atlasRankRates (fun j=>(L j : ℝ≥0)/(32*((2*S+1)^d : ℕ)))
        (fun j=>6*(L j : ℝ≥0)) D J i n j : ℝ)≤
      (if j=i then firstRankFactor ((2*S+1)^d : ℕ) n*D/(a : ℝ≥0)
        else transverseRankFactor ((2*S+1)^d : ℕ) d D J n/(b : ℝ≥0) : ℝ≥0) := by
    exact_mod_cast hrates
  exact hc.trans (mul_le_mul_of_nonneg_right hratesReal (abs_nonneg _))

end
end AbelianTargets

