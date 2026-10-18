import AbelianTargets.MarkerAtlasSideBounds
import AbelianTargets.IntegerPrismChart

namespace AbelianTargets
noncomputable section
open scoped NNReal

theorem integer_width_lower_from_cut_separation (L P : ℕ) (hP : 0<P) (A B : ℤ)
    (hAB : A<B) (hsep : ((L/(16*P) : ℕ) : ℤ)<B-A) :
    (L : ℝ≥0)/(32*(P : ℝ≥0))≤((B : ℝ)-(A : ℝ)).toNNReal := by
  let w := (B-A).toNat
  have hw : (w : ℤ)=B-A := Int.toNat_of_nonneg (by omega)
  have hnat : L/(16*P)<w := by exact_mod_cast (hw ▸ hsep)
  have hmul : L<16*P*w := by simpa only [Nat.mul_comm] using (@Nat.div_lt_iff_lt_mul (16*P) L w (by positivity)).mp hnat
  have hwreal : (w : ℝ)=(B : ℝ)-(A : ℝ) := by exact_mod_cast hw
  have hreal : (L : ℝ)<16*(P : ℝ)*((B : ℝ)-(A : ℝ)) := by
    have hh : (L : ℝ)<(16*P*w : ℕ) := by exact_mod_cast hmul
    simpa only [Nat.cast_mul,Nat.cast_ofNat,hwreal,mul_assoc] using hh
  have hwidth : 0<(B : ℝ)-(A : ℝ) := sub_pos.mpr (by exact_mod_cast hAB)
  have hp : 0<(P : ℝ) := by exact_mod_cast hP
  have hh : ((L : ℝ≥0)/(32*(P : ℝ≥0)) : ℝ)≤
      (((B : ℝ)-(A : ℝ)).toNNReal : ℝ) := by
    simp only [NNReal.coe_div,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast,
      Real.coe_toNNReal _ hwidth.le]
    apply (div_le_iff₀ (by positivity : 0<(32 : ℝ)*(P : ℝ))).mpr
    nlinarith
  exact_mod_cast hh

theorem ContinuousMarkerBoxes.atlas_quantitative_widths
    {d : ℕ} {L : Fin d→ℕ} {X : Type*} [TopologicalSpace X]
    [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
    {M : AnisotropicClopenMarkers d L X} {S : ℕ}
    (B : ContinuousMarkerBoxes M S) (hL : ∀i,1≤L i) (hS : 24≤S) (x : X)
    {R : RectangularCell d} (hR : R∈B.atlasCells hL (by omega) x) (j : Fin d) :
    (R.lower j<R.upper j → (L j : ℝ≥0)/(32*((2*S+1)^d : ℕ))≤(R.transverseWidth j).toNNReal) ∧
      (R.transverseWidth j).toNNReal≤6*(L j : ℝ≥0) := by
  constructor
  · intro hj
    have hb := B.atlas_side_bounds hL hS x hR j hj
    exact integer_width_lower_from_cut_separation (L j) ((2*S+1)^d) (by positivity) _ _ hj hb.1
  · have hb := (B.tiling hL (by omega) x).cells_bounded hR j
    have hw : 0≤R.transverseWidth j := sub_nonneg.mpr (by exact_mod_cast R.ordered j)
    have hh : ((R.transverseWidth j).toNNReal : ℝ)≤(6*(L j : ℝ≥0) : ℝ) := by
      rw [Real.coe_toNNReal _ hw]
      dsimp [RectangularCell.transverseWidth]
      have hbReal : ((R.upper j - R.lower j : ℤ) : ℝ)≤((6*L j : ℕ) : ℝ) := by exact_mod_cast hb
      simpa only [Int.cast_sub,Nat.cast_mul,Nat.cast_ofNat,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast] using hbReal
    exact_mod_cast hh

end
end AbelianTargets



