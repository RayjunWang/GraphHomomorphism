import AbelianTargets.DeterministicAtlasLocality
import AbelianTargets.AtlasDependencyAgreement
import AbelianTargets.ProjectedAtlasMaps
import AbelianTargets.CanonicalMarkerQuantitativeAtlas

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AbelianTargets
noncomputable section
open scoped NNReal
variable {d : ℕ} {K₀ : Fin d→ℕ} {T U : IntegerRectangularTiling d K₀}
variable {W : Type*} [Fintype W] {G : SimpleGraph W} (D₀ : SupportTorsionData G)
variable {K : ℕ} {i : Fin d}

theorem actualQuantitativeSkeleton_projected_pattern
    (δ V : Fin d→ℝ≥0) (D J : ℝ≥0) (hδ : ∀j,0<δ j)
    (hlower : ∀R,R∈T.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper : ∀R,R∈T.cells → ∀j,(R.transverseWidth j).toNNReal≤V j)
    (hlower' : ∀R,R∈U.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper' : ∀R,R∈U.cells → ∀j,(R.transverseWidth j).toNNReal≤V j)
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint (2*D₀.power+1) K i R) D J)
    (H' : ∀R,R∈U.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint (2*D₀.power+1) K i R) D J)
    (hH : ∀Q (hQ : Q∈T.cells) (hQ' : Q∈U.cells) (hi : Q.lower i<Q.upper i),H Q hQ hi=H' Q hQ' hi)
    (z : RealCoordinates d) (hpat : T.dependencyPattern z=U.dependencyPattern z) :
    (actualQuantitativeSkeleton δ V D J hδ hlower hupper H (d+1)).toSkeletonCarrierMaps.projectedMap D₀ z=
      (actualQuantitativeSkeleton δ V D J hδ hlower' hupper' H' (d+1)).toSkeletonCarrierMaps.projectedMap D₀ z := by
  let P := T.pointCell z
  have hP : P∈T.cells := ⟨z,rfl⟩
  have hz : z∈P.closedBox := P.relativeInterior_subset (T.mem_relativeInterior_pointCell z)
  have hcells := T.dependencyPattern_eq_contained_cells U z hpat P hP hz
  have hP' : P∈U.cells := (hcells P Set.Subset.rfl).mp hP
  rw [SkeletonCarrierMaps.projectedMap_eq_cell D₀ _ P hP z hz,
    SkeletonCarrierMaps.projectedMap_eq_cell D₀ _ P hP' z hz]
  apply congrArg (D₀.carrierProjection K (P.lower i) (P.upper i))
  exact actualQuantitativeSkeleton_locality δ V D J hδ hlower hupper hlower' hupper' H H' P
    hcells (fun Q hQ hQ' hi _=>hH Q hQ hQ' hi) (d+1) P hP hP' P.rank_lt_succ_dimension Set.Subset.rfl ⟨z,hz⟩

variable {L : Fin d→ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M₀ : AnisotropicClopenMarkers d L X} {S : ℕ}

def ContinuousMarkerBoxes.canonicalProjectedMap
    (B : ContinuousMarkerBoxes M₀ S) (hL : ∀j,1≤L j) (hS : 24≤S)
    (K : ℕ) (i : Fin d) (J : ℝ≥0)
    (H : IntervalCarriers.NormalizedContractionFamily (2*D₀.power+1) K (6*L i) J)
    (x : X) (z : RealCoordinates d) : SupportPair G :=
  (B.canonicalQuantitativeSkeleton hL hS x (2*D₀.power+1) K i J H (d+1)).toSkeletonCarrierMaps.projectedMap D₀ z

theorem ContinuousMarkerBoxes.canonicalProjectedMap_pattern
    (B : ContinuousMarkerBoxes M₀ S) (hL : ∀j,1≤L j) (hS : 24≤S)
    (K : ℕ) (i : Fin d) (J : ℝ≥0)
    (H : IntervalCarriers.NormalizedContractionFamily (2*D₀.power+1) K (6*L i) J)
    (x y : X) (z : RealCoordinates d)
    (hpat : (B.tiling hL (by omega) x).dependencyPattern z=(B.tiling hL (by omega) y).dependencyPattern z) :
    B.canonicalProjectedMap D₀ hL hS K i J H x z=B.canonicalProjectedMap D₀ hL hS K i J H y z := by
  unfold canonicalProjectedMap canonicalQuantitativeSkeleton quantitativeSkeleton
  apply actualQuantitativeSkeleton_projected_pattern
  · intro Q hQ hQ' hi
    rfl
  · exact hpat

end
end AbelianTargets

