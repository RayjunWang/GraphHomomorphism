import AbelianTargets.MarkerAtlasSideBounds
import AbelianTargets.MarkerAtlasCovariance
import AbelianTargets.ContinuousAtlasPatterns

/-! An actual regular anisotropic atlas package. Its fields are marker and
cut data; all tiling, stratum, boundary, covariance and locality properties
are theorems about the constructed rectangles. -/

namespace AbelianTargets
noncomputable section
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]

structure RegularAnisotropicAtlas (L : Fin d → ℕ) (X : Type*)
    [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X] where
  markers : AnisotropicClopenMarkers d L X
  boxes : ContinuousMarkerBoxes markers 30

theorem exists_regularAnisotropicAtlas [T1Space X] [SecondCountableTopology X]
    (L : Fin d → ℕ) (zeroDim : ZeroDimensional X)
    (free : IsFree (G := Lattice d) (X := X))
    (hscale : ∀ i,32*(61^d) ≤ L i) : Nonempty (RegularAnisotropicAtlas L X) := by
  obtain ⟨M⟩ := exists_anisotropicClopenMarkers L zeroDim free
  have hL : ∀ i,1 ≤ L i := by
    intro i
    have hp : 1 ≤ 61^d := Nat.one_le_pow _ _ (by norm_num)
    have hs := hscale i
    omega
  obtain ⟨B⟩ := exists_continuousMarkerBoxes M hL 30 free zeroDim hscale
  exact ⟨⟨M,B⟩⟩

end
end AbelianTargets
