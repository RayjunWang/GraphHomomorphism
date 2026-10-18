import AbelianTargets.CarrierProjectionFaceCharts
import AbelianTargets.CarrierFaceBound
import AbelianTargets.UniformSimplexGluing

/-! One modulus for every finite interval-carrier projection. -/
namespace AbelianTargets.SupportTorsionData
noncomputable section
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
open IntervalCarriers

theorem carrierProjection_face_modulus :
    ∀ ε:ℝ,0<ε→∃δ:ℝ,0<δ ∧ ∀(K:ℕ)(A B:ℤ)
      (s:Finset (CarrierVertex K A B)),s∈simplexFaces (2*D.power+1) K A B→
      ∀p q:Realization (2*D.power+1) K A B,
        p.1.SupportedOn (s:Set _)→q.1.SupportedOn (s:Set _)→
        dist p q<δ→dist (D.carrierProjection K A B p) (D.carrierProjection K A B q)<ε := by
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := D.affineChart_uniform_face_modulus ε hε
  refine ⟨δ,hδ,?_⟩
  intro K A B s hs p q hp hq hd
  obtain ⟨r,height,theta,hrepr⟩ := D.faceValue_affine_representation K A B s hs
  rw [D.carrierProjection_eq_faceValue K A B p s hs hp,
    D.carrierProjection_eq_faceValue K A B q s hs hq,hrepr p.1 hp,hrepr q.1 hq]
  exact hbound height theta r s p.1 q.1 (simplexFaces_card_le_three hs) hp hq hd

theorem carrierProjection_uniform_modulus :
    ∀ ε:ℝ,0<ε→∃δ:ℝ,0<δ ∧ ∀(K:ℕ)(A B:ℤ)
      (p q:Realization (2*D.power+1) K A B),
        dist p q<δ→dist (D.carrierProjection K A B p) (D.carrierProjection K A B q)<ε := by
  let F (i:ℕ×ℤ×ℤ) := simplexFaces (2*D.power+1) i.1 i.2.1 i.2.2
  let f (i:ℕ×ℤ×ℤ) := D.carrierProjection i.1 i.2.1 i.2.2
  have hface : ∀ε:ℝ,0<ε→∃δ:ℝ,0<δ ∧ ∀i s,s∈F i→
      ∀p q:SimplicialCarrier (F i),p.1.SupportedOn (s:Set _)→q.1.SupportedOn (s:Set _)→
        dist p q<δ→dist (f i p) (f i q)<ε := by
    intro ε hε
    obtain ⟨δ,hδ,hbound⟩ := D.carrierProjection_face_modulus ε hε
    exact ⟨δ,hδ,fun i s hs p q hp hq hd => hbound i.1 i.2.1 i.2.2 s hs p q hp hq hd⟩
  have hglobal := uniform_simplex_face_modulus F f 3
    (fun i s hs => simplexFaces_card_le_three hs) hface
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := hglobal ε hε
  exact ⟨δ,hδ,fun K A B p q h => hbound (K,A,B) p q h⟩

end
end AbelianTargets.SupportTorsionData
