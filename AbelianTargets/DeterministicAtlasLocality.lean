import AbelianTargets.DeterministicQuantitativeAtlas
import AbelianTargets.AtlasCellLocality

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AbelianTargets
noncomputable section
open scoped NNReal
variable {d : ℕ} {K₀ : Fin d→ℕ} {T T' : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d}

/-- Literal rank recursion is local: inside a fixed parent rectangle it
depends only on the contained cell pattern and the chosen carrier contractions. -/
theorem actualQuantitativeSkeleton_locality
    (δ U : Fin d→ℝ≥0) (D J : ℝ≥0) (hδ : ∀j,0<δ j)
    (hlower : ∀R,R∈T.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper : ∀R,R∈T.cells → ∀j,(R.transverseWidth j).toNNReal≤U j)
    (hlower' : ∀R,R∈T'.cells → ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper' : ∀R,R∈T'.cells → ∀j,(R.transverseWidth j).toNNReal≤U j)
    (H : ∀R,R∈T.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (H' : ∀R,R∈T'.cells → R.lower i<R.upper i → ControlledContraction (cellLeftPoint m K i R) D J)
    (P : RectangularCell d)
    (hcells : ∀Q,Q.closedBox⊆P.closedBox → (Q∈T.cells ↔ Q∈T'.cells))
    (hH : ∀Q (hQ : Q∈T.cells) (hQ' : Q∈T'.cells) (hi : Q.lower i<Q.upper i),
      Q.closedBox⊆P.closedBox → H Q hQ hi=H' Q hQ' hi)
    (n : ℕ) : ∀ (R : RectangularCell d) (hR : R∈T.cells) (hR' : R∈T'.cells)
      (hr : R.rank<n) (hRP : R.closedBox⊆P.closedBox) (z : CellClosedDomain R),
      (actualQuantitativeSkeleton δ U D J hδ hlower hupper H n).map R hR hr z=
        (actualQuantitativeSkeleton δ U D J hδ hlower' hupper' H' n).map R hR' hr z := by
  induction n with
  | zero => intro R hR hR' hr; exact (Nat.not_lt_zero _ hr).elim
  | succ n ih =>
    intro R hR hR' hr hRP z
    let F := actualQuantitativeSkeleton δ U D J hδ hlower hupper H n
    let G := actualQuantitativeSkeleton δ U D J hδ hlower' hupper' H' n
    change F.toEndpointSkeletonCarrierMaps.nextMap (actualQuantitativeExtension F H) R hR hr z=
      G.toEndpointSkeletonCarrierMaps.nextMap (actualQuantitativeExtension G H') R hR' hr z
    by_cases hsmall : R.rank<n
    · simp only [EndpointSkeletonCarrierMaps.nextMap,dif_pos hsmall]
      exact ih R hR hR' hsmall hRP z
    · have he : R.rank=n := by omega
      simp only [EndpointSkeletonCarrierMaps.nextMap,dif_neg hsmall]
      by_cases hi : R.lower i<R.upper i
      · simp only [actualQuantitativeExtension,dif_pos hi]
        rw [←hH R hR hR' hi hRP]
        let LF := F.toSkeletonCarrierMaps.lowerFamily R he
        let LG := G.toSkeletonCarrierMaps.lowerFamily R he
        apply LF.controlledCellExtension_map_ext LG hR hR'
          (F.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he)
          (G.toEndpointSkeletonCarrierMaps.lowerFamily_endpoints R he)
          _ _ (F.lowerFamily_update_bounds R he) (G.lowerFamily_update_bounds R he) hi (H R hR hi) _ z
        intro zb
        apply LF.boundaryValue_eq_of_finite_lower_agreement LG hR hR'
        · intro Q hQb
          obtain ⟨hQc,hQR,hrQ⟩ := (T.mem_boundaryCells R Q).mp hQb
          exact (hcells Q (hQR.trans hRP)).mp hQc
        · intro Q hQb hQc hQc' hrQ zQ
          have hQR := ((T.mem_boundaryCells R Q).mp hQb).2.1
          exact ih Q hQc hQc' (by omega) (hQR.trans hRP) zQ
      · simp only [actualQuantitativeExtension,dif_neg hi]
        rfl

end
end AbelianTargets
