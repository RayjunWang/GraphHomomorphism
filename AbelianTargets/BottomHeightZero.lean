import AbelianTargets.BottomCarrierClassification
import AbelianTargets.CarrierHeightCut
import AbelianTargets.SimplicialSupport

namespace AbelianTargets.IntervalCarriers
noncomputable section

theorem CarrierFace.zero_of_height {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    {s : Finset Vertex} (hs : CarrierFace m K A B s) (hzero : ∀ v ∈ s,v.2=0) :
    CarrierFace m 0 A B s := by
  induction K with
  | zero => exact hs
  | succ K ih =>
    apply ih
    exact hs.lower_of_height hm (fun v hv => by rw [hzero v hv]; exact Nat.zero_le K)

theorem realization_bottomSupported_of_height_zero {m K R : ℕ} (hm : 1 ≤ m)
    (p : Realization m K 0 R) (hzero : ∀ v,0 < p.val.mass v → v.val.2=0) :
    BottomSupported K R p.val := by
  let s := p.val.positiveSupport
  have hs := (mem_simplexFaces s).mp (positiveSupport_mem p)
  apply bottomSupported_of_face p.val s (hs.zero_of_height hm ?_) p.val.supportedOn_positiveSupport
  intro v hv
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  exact hzero w ((Probability.mem_positiveSupport p.val w).mp hw)

theorem bottomMap_inverse_height_zero {m K R : ℕ} (hm : 1 ≤ m)
    (p : Realization m K 0 R) (hzero : ∀ v,0 < p.val.mass v → v.val.2=0) :
    bottomMap K R (bottomCoordinate K R p.val)=p.val.mass :=
  bottomMap_inverse K R p.val (realization_bottomSupported_of_height_zero hm p hzero)

end
end AbelianTargets.IntervalCarriers
