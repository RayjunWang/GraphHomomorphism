import AbelianTargets.CarrierGeometry
import AbelianTargets.SimplexMetricGluing

namespace AbelianTargets
noncomputable section
namespace Probability
variable {V : Type*} [Fintype V]
def positiveSupport (p : Probability V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => 0 < p.mass v)
@[simp] theorem mem_positiveSupport (p : Probability V) (v : V) :
    v ∈ p.positiveSupport ↔ 0 < p.mass v := by
  classical
  simp [positiveSupport]
theorem supportedOn_positiveSupport (p : Probability V) :
    p.SupportedOn (p.positiveSupport : Set V) := fun v hv => (mem_positiveSupport p v).mpr hv
theorem positiveSupport_subset (p : Probability V) {s : Finset V}
    (hp : p.SupportedOn (s : Set V)) : p.positiveSupport ⊆ s := by
  intro v hv; exact hp v ((mem_positiveSupport p v).mp hv)
end Probability
namespace IntervalCarriers
theorem simplexFaces_downward {m K : ℕ} {A B : ℤ} {s t : Finset (CarrierVertex K A B)}
    (hs : s ∈ simplexFaces m K A B) (ht : t ⊆ s) : t ∈ simplexFaces m K A B := by
  apply (mem_simplexFaces t).mpr
  exact ((mem_simplexFaces s).mp hs).downward (Finset.image_subset_image ht)
theorem positiveSupport_mem {m K : ℕ} {A B : ℤ} (p : Realization m K A B) :
    p.1.positiveSupport ∈ simplexFaces m K A B := by
  obtain ⟨s,hs,hp⟩ := p.2
  exact simplexFaces_downward hs (p.1.positiveSupport_subset hp)
end IntervalCarriers
end
end AbelianTargets
