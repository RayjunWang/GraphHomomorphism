import AbelianTargets.CarrierGeometry

/-! Convex ambient charts of the actual finite interval carrier. -/

namespace AbelianTargets
open scoped BigOperators
noncomputable section
namespace Probability

variable {V : Type*} [Fintype V]

def faceChart (s : Finset V) : Set (V → ℝ) :=
  {f | (∀ v, 0 ≤ f v) ∧ (∑ v, f v = 1) ∧ ∀ v ∉ s, f v = 0}

theorem faceChart_convex (s : Finset V) : Convex ℝ (faceChart s) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_,?_,?_⟩
  · intro v
    exact add_nonneg (mul_nonneg ha (hx.1 v)) (mul_nonneg hb (hy.1 v))
  · change ∑ v, (a*x v+b*y v) = 1
    rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hx.2.1,hy.2.1]
    simpa only [mul_one] using hab
  · intro v hv
    change a*x v+b*y v = 0
    rw [hx.2.2 v hv,hy.2.2 v hv]
    simp

theorem mass_mem_faceChart (p : Probability V) (s : Finset V)
    (hp : p.SupportedOn (s : Set V)) : p.mass ∈ faceChart s :=
  ⟨p.nonneg,p.sum_one,fun v hv => supportedOn_iff_zero.mp hp v hv⟩

theorem dirac_mem_faceChart (s : Finset V) (v : V) (hv : v ∈ s) :
    (dirac v).mass ∈ faceChart s :=
  mass_mem_faceChart _ _ (supportedOn_dirac v hv)

end Probability
namespace IntervalCarriers

def ambientRealization (m K : ℕ) (A B : ℤ) : Set (CarrierVertex K A B → ℝ) :=
  Set.range (fun p : Realization m K A B => p.1.mass)

def ambientEquiv (m K : ℕ) (A B : ℤ) :
    Realization m K A B ≃ᵢ {f : CarrierVertex K A B → ℝ // f ∈ ambientRealization m K A B} where
  toEquiv := Equiv.ofInjective (fun p : Realization m K A B => p.1.mass) (by
    intro p q h
    exact Subtype.ext (Probability.ext h))
  isometry_toFun := by intro p q; rfl

theorem faceChart_subset_ambient {m K : ℕ} {A B : ℤ} (s : Finset (CarrierVertex K A B))
    (hs : CarrierFace m K A B (s.image Subtype.val)) :
    Probability.faceChart s ⊆ ambientRealization m K A B := by
  intro f hf
  let p : Probability (CarrierVertex K A B) := ⟨f,hf.1,hf.2.1⟩
  have hp : p.SupportedOn (s : Set _) := Probability.supportedOn_iff_zero.mpr hf.2.2
  exact ⟨⟨p,s,(mem_simplexFaces s).mpr hs,hp⟩,rfl⟩

end IntervalCarriers
end
end AbelianTargets
