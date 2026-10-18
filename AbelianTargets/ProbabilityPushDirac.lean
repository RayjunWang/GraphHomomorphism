import AbelianTargets.ProbabilityPushGeometry

namespace AbelianTargets.Probability
noncomputable section
variable {V W : Type*} [Fintype V] [Fintype W]

@[simp] theorem push_dirac (f : V → W) (v : V) : push f (dirac v)=dirac (f v) := by
  classical
  ext w
  rw [push_mass]
  rw [Finset.sum_eq_single v]
  · simp [dirac_mass,eq_comm]
  · intro u hu huv
    simp [dirac_mass,huv]
  · simp

end
end AbelianTargets.Probability
