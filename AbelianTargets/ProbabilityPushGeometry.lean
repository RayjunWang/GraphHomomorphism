import AbelianTargets.ProbabilityMap
import AbelianTargets.CarrierGeometry

namespace AbelianTargets.Probability
open scoped BigOperators NNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W : Type*} [Fintype V] [Fintype W]

theorem push_eq_self (f : V → V) (p : Probability V)
    (hf : ∀ v, 0 < p.mass v → f v = v) : push f p = p := by
  ext w
  rw [push_mass]
  have he : (∑ v, if f v = w then p.mass v else 0) =
      ∑ v, if v = w then p.mass v else 0 := by
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hp : 0 < p.mass v
    · rw [hf v hp]
    · have hz : p.mass v = 0 := le_antisymm (le_of_not_gt hp) (p.nonneg v)
      simp [hz]
  rw [he]
  simp

theorem push_lipschitz (f : V → W) : LipschitzWith (Fintype.card V) (push f) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change dist (push f p).mass (push f q).mass ≤ (Fintype.card V : ℝ)*dist p q
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ (Fintype.card V : ℝ)*dist p q)).mpr
  intro w
  rw [Real.dist_eq,push_mass,push_mass,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ v, |(if f v = w then p.mass v else 0)-(if f v = w then q.mass v else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : V, dist p q := Finset.sum_le_sum (fun v _ => by
      by_cases h : f v = w
      · simpa only [h,if_true] using dist_le_pi_dist p.mass q.mass v
      · simp only [h,if_false,sub_self,abs_zero]; exact dist_nonneg)
    _ = _ := by simp

theorem push_supportedOn_image (f : V → W) (p : Probability V) {s : Set V}
    (hp : p.SupportedOn s) : (push f p).SupportedOn (f '' s) := by
  intro w hw
  obtain ⟨v,hv,hpv⟩ := (push_pos_iff f p w).mp hw
  exact ⟨v,hp v hpv,hv⟩

theorem push_comp {U : Type*} [Fintype U] (f : V → W) (g : W → U) (p : Probability V) :
    push g (push f p) = push (g ∘ f) p := by
  ext u
  simp only [push_mass]
  have he : (∑ w, if g w = u then ∑ v, if f v = w then p.mass v else 0 else 0) =
      ∑ w, ∑ v, if g w = u then (if f v = w then p.mass v else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro w hw
    split_ifs
    · rfl
    · simp
  rw [he,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  have he' : (∑ w, if g w = u then (if f v = w then p.mass v else 0) else 0) =
      ∑ w, if w = f v then (if g (f v) = u then p.mass v else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro w hw
    by_cases h : w = f v
    · subst w; simp
    · simp [h,Ne.symm h]
  rw [he']
  simp

theorem push_mass_of_injective (f : V → W) (hf : Function.Injective f) (p : Probability V) (v : V) :
    (push f p).mass (f v) = p.mass v := by
  rw [push_mass]
  simp only [hf.eq_iff]
  simp

theorem isometry_push (f : V → W) (hf : Function.Injective f) : Isometry (push f) := by
  apply Isometry.of_dist_eq
  intro p q
  apply le_antisymm
  · change dist (push f p).mass (push f q).mass ≤ dist p q
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro w
    by_cases hw : ∃ v, f v = w
    · obtain ⟨v,rfl⟩ := hw
      rw [push_mass_of_injective f hf, push_mass_of_injective f hf,Real.dist_eq]
      exact dist_le_pi_dist p.mass q.mass v
    · have hz (r : Probability V) : (push f r).mass w = 0 := by
        rw [push_mass]
        apply Finset.sum_eq_zero
        intro v hv
        simp [show f v ≠ w from fun h => hw ⟨v,h⟩]
      rw [hz p,hz q,dist_self]
      exact dist_nonneg
  · change dist p.mass q.mass ≤ dist (push f p) (push f q)
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro v
    rw [←push_mass_of_injective f hf p v,←push_mass_of_injective f hf q v]
    exact dist_le_pi_dist (push f p).mass (push f q).mass (f v)

end
end AbelianTargets.Probability
