import AbelianTargets.IntegerCellGluing

/-! Unit-interval gluing on an integer bounded coordinate interval. -/
namespace AbelianTargets
open scoped NNReal
noncomputable section

def integerIntervalClamp (A B : ℤ) (t : ℝ) : ℝ := max (A : ℝ) (min (B : ℝ) t)

theorem integerIntervalClamp_mem {A B : ℤ} (hAB : A≤B) (t : ℝ) :
    integerIntervalClamp A B t∈Set.Icc (A : ℝ) (B : ℝ) := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by exact_mod_cast hAB) (min_le_left _ _)

theorem integerIntervalClamp_eq {A B : ℤ} {t : ℝ} (ht : t∈Set.Icc (A : ℝ) (B : ℝ)) :
    integerIntervalClamp A B t=t := by simp [integerIntervalClamp,min_eq_right ht.2,max_eq_right ht.1]

theorem integerIntervalClamp_low {A B : ℤ} (hAB : A≤B) {t : ℝ} (ht : t≤(A : ℝ)) :
    integerIntervalClamp A B t=(A : ℝ) := by
  have hAB' : (A : ℝ)≤B := by exact_mod_cast hAB
  simp [integerIntervalClamp,min_eq_right (ht.trans hAB'),max_eq_left ht]

theorem integerIntervalClamp_high {A B : ℤ} (hAB : A≤B) {t : ℝ} (ht : (B : ℝ)≤t) :
    integerIntervalClamp A B t=(B : ℝ) := by
  have hAB' : (A : ℝ)≤B := by exact_mod_cast hAB
  simp [integerIntervalClamp,min_eq_left ht,max_eq_right hAB']

theorem lipschitz_integer_clamped_intervals {Z : Type*} [PseudoMetricSpace Z]
    (A B : ℤ) (hAB : A≤B) (f : ℝ→Z) (K : ℝ≥0)
    (hunit : ∀ n : ℤ,A≤n→n+1≤B→∀ x∈Set.Icc (n : ℝ) ((n : ℝ)+1),
      ∀ y∈Set.Icc (n : ℝ) ((n : ℝ)+1),dist (f x) (f y)≤K*|x-y|) :
    LipschitzWith K (fun t => f (integerIntervalClamp A B t)) := by
  apply lipschitz_real_of_integer_intervals
  intro n x hx y hy
  by_cases hlo : n<A
  · have hn : n+1≤A := by omega
    have hn' : (n : ℝ)+1≤A := by exact_mod_cast hn
    rw [integerIntervalClamp_low hAB (hx.2.trans hn'),integerIntervalClamp_low hAB (hy.2.trans hn')]
    simp only [dist_self]
    exact mul_nonneg K.2 (abs_nonneg _)
  · by_cases hhi : B≤n
    · have hn' : (B : ℝ)≤n := by exact_mod_cast hhi
      rw [integerIntervalClamp_high hAB (hn'.trans hx.1),integerIntervalClamp_high hAB (hn'.trans hy.1)]
      simp only [dist_self]
      exact mul_nonneg K.2 (abs_nonneg _)
    · have hnA : A≤n := le_of_not_gt hlo
      have hnB : n+1≤B := by omega
      have hxR : x∈Set.Icc (A : ℝ) (B : ℝ) :=
        ⟨(show (A : ℝ)≤n by exact_mod_cast hnA).trans hx.1,
          hx.2.trans (show (n : ℝ)+1≤B by exact_mod_cast hnB)⟩
      have hyR : y∈Set.Icc (A : ℝ) (B : ℝ) :=
        ⟨(show (A : ℝ)≤n by exact_mod_cast hnA).trans hy.1,
          hy.2.trans (show (n : ℝ)+1≤B by exact_mod_cast hnB)⟩
      rw [integerIntervalClamp_eq hxR,integerIntervalClamp_eq hyR]
      exact hunit n hnA hnB x hx y hy

end
end AbelianTargets
