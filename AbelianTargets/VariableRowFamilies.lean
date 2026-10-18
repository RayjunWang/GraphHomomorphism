import AbelianTargets.FixedRowRealization

/-! Fixed-slot row interpolation with a moving terminal vertex. -/

namespace AbelianTargets.FixedSlots

open scoped NNReal
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def rowFamily (row₀ row₁ : ℕ → E) (n : ℕ) (z : unitInterval × unitInterval) : E :=
  rowPath (n+1) (fun j => mix (row₀ j) (row₁ j) z.1) n z.2

theorem rowFamily_continuous (row₀ row₁ : ℕ → E) (n : ℕ) :
    Continuous (rowFamily row₀ row₁ n) := by
  apply (continuous_rowPath (n+1) (Nat.succ_pos n)
    (fun r j => mix (row₀ j) (row₁ j) r) (fun j => ?_) n).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  exact (continuous_const.sub continuous_subtype_val).smul continuous_const |>.add
    (continuous_subtype_val.smul continuous_const)

theorem rowFamily_path_time_lipschitz (row₀ row₁ : ℕ → E) (n : ℕ) (Δ : ℝ≥0)
    (h₀ : ∀ j ≤ n, dist (row₀ j) (row₀ (j+1)) ≤ Δ)
    (h₁ : ∀ j ≤ n, dist (row₁ j) (row₁ (j+1)) ≤ Δ) (r : unitInterval) :
    LipschitzWith (Δ*(n+1)) (fun u : unitInterval => rowFamily row₀ row₁ n (r,u)) := by
  simpa only [mul_one,Nat.cast_add,Nat.cast_one,rowFamily,Function.comp_def] using
    (interpolated_row_lipschitz (n+1) (Nat.succ_pos n) row₀ row₁ n Δ h₀ h₁ r).comp
      (LipschitzWith.subtype_val (Set.Icc (0 : ℝ) 1))

theorem rowFamily_joint_lipschitz (row₀ row₁ : ℕ → E) (n : ℕ) (Δ C : ℝ≥0)
    (h₀ : ∀ j ≤ n, dist (row₀ j) (row₀ (j+1)) ≤ Δ)
    (h₁ : ∀ j ≤ n, dist (row₁ j) (row₁ (j+1)) ≤ Δ)
    (hv : ∀ j ≤ n+1, dist (row₀ j) (row₁ j) ≤ C) :
    LipschitzWith (Δ*(n+1)+C) (rowFamily row₀ row₁ n) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨r,u⟩ ⟨s,v⟩
  have hu := (rowFamily_path_time_lipschitz row₀ row₁ n Δ h₀ h₁ r).dist_le_mul u v
  have hs := interpolated_row_parameter_bound row₀ row₁ n C hv r s v
  calc
    _ ≤ dist (rowFamily row₀ row₁ n (r,u)) (rowFamily row₀ row₁ n (r,v)) +
      dist (rowFamily row₀ row₁ n (r,v)) (rowFamily row₀ row₁ n (s,v)) := dist_triangle _ _ _
    _ ≤ (Δ*(n+1) : ℝ≥0)*dist u v + C*dist r s := add_le_add hu hs
    _ ≤ (Δ*(n+1) : ℝ≥0)*dist (r,u) (s,v) + C*dist (r,u) (s,v) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
        (mul_le_mul_of_nonneg_left (le_max_left _ _) C.property)
    _ = (Δ*(n+1)+C : ℝ≥0)*dist (r,u) (s,v) := by simp [add_mul]

theorem rowFamily_mem_charts (row₀ row₁ : ℕ → E) (n : ℕ) {S : Set E}
    (hcharts : ∀ j ≤ n, ∃ F : Set E, Convex ℝ F ∧ F ⊆ S ∧
      row₀ j ∈ F ∧ row₀ (j+1) ∈ F ∧ row₁ j ∈ F ∧ row₁ (j+1) ∈ F)
    (z : unitInterval × unitInterval) : rowFamily row₀ row₁ n z ∈ S := by
  have hne : (n : ℝ)+1 ≠ 0 := by positivity
  have hu : (z.2 : ℝ) ≤ ((n : ℝ)+1)/((n+1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add,Nat.cast_one,hne] using z.2.property.2
  obtain ⟨j,hj,h₀,h₁⟩ := exists_slot (n+1) (Nat.succ_pos n) n z.2 z.2.property.1 hu
  obtain ⟨F,hconv,hsub,ha,hb,hc,hd⟩ := hcharts j hj
  exact hsub (interpolated_row_mem_on_slot (n+1) (Nat.succ_pos n) row₀ row₁ n j hj z.1
    hconv ha hb hc hd z.2 h₀ h₁)

@[simp] theorem rowFamily_zero (row₀ row₁ : ℕ → E) (n : ℕ) (u : unitInterval) :
    rowFamily row₀ row₁ n (0,u) = asPath row₀ n u := by
  simp only [rowFamily,mix_zero]
  rfl

@[simp] theorem rowFamily_one (row₀ row₁ : ℕ → E) (n : ℕ) (u : unitInterval) :
    rowFamily row₀ row₁ n (1,u) = asPath row₁ n u := by
  simp only [rowFamily,mix_one]
  rfl

@[simp] theorem rowFamily_source (row₀ row₁ : ℕ → E) (n : ℕ) (r : unitInterval) :
    rowFamily row₀ row₁ n (r,0) = mix (row₀ 0) (row₁ 0) r :=
  rowPath_zero (n+1) (Nat.succ_pos n) _ n

@[simp] theorem rowFamily_target (row₀ row₁ : ℕ → E) (n : ℕ) (r : unitInterval) :
    rowFamily row₀ row₁ n (r,1) = mix (row₀ (n+1)) (row₁ (n+1)) r := by
  have h := rowPath_right (n+1) (Nat.succ_pos n) (fun j => mix (row₀ j) (row₁ j) r) n
  have he : ((n : ℝ)+1)/(n+1 : ℕ) = 1 := by push_cast; field_simp
  simpa only [rowFamily,he] using h

end
end AbelianTargets.FixedSlots
