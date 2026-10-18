import AbelianTargets.ControlledStages

/-! Equal-slot concatenation of a family of curves with literal seams. -/
namespace AbelianTargets
open scoped NNReal unitInterval
noncomputable section

def familyCurve {X Y : Type*} (H : ℕ → X × I → Y) : ℕ → ℝ × X → Y
  | 0 => fun z => H 0 (z.2,0)
  | 1 => fun z => H 0 (z.2,clampInterval z.1)
  | n+2 => fun z => if z.1 ≤ ((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ) then
      familyCurve H (n+1) (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)*z.1,z.2)
    else H (n+1) (z.2,clampInterval (((n+2 : ℕ) : ℝ)*z.1-((n+1 : ℕ) : ℝ)))

theorem familyCurve_zero {X Y : Type*} (H : ℕ → X × I → Y) (n : ℕ) (x : X) :
    familyCurve H n (0,x)=H 0 (x,0) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [familyCurve]
  | more n ih ih' =>
    have hc : (0 : ℝ)≤((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ) := by positivity
    simpa only [familyCurve,if_pos hc,mul_zero] using ih'

theorem familyCurve_one {X Y : Type*} (H : ℕ → X × I → Y) (n : ℕ) (x : X) :
    familyCurve H (n+1) (1,x)=H n (x,1) := by
  cases n with
  | zero => simp [familyCurve]
  | succ n =>
    have hc : ¬(1 : ℝ)≤((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ) := by
      apply not_le.mpr
      apply (div_lt_one (by positivity)).2
      norm_cast; omega
    rw [familyCurve]
    dsimp only
    rw [if_neg hc]
    have ht : ((n+2 : ℕ) : ℝ)*1-((n+1 : ℕ) : ℝ)=1 := by push_cast; ring
    rw [ht,clampInterval_one]

theorem familyCurve_seam {X Y : Type*} (H : ℕ → X × I → Y)
    (hseam : ∀ n x, H n (x,1)=H (n+1) (x,0)) (n : ℕ) (x : X) :
    familyCurve H (n+1)
      ((((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)),x)=
    H (n+1) (x,clampInterval (((n+2 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))-((n+1 : ℕ) : ℝ))) := by
  have h₁ : (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))=1 := by field_simp
  have h₂ : ((n+2 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))-((n+1 : ℕ) : ℝ)=0 := by field_simp; simp
  rw [h₁,h₂,clampInterval_zero,familyCurve_one,hseam]

theorem familyCurve_track {X Y : Type*} [MetricSpace Y] (H : ℕ → X × I → Y)
    (hseam : ∀ n x, H n (x,1)=H (n+1) (x,0)) (D : ℝ≥0)
    (htrack : ∀ n x, LipschitzWith D (fun t : I => H n (x,t)))
    (n : ℕ) (x : X) : LipschitzWith ((n : ℝ≥0)*D) (fun t : ℝ => familyCurve H n (t,x)) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [familyCurve] using (LipschitzWith.const (H 0 (x,0)) : LipschitzWith 0 (fun _ : ℝ => H 0 (x,0)))
  | one => simpa only [Nat.cast_one,one_mul,familyCurve,Function.comp_def,mul_one] using
      (htrack 0 x).comp lipschitz_clampInterval
  | more n ih ih' =>
    let r : ℝ≥0 := ((n+2 : ℕ) : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
    have hr : |(((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))|≤r := by
      change |(((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))|≤((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)
      rw [abs_of_nonneg (by positivity)]
    have hf := ih'.comp (lipschitz_affine_le r (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)) 0 hr)
    have hconst : (((n+1 : ℕ) : ℝ≥0)*D)*r=((n+2 : ℕ) : ℝ≥0)*D := by dsimp [r]; field_simp
    rw [hconst] at hf
    have hg := ((htrack (n+1) x).comp lipschitz_clampInterval).comp
      (lipschitz_affine_le ((n+2 : ℕ) : ℝ≥0) ((n+2 : ℕ) : ℝ) (-((n+1 : ℕ) : ℝ)) (by
        change |((n+2 : ℕ) : ℝ)|≤((n+2 : ℕ) : ℝ)
        rw [abs_of_nonneg (by positivity)]))
    have hconst' : (D*1)*((n+2 : ℕ) : ℝ≥0)=((n+2 : ℕ) : ℝ≥0)*D := by ring
    rw [hconst'] at hg
    have he := lipschitz_glue_at _ _ hf hg (((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)) (by
      simpa only [Function.comp_def,add_zero,←sub_eq_add_neg] using familyCurve_seam H hseam n x)
    simpa only [familyCurve,Function.comp_def,add_zero,sub_eq_add_neg] using he

theorem familyCurve_joint {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (H : ℕ → X × I → Y) (hseam : ∀ n x, H n (x,1)=H (n+1) (x,0))
    (hjoint : ∀ n, ∃ J : ℝ≥0, LipschitzWith J (H n)) (n : ℕ) :
    ∃ J : ℝ≥0, LipschitzWith J (familyCurve H n) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    obtain ⟨J,hJ⟩ := hjoint 0
    refine ⟨J*max 1 0,?_⟩
    simpa only [familyCurve,Function.comp_def] using
      hJ.comp ((LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × X → X)).prodMk
        (LipschitzWith.const (0 : I)))
  | one =>
    obtain ⟨J,hJ⟩ := hjoint 0
    refine ⟨J*max 1 (1*1),?_⟩
    simpa only [familyCurve,Function.comp_def] using
      hJ.comp ((LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × X → X)).prodMk
        (lipschitz_clampInterval.comp LipschitzWith.prod_fst))
  | more n ih ih' =>
    obtain ⟨A,hA⟩ := ih'
    obtain ⟨J,hJ⟩ := hjoint (n+1)
    let r : ℝ≥0 := ((n+2 : ℕ) : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
    have hr : |(((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))|≤r := by
      change |(((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ))|≤((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)
      rw [abs_of_nonneg (by positivity)]
    have hp := ((lipschitz_affine_le r (((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)) 0 hr).comp
      (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : ℝ × X → ℝ))).prodMk
      (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × X → X))
    have hf := hA.comp hp
    have ht := (lipschitz_clampInterval.comp
      (lipschitz_affine_le ((n+2 : ℕ) : ℝ≥0) ((n+2 : ℕ) : ℝ) (-((n+1 : ℕ) : ℝ)) (by
        change |((n+2 : ℕ) : ℝ)|≤((n+2 : ℕ) : ℝ)
        rw [abs_of_nonneg (by positivity)]))).comp
      (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : ℝ × X → ℝ))
    have hg := hJ.comp ((LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × X → X)).prodMk ht)
    let K := max (A*max (r*1) 1) (J*max 1 ((1*((n+2 : ℕ) : ℝ≥0))*1))
    refine ⟨2*K,?_⟩
    have hglue := lipschitz_glue_product_at _ _ (hf.weaken (le_max_left _ _)) (hg.weaken (le_max_right _ _))
      (((n+1 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)) (fun x => by
        simpa only [Function.comp_def,add_zero,←sub_eq_add_neg] using familyCurve_seam H hseam n x)
    simpa only [familyCurve,Function.comp_def,add_zero,sub_eq_add_neg] using hglue

theorem familyCurve_mem {X Y : Type*} (H : ℕ → X × I → Y) (S : Set Y)
    (hS : ∀ n x t, H n (x,t)∈S) (n : ℕ) (z : ℝ × X) : familyCurve H n z∈S := by
  induction n using Nat.twoStepInduction generalizing z with
  | zero => exact hS 0 z.2 0
  | one => exact hS 0 z.2 _
  | more n ih ih' =>
    rw [familyCurve]; dsimp only; split_ifs
    · exact ih' _
    · exact hS (n+1) z.2 _

theorem familyCurve_fixed {X Y : Type*} (H : ℕ → X × I → Y) (x : X) (b : Y)
    (hfix : ∀ n t, H n (x,t)=b) (n : ℕ) (t : ℝ) : familyCurve H n (t,x)=b := by
  induction n using Nat.twoStepInduction generalizing t with
  | zero => exact hfix 0 0
  | one => exact hfix 0 _
  | more n ih ih' =>
    rw [familyCurve]; dsimp only; split_ifs
    · exact ih' _
    · exact hfix (n+1) _

def familyHomotopy {X Y : Type*} (H : ℕ → X × I → Y) (n : ℕ) (z : X × I) : Y :=
  familyCurve H n ((z.2 : ℝ),z.1)

theorem familyHomotopy_joint {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (H : ℕ → X × I → Y) (hseam : ∀ n x, H n (x,1)=H (n+1) (x,0))
    (hjoint : ∀ n, ∃ J : ℝ≥0, LipschitzWith J (H n)) (n : ℕ) :
    ∃ J : ℝ≥0, LipschitzWith J (familyHomotopy H n) := by
  obtain ⟨J,hJ⟩ := familyCurve_joint H hseam hjoint n
  have he : LipschitzWith 1 (fun z : X × I => ((z.2 : ℝ),z.1)) := by
    apply LipschitzWith.of_dist_le_mul; intro x y
    change max (dist x.2 y.2) (dist x.1 y.1) ≤ (1 : ℝ)*max (dist x.1 y.1) (dist x.2 y.2)
    simp only [one_mul,max_comm]
    exact le_rfl
  exact ⟨J,by simpa only [familyHomotopy,Function.comp_def,mul_one] using hJ.comp he⟩

theorem familyHomotopy_track {X Y : Type*} [MetricSpace Y] (H : ℕ → X × I → Y)
    (hseam : ∀ n x, H n (x,1)=H (n+1) (x,0)) (D : ℝ≥0)
    (htrack : ∀ n x, LipschitzWith D (fun t : I => H n (x,t))) (n : ℕ) (x : X) :
    LipschitzWith ((n : ℝ≥0)*D) (fun t : I => familyHomotopy H n (x,t)) := by
  have he : LipschitzWith 1 ((↑) : I → ℝ) := by
    apply LipschitzWith.of_dist_le_mul; intro x y
    change dist x y ≤ (1 : ℝ)*dist x y; simp
  simpa only [familyHomotopy,Function.comp_def,mul_one] using (familyCurve_track H hseam D htrack n x).comp he

end
end AbelianTargets
