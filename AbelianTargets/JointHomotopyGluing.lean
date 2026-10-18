import AbelianTargets.RelativePathBounds

/-! # Joint Lipschitz bounds for concatenated homotopies -/

namespace AbelianTargets

open scoped unitInterval NNReal

noncomputable section

theorem lipschitz_glue_product_at {E Z : Type*} [PseudoMetricSpace E] [PseudoMetricSpace Z]
    {K : ℝ≥0} (f g : ℝ × E → Z) (hf : LipschitzWith K f) (hg : LipschitzWith K g)
    (c : ℝ) (hmatch : ∀ u, f (c,u) = g (c,u)) :
    LipschitzWith (2*K) (fun x => if x.1 ≤ c then f x else g x) := by
  have hcross : ∀ x y : ℝ × E, x.1 ≤ c → c ≤ y.1 →
      dist (f x) (g y) ≤ (2*K : ℝ≥0) * dist x y := by
    intro x y hx hy
    have hfx := hf.dist_le_mul x (c,x.2)
    have hgy := hg.dist_le_mul (c,x.2) y
    have hdx : dist x (c,x.2) = c-x.1 := by
      simp only [Prod.dist_eq, dist_self, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx)]
      rw [max_eq_left (by linarith)]
      ring
    have hdgy : dist (c,x.2) y ≤ (y.1-c)+dist x.2 y.2 := by
      rw [Prod.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hy)]
      exact max_le (by have := dist_nonneg (x := x.2) (y := y.2); linarith)
        (by linarith)
    have hd₁ : y.1-x.1 ≤ dist x y := by
      have hh : dist x.1 y.1 ≤ dist x y := le_max_left _ _
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hx.trans hy))] at hh
      simpa only [neg_sub] using hh
    have hd₂ : dist x.2 y.2 ≤ dist x y := le_max_right _ _
    have htri : dist (f x) (g y) ≤ dist (f x) (f (c,x.2)) + dist (g (c,x.2)) (g y) := by
      simpa only [hmatch] using dist_triangle (f x) (f (c,x.2)) (g y)
    rw [hdx] at hfx
    have hgy' := hgy.trans (mul_le_mul_of_nonneg_left hdgy K.2)
    calc
      _ ≤ (K : ℝ)*((y.1-x.1)+dist x.2 y.2) := by linarith
      _ ≤ (K : ℝ)*(dist x y+dist x y) :=
        mul_le_mul_of_nonneg_left (add_le_add hd₁ hd₂) K.2
      _ = _ := by simp only [NNReal.coe_mul,NNReal.coe_ofNat]; ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x.1 ≤ c <;> by_cases hy : y.1 ≤ c
  · simp only [if_pos hx, if_pos hy]
    exact (hf.dist_le_mul x y).trans (by
      simp only [NNReal.coe_mul, NNReal.coe_ofNat]
      have hh : 0 ≤ (K : ℝ)*dist x y := mul_nonneg K.2 dist_nonneg
      linarith)
  · simp only [if_pos hx,if_neg hy]
    exact hcross x y hx (le_of_not_ge hy)
  · simp only [if_neg hx,if_pos hy]
    rw [dist_comm,dist_comm x y]
    exact hcross y x hy (le_of_not_ge hx)
  · simp only [if_neg hx,if_neg hy]
    exact (hg.dist_le_mul x y).trans (by
      simp only [NNReal.coe_mul, NNReal.coe_ofNat]
      have hh : 0 ≤ (K : ℝ)*dist x y := mul_nonneg K.2 dist_nonneg
      linarith)

theorem homotopy_trans_joint_lipschitz {Z : Type*} [MetricSpace Z]
    {p q : Z} {P Q R : Path p q} (F : P.Homotopy Q) (G : Q.Homotopy R)
    {K L : ℝ≥0} (hF : LipschitzWith K F) (hG : LipschitzWith L G) :
    LipschitzWith (4*max K L) (F.trans G) := by
  let a : ℝ × I → I × I := fun x => (clampInterval (2*x.1),x.2)
  let b : ℝ × I → I × I := fun x => (clampInterval (2*x.1-1),x.2)
  have ha : LipschitzWith 2 a := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hc := ((lipschitz_clampInterval.comp (lipschitz_affine_le 2 2 0 (by norm_num)))).dist_le_mul x.1 y.1
    simp only [Function.comp_def,NNReal.coe_mul,NNReal.coe_one,NNReal.coe_ofNat,add_zero,one_mul] at hc
    change max (dist (clampInterval (2*x.1)) (clampInterval (2*y.1))) (dist x.2 y.2) ≤ _
    apply max_le
    · simpa using hc.trans (mul_le_mul_of_nonneg_left (le_max_left (dist x.1 y.1) (dist x.2 y.2)) (by norm_num : (0:ℝ)≤2))
    · have hh : dist x.2 y.2 ≤ dist x y := le_max_right _ _
      simp only [NNReal.coe_ofNat]; nlinarith [dist_nonneg (x := x) (y := y)]
  have hb : LipschitzWith 2 b := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hc := ((lipschitz_clampInterval.comp (lipschitz_affine_le 2 2 (-1) (by norm_num)))).dist_le_mul x.1 y.1
    simp only [Function.comp_def,NNReal.coe_mul,NNReal.coe_one,NNReal.coe_ofNat,one_mul] at hc
    change max (dist (clampInterval (2*x.1-1)) (clampInterval (2*y.1-1))) (dist x.2 y.2) ≤ _
    apply max_le
    · simpa using hc.trans (mul_le_mul_of_nonneg_left (le_max_left (dist x.1 y.1) (dist x.2 y.2)) (by norm_num : (0:ℝ)≤2))
    · have hh : dist x.2 y.2 ≤ dist x y := le_max_right _ _
      simp only [NNReal.coe_ofNat]; nlinarith [dist_nonneg (x := x) (y := y)]
  have hf : LipschitzWith (2*max K L) (fun x => F (a x)) := by
    exact (hF.weaken (le_max_left K L)).comp ha |>.weaken (by ring_nf; exact le_rfl)
  have hg : LipschitzWith (2*max K L) (fun x => G (b x)) := by
    exact (hG.weaken (le_max_right K L)).comp hb |>.weaken (by ring_nf; exact le_rfl)
  have hmatch : ∀ u : I, F (a (1/2,u)) = G (b (1/2,u)) := by
    intro u
    have ha' : a (1/2,u) = (1,u) := by apply Prod.ext <;> simp [a,clampInterval]
    have hb' : b (1/2,u) = (0,u) := by apply Prod.ext <;> simp [b,clampInterval]
    rw [ha',hb']
    exact (F.map_one_left u).trans (G.map_zero_left u).symm
  have hh := lipschitz_glue_product_at (fun x => F (a x)) (fun x => G (b x)) hf hg (1/2) hmatch
  let e : I × I → ℝ × I := fun x => ((x.1 : ℝ),x.2)
  have he : LipschitzWith 1 e := by
    apply LipschitzWith.of_dist_le_mul; intro x y
    change dist x y ≤ (1 : ℝ)*dist x y
    simp
  have hres := hh.comp he
  have heq : (fun x : I × I => if (x.1 : ℝ) ≤ 1/2 then F (a (e x)) else G (b (e x))) = F.trans G := by
    funext x
    rw [Path.Homotopy.trans_apply]
    split_ifs with h
    · congr 1
      apply Prod.ext
      · change clampInterval (2*(x.1 : ℝ)) = _
        exact clampInterval_coe ⟨2*(x.1 : ℝ),⟨by linarith [x.1.property.1],by linarith⟩⟩
      · rfl
    · congr 1
      apply Prod.ext
      · change clampInterval (2*(x.1 : ℝ)-1) = _
        exact clampInterval_coe ⟨2*(x.1 : ℝ)-1,⟨by linarith,by linarith [x.1.property.2]⟩⟩
      · rfl
  simpa only [Function.comp_def,heq,mul_one,show 2*(2*max K L)=4*max K L by ring] using hres

end

end AbelianTargets
