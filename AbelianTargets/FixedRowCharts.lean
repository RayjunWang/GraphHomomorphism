import AbelianTargets.CanonicalRows

/-! Four-corner simplex certificates for contextual equal-slot replacements. -/

namespace AbelianTargets

variable {V : Type*} [DecidableEq V] {Face : Finset V → Prop}

theorem contextual_getD_first (p s : List V) (a b c d : V) :
    (p ++ [a,b,c] ++ s).getD p.length d = a := by
  induction p with
  | nil => rfl
  | cons v p ih => simpa only [List.length_cons,List.cons_append,List.getD_cons_succ] using ih

theorem contextual_getD_middle (p s : List V) (a b c d : V) :
    (p ++ [a,b,c] ++ s).getD (p.length+1) d = b := by
  induction p with
  | nil => rfl
  | cons v p ih => simpa only [List.length_cons,List.cons_append,List.getD_cons_succ] using ih

theorem contextual_getD_third (p s : List V) (a b c d : V) :
    (p ++ [a,b,c] ++ s).getD (p.length+2) d = c := by
  induction p with
  | nil => rfl
  | cons v p ih => simpa only [List.length_cons,List.cons_append,List.getD_cons_succ] using ih

theorem contextual_getD_unchanged (p s : List V) (a b b' c d : V) (j : ℕ)
    (hj : j ≠ p.length+1) :
    (p ++ [a,b,c] ++ s).getD j d = (p ++ [a,b',c] ++ s).getD j d := by
  induction p generalizing j with
  | nil =>
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => exact False.elim (hj rfl)
      | succ j => rfl
  | cons v p ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simpa only [List.cons_append,List.getD_cons_succ] using ih j (by
        simp only [List.length_cons] at hj
        omega)

theorem contextual_four_corners_face (hd : FaceDownward Face)
    (p s : List V) (a b b' c z : V) (hf : Face {a,b,b',c})
    (hv : ValidRow Face (p ++ [a,b,c] ++ s)) (j : ℕ)
    (hj : j+1 < (p ++ [a,b,c] ++ s).length) :
    Face {(p ++ [a,b,c] ++ s).getD j z,
      (p ++ [a,b,c] ++ s).getD (j+1) z,
      (p ++ [a,b',c] ++ s).getD j z,
      (p ++ [a,b',c] ++ s).getD (j+1) z} := by
  by_cases h₀ : j = p.length
  · subst j
    rw [contextual_getD_first,contextual_getD_middle,
      contextual_getD_first,contextual_getD_middle]
    apply hd hf
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
    obtain rfl | rfl | rfl | rfl := hv <;> simp
  · by_cases h₁ : j = p.length+1
    · subst j
      rw [contextual_getD_middle,contextual_getD_third,
        contextual_getD_middle,contextual_getD_third]
      apply hd hf
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
      obtain rfl | rfl | rfl | rfl := hv <;> simp
    · rw [← contextual_getD_unchanged p s a b b' c z j h₁,
        ← contextual_getD_unchanged p s a b b' c z (j+1) (by omega)]
      apply hd (hv.edge_getD z j hj)
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
      tauto

end AbelianTargets
