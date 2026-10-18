import AbelianTargets.JointCarrierRows

/-! Coordinate identities for canonical endpoint padding and one appended edge. -/

namespace AbelianTargets
variable {V : Type*} [DecidableEq V]

theorem padRow_getD (N : ℕ) (z : V) (w : List V) (j : ℕ) :
    (padRow N z w).getD j z = w.getD j z := by
  simp only [padRow,List.getD_eq_getElem?_getD,List.getElem?_append]
  split_ifs with hj
  · rfl
  · rw [List.getElem?_eq_none (l := w) (i := j) (by omega)]
    simp only [List.getElem?_replicate,Option.getD_none]
    split <;> rfl

theorem list_getD_terminal {w : List V} {p : V} (hz : w.getLast? = some p)
    (j : ℕ) (hj : w.length-1 ≤ j) : w.getD j p = p := by
  by_cases hj' : j < w.length
  · have he : j = w.length-1 := by omega
    simp only [List.getD_eq_getElem?_getD,he,←List.getLast?_eq_getElem?,hz,Option.getD_some]
  · simp only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (l := w) (i := j) (by omega),Option.getD_none]

theorem getD_append_endpoint (w : List V) (p q : V) (j : ℕ) :
    (w++[q]).getD j q = if j < w.length then w.getD j p else q := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append]
  by_cases hj : j < w.length
  · rw [if_pos hj,if_pos hj]
    rw [List.getElem?_eq_getElem hj]
    rfl
  · rw [if_neg hj,if_neg hj]
    cases j-w.length <;> rfl

end AbelianTargets
