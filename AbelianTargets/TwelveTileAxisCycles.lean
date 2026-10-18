import AbelianTargets.TwelveTileTorus

namespace AbelianTargets.TwelveTiles

variable {p q : ℕ}

def axisCycleLabel (s : Fin 2) : Fin 4 := if s.val = 0 then 2 else 0

@[simp] theorem axisCycleLength (p q : ℕ) (s : Fin 2) :
    cycleLength p q (axisCycleLabel s) = p := by
  fin_cases s <;> norm_num [axisCycleLabel, cycleLength]

def AxisStep (hp : 5 ≤ p) (hq : 5 ≤ q) (s : Fin 2) (u v : Vertex p q) : Prop :=
  if s.val = 0 then HorizontalStep hp hq u v else VerticalStep hp hq u v

theorem AxisStep.adj {hp : 5 ≤ p} {hq : 5 ≤ q} {s : Fin 2} {u v : Vertex p q}
    (h : AxisStep hp hq s u v) : (graph p q hp hq).Adj u v := by
  unfold AxisStep at h
  split at h
  · exact h.adj
  · exact h.adj

def axisCyclePoint (hp : 5 ≤ p) (hq : 5 ≤ q) (s : Fin 2) (z : ZMod p) : Vertex p q :=
  cycleAt hp hq (axisCycleLabel s) z.val

theorem axisCyclePoint_step (hp : 5 ≤ p) (hq : 5 ≤ q) (s : Fin 2) (z : ZMod p) :
    AxisStep hp hq s (axisCyclePoint hp hq s z) (axisCyclePoint hp hq s (z+1)) := by
  letI : NeZero p := ⟨by omega⟩
  have heq : axisCyclePoint hp hq s (z+1) =
      cycleAt hp hq (axisCycleLabel s) (z.val+1) := by
    unfold axisCyclePoint
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (show 1 < p by omega)]
    simpa only [axisCycleLength] using cycleAt_mod hp hq (axisCycleLabel s) (z.val+1)
  rw [heq]
  fin_cases s
  · exact cycle_horizontalStep hp hq 2 (by norm_num) z.val (by simpa [cycleLength] using z.val_lt)
  · exact cycle_verticalStep hp hq 0 (by norm_num) z.val (by simpa [cycleLength] using z.val_lt)

end AbelianTargets.TwelveTiles
