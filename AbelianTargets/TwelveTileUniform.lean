import AbelianTargets.TwelveTileFields
import AbelianTargets.DirectionSaturation

namespace AbelianTargets.TwelveTiles

open scoped BigOperators

variable {p q m : ℕ} {hp : 5 ≤ p} {hq : 5 ≤ q}
variable {V : Type*} {H : SimpleGraph V}

theorem wordVector_constant (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (w : Word) (d : Lattice m)
    (hfirst : ∀ x, cycleVector laws f w.first x = d)
    (hsecond : ∀ l, w.second = some l → ∀ x, cycleVector laws f l x = d)
    (x : ℕ) : wordVector laws f w x = d := by
  cases hs : w.second with
  | none => rw [wordVector_none laws f w hs]; exact hfirst x
  | some l =>
    by_cases hx : x < w.headLength p q
    · rw [wordVector_before laws f w x hx]; exact hfirst x
    · rw [wordVector_after laws f w l hs x (by omega)]; exact hsecond l hs _

def HorizontalWord (w : Word) : Prop :=
  2 ≤ w.first.val ∧ ∀ l, w.second = some l → 2 ≤ l.val

def VerticalWord (w : Word) : Prop :=
  w.first.val < 2 ∧ ∀ l, w.second = some l → l.val < 2

theorem topWord_horizontal (p q : ℕ) (t : Fin 12) : HorizontalWord (topWord p q t) := by
  fin_cases t <;> norm_num [HorizontalWord, topWord, single, pair, repeatWord]
  all_goals intro l h; cases h

theorem bottomWord_horizontal (p q : ℕ) (t : Fin 12) : HorizontalWord (bottomWord p q t) := by
  fin_cases t <;> norm_num [HorizontalWord, bottomWord, single, pair, repeatWord]
  all_goals intro l h; cases h

theorem leftWord_vertical (p q : ℕ) (t : Fin 12) : VerticalWord (leftWord p q t) := by
  fin_cases t <;> norm_num [VerticalWord, leftWord, single, pair, repeatWord]
  all_goals intro l h; cases h

theorem rightWord_vertical (p q : ℕ) (t : Fin 12) : VerticalWord (rightWord p q t) := by
  fin_cases t <;> norm_num [VerticalWord, rightWord, single, pair, repeatWord]
  all_goals intro l h; cases h

theorem horizontal_word_constant (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (u : SignedDirection m)
    (hcycles : ∀ l : Fin 4, 2 ≤ l.val → ∀ x, cycleVector laws f l x = u.vector)
    (w : Word) (hw : HorizontalWord w) (x : ℕ) : wordVector laws f w x = u.vector :=
  wordVector_constant laws f w u.vector (hcycles w.first hw.1)
    (fun l hl => hcycles l (hw.2 l hl)) x

theorem vertical_word_constant (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (v : SignedDirection m)
    (hcycles : ∀ l : Fin 4, l.val < 2 → ∀ x, cycleVector laws f l x = v.vector)
    (w : Word) (hw : VerticalWord w) (x : ℕ) : wordVector laws f w x = v.vector :=
  wordVector_constant laws f w v.vector (hcycles w.first hw.1)
    (fun l hl => hcycles l (hw.2 l hl)) x

theorem rowTotal_constant_of_cycles (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (u v : SignedDirection m)
    (hu : ∀ l : Fin 4, 2 ≤ l.val → ∀ x, cycleVector laws f l x = u.vector)
    (hv : ∀ l : Fin 4, l.val < 2 → ∀ x, cycleVector laws f l x = v.vector)
    (t : Fin 12) (y : ℕ) (hy : y ≤ height p q t) :
    rowTotal laws f t y = width p q t • u.vector := by
  induction y with
  | zero =>
    unfold rowTotal
    calc
      _ = ∑ x ∈ Finset.range (width p q t), u.vector := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [horizontalVector_top laws f t x (Finset.mem_range.mp hx)]
        exact horizontal_word_constant laws f u hu _ (topWord_horizontal p q t) x
      _ = _ := by simp
  | succ y ih =>
    have hd := rowTotal_difference laws f t y (by omega)
    rw [verticalVector_right laws f t y (by omega), verticalVector_left laws f t y (by omega),
      vertical_word_constant laws f v hv _ (rightWord_vertical p q t),
      vertical_word_constant laws f v hv _ (leftWord_vertical p q t), sub_self] at hd
    exact (sub_eq_zero.mp hd).trans (ih (by omega))

theorem horizontalVector_constant_of_cycles (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (u v : SignedDirection m)
    (hu : ∀ l : Fin 4, 2 ≤ l.val → ∀ x, cycleVector laws f l x = u.vector)
    (hv : ∀ l : Fin 4, l.val < 2 → ∀ x, cycleVector laws f l x = v.vector)
    (t : Fin 12) (x y : ℕ) (hx : x < width p q t) (hy : y ≤ height p q t) :
    horizontalVector laws f t x y = u.vector := by
  let s : Fin (width p q t) → SignedDirection m :=
    fun z => laws.direction (f.map_adj (horizontal_adj hp hq t z.val y z.isLt hy))
  have hsum : (∑ z, (s z).vector : Lattice m) = width p q t • u.vector := by
    calc
      (∑ z, (s z).vector : Lattice m) = ∑ z : Fin (width p q t), horizontalVector laws f t z.val y := by
        apply Finset.sum_congr rfl
        intro z _
        simp only [horizontalVector, dif_pos (show z.val < width p q t ∧ y ≤ height p q t from ⟨z.isLt, hy⟩)]
        rfl
      _ = rowTotal laws f t y := Fin.sum_univ_eq_sum_range (fun z => horizontalVector laws f t z y) (width p q t)
      _ = _ := rowTotal_constant_of_cycles laws f u v hu hv t y hy
  have hs := signedDirection_sum_saturation s u hsum ⟨x, hx⟩
  unfold horizontalVector
  rw [dif_pos ⟨hx, hy⟩]
  exact congrArg SignedDirection.vector hs

theorem verticalVector_constant_of_cycles (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (u v : SignedDirection m)
    (hu : ∀ l : Fin 4, 2 ≤ l.val → ∀ x, cycleVector laws f l x = u.vector)
    (hv : ∀ l : Fin 4, l.val < 2 → ∀ x, cycleVector laws f l x = v.vector)
    (t : Fin 12) (x y : ℕ) (hx : x ≤ width p q t) (hy : y < height p q t) :
    verticalVector laws f t x y = v.vector := by
  induction x with
  | zero =>
    rw [verticalVector_left laws f t y hy]
    exact vertical_word_constant laws f v hv _ (leftWord_vertical p q t) y
  | succ x ih =>
    have hd := tile_curl laws f t x y (by omega) hy
    rw [horizontalVector_constant_of_cycles laws f u v hu hv t x (y + 1) (by omega) (by omega),
      horizontalVector_constant_of_cycles laws f u v hu hv t x y (by omega) (by omega),
      sub_self] at hd
    exact (sub_eq_zero.mp hd.symm).trans (ih (by omega))

end AbelianTargets.TwelveTiles
