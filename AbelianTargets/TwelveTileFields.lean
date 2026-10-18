import AbelianTargets.TwelveTiles
import AbelianTargets.Dimension
import Mathlib.Tactic.Abel

namespace AbelianTargets.TwelveTiles

open scoped BigOperators

theorem sum_range_difference {A : Type*} [AddCommGroup A] (f : ℕ → A) (n : ℕ) :
    (∑ x ∈ Finset.range n, (f (x + 1) - f x)) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; abel

theorem periodic_nat_multiple {A : Type*} {f : ℕ → A} {L : ℕ}
    (hperiod : ∀ x, f (x + L) = f x) (n x : ℕ) : f (n * L + x) = f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : (n + 1) * L + x = (n * L + x) + L := by ring
    rw [heq, hperiod, ih]

theorem sum_range_periodic_mul {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (L : ℕ) (hperiod : ∀ x, f (x + L) = f x) (n : ℕ) :
    (∑ x ∈ Finset.range (n * L), f x) = n • ∑ x ∈ Finset.range L, f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    simp only [periodic_nat_multiple hperiod, add_nsmul, one_nsmul]

variable {p q m : ℕ} {hp : 5 ≤ p} {hq : 5 ≤ q}
variable {V : Type*} {H : SimpleGraph V}

def edgeVector (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    {u v : Vertex p q} (h : (graph p q hp hq).Adj u v) : Lattice m :=
  (laws.direction (f.map_adj h)).vector

theorem edgeVector_congr (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    {u v u' v' : Vertex p q} (h : (graph p q hp hq).Adj u v)
    (h' : (graph p q hp hq).Adj u' v') (hu : u = u') (hv : v = v') :
    edgeVector laws f h = edgeVector laws f h' := by subst u'; subst v'; rfl

theorem edgeVector_reverse (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    {u v : Vertex p q} (h : (graph p q hp hq).Adj u v) :
    edgeVector laws f h.symm = -edgeVector laws f h := laws.reverse (f.map_adj h)

def horizontalVector (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (t : Fin 12) (x y : ℕ) : Lattice m :=
  if h : x < width p q t ∧ y ≤ height p q t then
    edgeVector laws f (horizontal_adj hp hq t x y h.1 h.2) else 0

def verticalVector (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (t : Fin 12) (x y : ℕ) : Lattice m :=
  if h : x ≤ width p q t ∧ y < height p q t then
    edgeVector laws f (vertical_adj hp hq t x y h.1 h.2) else 0

def cycleVector (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (l : Fin 4) (x : ℕ) : Lattice m := edgeVector laws f (cycle_adj_all hp hq l x)

def wordVector (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (w : Word) (x : ℕ) : Lattice m := edgeVector laws f (w.step_adj hp hq x)

theorem cycleVector_periodic (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (l : Fin 4) (x : ℕ) :
    cycleVector laws f l (x + cycleLength p q l) = cycleVector laws f l x := by
  unfold cycleVector
  apply edgeVector_congr
  · exact cycleAt_add_period hp hq l x
  · have heq : x + cycleLength p q l + 1 = x + 1 + cycleLength p q l := by omega
    rw [heq]
    exact cycleAt_add_period hp hq l (x + 1)

theorem wordVector_none (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (w : Word) (hw : w.second = none) (x : ℕ) :
    wordVector laws f w x = cycleVector laws f w.first x := by
  unfold wordVector cycleVector
  apply edgeVector_congr <;> simp [Word.at, hw]

theorem wordVector_before (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (w : Word) (x : ℕ) (hx : x < w.headLength p q) :
    wordVector laws f w x = cycleVector laws f w.first x := by
  cases hs : w.second with
  | none => exact wordVector_none laws f w hs x
  | some k =>
    unfold wordVector cycleVector
    apply edgeVector_congr
    · simp [Word.at, hs, hx]
    · by_cases hxs : x + 1 < w.headLength p q
      · simp [Word.at, hs, hxs]
      · have heq : x + 1 = w.headLength p q := by omega
        simp [Word.at, hs, heq, Word.headLength]

theorem wordVector_after (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (w : Word) (k : Fin 4) (hs : w.second = some k) (x : ℕ)
    (hx : w.headLength p q ≤ x) :
    wordVector laws f w x = cycleVector laws f k (x - w.headLength p q) := by
  unfold wordVector cycleVector
  apply edgeVector_congr
  · simp [Word.at, hs, Nat.not_lt.mpr hx]
  · have hxs : ¬ x + 1 < w.headLength p q := by omega
    have heq : x + 1 - w.headLength p q = x - w.headLength p q + 1 := by omega
    simp [Word.at, hs, hxs, heq]

def cycleTotal (laws : DirectionLaws H m) (f : graph p q hp hq →g H) (l : Fin 4) : Lattice m :=
  ∑ x ∈ Finset.range (cycleLength p q l), cycleVector laws f l x

def wordTotal (laws : DirectionLaws H m) (f : graph p q hp hq →g H) (w : Word) : Lattice m :=
  ∑ x ∈ Finset.range (w.length p q), wordVector laws f w x

theorem wordTotal_none (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (w : Word) (hw : w.second = none) :
    wordTotal laws f w = w.copies • cycleTotal laws f w.first := by
  unfold wordTotal Word.length
  simp only [hw, Option.map_none, Option.getD_none, add_zero]
  simp only [wordVector_none laws f w hw, Word.headLength]
  exact sum_range_periodic_mul _ _ (cycleVector_periodic laws f w.first) w.copies

theorem wordTotal_some (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (w : Word) (k : Fin 4) (hw : w.second = some k) :
    wordTotal laws f w = w.copies • cycleTotal laws f w.first + cycleTotal laws f k := by
  unfold wordTotal Word.length
  simp only [hw, Option.map_some, Option.getD_some]
  rw [Finset.sum_range_add]
  congr 1
  · rw [show (∑ x ∈ Finset.range (w.headLength p q), wordVector laws f w x) =
        ∑ x ∈ Finset.range (w.headLength p q), cycleVector laws f w.first x from
      Finset.sum_congr rfl (fun x hx => wordVector_before laws f w x (Finset.mem_range.mp hx))]
    exact sum_range_periodic_mul _ _ (cycleVector_periodic laws f w.first) w.copies
  · apply Finset.sum_congr rfl
    intro x hx
    rw [wordVector_after laws f w k hw _ (by omega)]
    simp

theorem tile_curl (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (t : Fin 12) (x y : ℕ) (hx : x < width p q t) (hy : y < height p q t) :
    horizontalVector laws f t x (y + 1) - horizontalVector laws f t x y =
      verticalVector laws f t (x + 1) y - verticalVector laws f t x y := by
  let ha := horizontal_adj hp hq t x y hx (by omega)
  let hb := vertical_adj hp hq t (x + 1) y (by omega) hy
  let hc := horizontal_adj hp hq t x (y + 1) hx (by omega)
  let hd := vertical_adj hp hq t x y (by omega) hy
  have h := laws.four_walk (f.map_adj ha) (f.map_adj hb)
    (f.map_adj hc.symm) (f.map_adj hd.symm)
  change edgeVector laws f ha + edgeVector laws f hb +
    edgeVector laws f hc.symm + edgeVector laws f hd.symm = 0 at h
  rw [edgeVector_reverse laws f hc, edgeVector_reverse laws f hd] at h
  simp only [horizontalVector, verticalVector,
    dif_pos (show x < width p q t ∧ y ≤ height p q t from ⟨hx, by omega⟩),
    dif_pos (show x < width p q t ∧ y + 1 ≤ height p q t from ⟨hx, by omega⟩),
    dif_pos (show x + 1 ≤ width p q t ∧ y < height p q t from ⟨by omega, hy⟩),
    dif_pos (show x ≤ width p q t ∧ y < height p q t from ⟨by omega, hy⟩)]
  ext i
  have hi := congrFun h i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.zero_apply] at hi ⊢
  omega

def rowTotal (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (t : Fin 12) (y : ℕ) : Lattice m :=
  ∑ x ∈ Finset.range (width p q t), horizontalVector laws f t x y

theorem rowTotal_difference (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (t : Fin 12) (y : ℕ) (hy : y < height p q t) :
    rowTotal laws f t (y + 1) - rowTotal laws f t y =
      verticalVector laws f t (width p q t) y - verticalVector laws f t 0 y := by
  unfold rowTotal
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun x hx => tile_curl laws f t x y (Finset.mem_range.mp hx) hy)]
  exact sum_range_difference (verticalVector laws f t · y) (width p q t)

theorem tile_boundary_vectors (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (t : Fin 12) :
    rowTotal laws f t (height p q t) - rowTotal laws f t 0 =
      (∑ y ∈ Finset.range (height p q t), verticalVector laws f t (width p q t) y) -
      (∑ y ∈ Finset.range (height p q t), verticalVector laws f t 0 y) := by
  rw [← sum_range_difference (rowTotal laws f t) (height p q t), ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun y hy => rowTotal_difference laws f t y (Finset.mem_range.mp hy))

theorem horizontalVector_top (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (t : Fin 12) (x : ℕ) (hx : x < width p q t) :
    horizontalVector laws f t x 0 = wordVector laws f (topWord p q t) x := by
  unfold horizontalVector wordVector
  rw [dif_pos ⟨hx, Nat.zero_le _⟩]
  apply edgeVector_congr <;> exact tileVertex_top hp hq t _

theorem horizontalVector_bottom (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (t : Fin 12) (x : ℕ) (hx : x < width p q t) :
    horizontalVector laws f t x (height p q t) = wordVector laws f (bottomWord p q t) x := by
  unfold horizontalVector wordVector
  rw [dif_pos ⟨hx, le_rfl⟩]
  apply edgeVector_congr
  · exact tileVertex_bottom hp hq t x
  · exact tileVertex_bottom hp hq t (x + 1)

theorem verticalVector_left (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (t : Fin 12) (y : ℕ) (hy : y < height p q t) :
    verticalVector laws f t 0 y = wordVector laws f (leftWord p q t) y := by
  unfold verticalVector wordVector
  rw [dif_pos ⟨Nat.zero_le _, hy⟩]
  apply edgeVector_congr
  · exact tileVertex_left hp hq t y (by omega)
  · exact tileVertex_left hp hq t (y + 1) (by omega)

theorem verticalVector_right (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (t : Fin 12) (y : ℕ) (hy : y < height p q t) :
    verticalVector laws f t (width p q t) y = wordVector laws f (rightWord p q t) y := by
  unfold verticalVector wordVector
  rw [dif_pos ⟨le_rfl, hy⟩]
  apply edgeVector_congr
  · exact tileVertex_right hp hq t y (by omega)
  · exact tileVertex_right hp hq t (y + 1) (by omega)

theorem tile_boundary_totals (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (t : Fin 12) :
    wordTotal laws f (bottomWord p q t) - wordTotal laws f (topWord p q t) =
      wordTotal laws f (rightWord p q t) - wordTotal laws f (leftWord p q t) := by
  have h := tile_boundary_vectors laws f t
  have ht : rowTotal laws f t 0 = wordTotal laws f (topWord p q t) := by
    unfold rowTotal wordTotal
    exact Finset.sum_congr rfl (fun x hx => horizontalVector_top laws f t x (Finset.mem_range.mp hx))
  have hb : rowTotal laws f t (height p q t) = wordTotal laws f (bottomWord p q t) := by
    unfold rowTotal wordTotal
    rw [bottom_length]
    exact Finset.sum_congr rfl (fun x hx => horizontalVector_bottom laws f t x (Finset.mem_range.mp hx))
  have hr : (∑ y ∈ Finset.range (height p q t), verticalVector laws f t (width p q t) y) =
      wordTotal laws f (rightWord p q t) := by
    unfold wordTotal
    rw [right_length]
    exact Finset.sum_congr rfl (fun y hy => verticalVector_right laws f t y (Finset.mem_range.mp hy))
  have hl : (∑ y ∈ Finset.range (height p q t), verticalVector laws f t 0 y) =
      wordTotal laws f (leftWord p q t) := by
    unfold wordTotal
    exact Finset.sum_congr rfl (fun y hy => verticalVector_left laws f t y (Finset.mem_range.mp hy))
  rwa [ht, hb, hr, hl] at h

theorem wordTotal_single (laws : DirectionLaws H m) (f : graph p q hp hq →g H) (l : Fin 4) :
    wordTotal laws f (single l) = cycleTotal laws f l := by
  simpa [single] using wordTotal_none laws f (single l) rfl

theorem wordTotal_repeat (laws : DirectionLaws H m) (f : graph p q hp hq →g H) (l : Fin 4) (n : ℕ) :
    wordTotal laws f (repeatWord l n) = n • cycleTotal laws f l :=
  wordTotal_none laws f (repeatWord l n) rfl

theorem cycle_totals_horizontal_relation (laws : DirectionLaws H m) (f : graph p q hp hq →g H) :
    q • cycleTotal laws f 2 = p • cycleTotal laws f 3 := by
  have h := tile_boundary_totals laws f (8 : Fin 12)
  norm_num only [topWord, bottomWord, rightWord, leftWord] at h
  rw [wordTotal_repeat, wordTotal_repeat, wordTotal_single, sub_self] at h
  exact (sub_eq_zero.mp h).symm

theorem cycle_totals_vertical_relation (laws : DirectionLaws H m) (f : graph p q hp hq →g H) :
    q • cycleTotal laws f 0 = p • cycleTotal laws f 1 := by
  have h := tile_boundary_totals laws f (10 : Fin 12)
  norm_num only [topWord, bottomWord, rightWord, leftWord] at h
  rw [wordTotal_single, sub_self, wordTotal_repeat, wordTotal_repeat] at h
  exact (sub_eq_zero.mp h.symm).symm

end AbelianTargets.TwelveTiles
