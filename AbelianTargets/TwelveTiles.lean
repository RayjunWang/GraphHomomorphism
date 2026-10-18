import AbelianTargets.Actions
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The width-one twelve-tile graph

The finite construction in arXiv:2609.39824, Section 7.2, and GJKS,
Section 2.3. The four based cycles are indexed `a=0,b=1,c=2,d=3`.
Every tile interior is private; equally named boundary positions are
identified. Positive grid steps are recorded explicitly, avoiding any
unproved choice of an edge label.
-/

namespace AbelianTargets.TwelveTiles

open scoped BigOperators

def cycleLength (p q : ℕ) (l : Fin 4) : ℕ := if l.val % 2 = 0 then p else q

structure Word where
  first : Fin 4
  copies : ℕ := 1
  second : Option (Fin 4) := none
  deriving DecidableEq

def Word.headLength (p q : ℕ) (w : Word) := w.copies * cycleLength p q w.first
def Word.length (p q : ℕ) (w : Word) :=
  w.headLength p q + (w.second.map (cycleLength p q)).getD 0

def single (l : Fin 4) : Word := ⟨l, 1, none⟩
def pair (l k : Fin 4) : Word := ⟨l, 1, some k⟩
def repeatWord (l : Fin 4) (n : ℕ) : Word := ⟨l, n, none⟩

def topWord (p q : ℕ) (t : Fin 12) : Word :=
  match t.val with
  | 0 => single 2 | 1 => single 2 | 2 => single 3 | 3 => single 3
  | 4 => pair 3 2 | 5 => single 2 | 6 => pair 2 3 | 7 => single 2
  | 8 => repeatWord 2 q | 9 => repeatWord 3 p | 10 => single 2 | _ => single 2

def bottomWord (p q : ℕ) (t : Fin 12) : Word :=
  match t.val with
  | 0 => single 2 | 1 => single 2 | 2 => single 3 | 3 => single 3
  | 4 => pair 2 3 | 5 => single 2 | 6 => pair 3 2 | 7 => single 2
  | 8 => repeatWord 3 p | 9 => repeatWord 2 q | 10 => single 2 | _ => single 2

def leftWord (p q : ℕ) (t : Fin 12) : Word :=
  match t.val with
  | 0 => single 0 | 1 => single 1 | 2 => single 0 | 3 => single 1
  | 4 => single 0 | 5 => pair 0 1 | 6 => single 0 | 7 => pair 1 0
  | 8 => single 0 | 9 => single 0 | 10 => repeatWord 0 q | _ => repeatWord 1 p

def rightWord (p q : ℕ) (t : Fin 12) : Word :=
  match t.val with
  | 0 => single 0 | 1 => single 1 | 2 => single 0 | 3 => single 1
  | 4 => single 0 | 5 => pair 1 0 | 6 => single 0 | 7 => pair 0 1
  | 8 => single 0 | 9 => single 0 | 10 => repeatWord 1 p | _ => repeatWord 0 q

def width (p q : ℕ) (t : Fin 12) := (topWord p q t).length p q
def height (p q : ℕ) (t : Fin 12) := (leftWord p q t).length p q

theorem bottom_length (p q : ℕ) (t : Fin 12) :
    (bottomWord p q t).length p q = width p q t := by
  fin_cases t <;>
    norm_num [bottomWord, width, topWord, single, pair, repeatWord,
      Word.length, Word.headLength, cycleLength] <;> ring

theorem right_length (p q : ℕ) (t : Fin 12) :
    (rightWord p q t).length p q = height p q t := by
  fin_cases t <;>
    norm_num [rightWord, height, leftWord, single, pair, repeatWord,
      Word.length, Word.headLength, cycleLength] <;> ring

theorem width_ge_five {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (t : Fin 12) :
    5 ≤ width p q t := by
  have hpq : 5 ≤ p * q := hp.trans (Nat.le_mul_of_pos_right p (by omega))
  have hqp : 5 ≤ q * p := by simpa only [mul_comm] using hpq
  fin_cases t <;>
    norm_num [width, topWord, single, pair, repeatWord,
      Word.length, Word.headLength, cycleLength] <;> omega

theorem height_ge_five {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (t : Fin 12) :
    5 ≤ height p q t := by
  have hpq : 5 ≤ p * q := hp.trans (Nat.le_mul_of_pos_right p (by omega))
  have hqp : 5 ≤ q * p := by simpa only [mul_comm] using hpq
  fin_cases t <;>
    norm_num [height, leftWord, single, pair, repeatWord,
      Word.length, Word.headLength, cycleLength] <;> omega

abbrev Vertex (p q : ℕ) :=
  Unit ⊕ ((Σ l : Fin 4, {z : Fin (cycleLength p q l) // z.val ≠ 0}) ⊕
    (Σ t : Fin 12, Fin (width p q t - 1) × Fin (height p q t - 1)))

def base (p q : ℕ) : Vertex p q := Sum.inl ()

def cyclePoint {p q : ℕ} (l : Fin 4) (z : Fin (cycleLength p q l)) : Vertex p q :=
  if hz : z.val = 0 then base p q else Sum.inr (Sum.inl ⟨l, ⟨z, hz⟩⟩)

theorem cycleLength_pos {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (l : Fin 4) :
    0 < cycleLength p q l := by unfold cycleLength; split <;> omega

theorem cycleLength_gt_one {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (l : Fin 4) :
    1 < cycleLength p q l := by unfold cycleLength; split <;> omega

def cycleAt {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (l : Fin 4) (x : ℕ) : Vertex p q :=
  cyclePoint l ⟨x % cycleLength p q l, Nat.mod_lt x (cycleLength_pos hp hq l)⟩

@[simp] theorem cycleAt_zero {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (l : Fin 4) :
    cycleAt hp hq l 0 = base p q := by simp [cycleAt, cyclePoint]

@[simp] theorem cycleAt_multiple {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (l : Fin 4) (n : ℕ) : cycleAt hp hq l (n * cycleLength p q l) = base p q := by
  simp [cycleAt, cyclePoint]

@[simp] theorem cycleAt_length {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (l : Fin 4) :
    cycleAt hp hq l (cycleLength p q l) = base p q := by
  simpa using cycleAt_multiple hp hq l 1

theorem cyclePoint_injective {p q : ℕ} (l : Fin 4) :
    Function.Injective (cyclePoint (p := p) (q := q) l) := by
  intro z w h
  by_cases hz : z.val = 0 <;> by_cases hw : w.val = 0
  · apply Fin.ext; exact hz.trans hw.symm
  · simp [cyclePoint, hz, hw, base] at h
  · simp [cyclePoint, hz, hw, base] at h
  · simpa [cyclePoint, hz, hw] using h

theorem cycleAt_succ_ne {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (l : Fin 4) (x : ℕ) : cycleAt hp hq l x ≠ cycleAt hp hq l (x + 1) := by
  intro h
  have hv := congrArg Fin.val (cyclePoint_injective l h)
  have hz : (x : ZMod (cycleLength p q l)) = (x + 1 : ℕ) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hv
  haveI : Fact (1 < cycleLength p q l) := ⟨cycleLength_gt_one hp hq l⟩
  have hzero : (1 : ZMod (cycleLength p q l)) = 0 := by
    rw [Nat.cast_add, Nat.cast_one] at hz
    apply add_left_cancel (a := (x : ZMod (cycleLength p q l)))
    simpa only [add_zero] using hz.symm
  exact one_ne_zero hzero

def Word.at {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (w : Word) (x : ℕ) : Vertex p q :=
  match w.second with
  | none => cycleAt hp hq w.first x
  | some k => if x < w.headLength p q then cycleAt hp hq w.first x
      else cycleAt hp hq k (x - w.headLength p q)

@[simp] theorem Word.at_zero {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (w : Word) :
    w.at hp hq 0 = base p q := by
  unfold Word.at
  cases w.second
  · simp
  · split
    · simp
    · simp

@[simp] theorem Word.at_end {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (w : Word) :
    w.at hp hq (w.length p q) = base p q := by
  unfold Word.at Word.length
  cases hs : w.second with
  | none => simp [Word.headLength]
  | some k => simp [Word.headLength]

theorem Word.at_succ_ne {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (w : Word) (x : ℕ) : w.at hp hq x ≠ w.at hp hq (x + 1) := by
  unfold Word.at
  cases hs : w.second with
  | none => exact cycleAt_succ_ne hp hq w.first x
  | some k =>
    by_cases hx : x < w.headLength p q
    · by_cases hxs : x + 1 < w.headLength p q
      · simpa [hx, hxs] using cycleAt_succ_ne hp hq w.first x
      · have heq : x + 1 = w.headLength p q := by omega
        have hbase : cycleAt hp hq w.first (x + 1) = base p q := by
          rw [heq]; exact cycleAt_multiple hp hq w.first w.copies
        have hn : cycleAt hp hq w.first x ≠ base p q := by
          rw [← hbase]
          exact cycleAt_succ_ne hp hq w.first x
        simpa [hx, hxs, heq] using hn
    · have hxs : ¬ x + 1 < w.headLength p q := by omega
      have hsub : x + 1 - w.headLength p q = (x - w.headLength p q) + 1 := by omega
      simpa [hx, hxs, hsub] using cycleAt_succ_ne hp hq k (x - w.headLength p q)

def tileVertex {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (t : Fin 12) (x y : ℕ) :
    Vertex p q :=
  if y = 0 then (topWord p q t).at hp hq x
  else if y = height p q t then (bottomWord p q t).at hp hq x
  else if x = 0 then (leftWord p q t).at hp hq y
  else if x = width p q t then (rightWord p q t).at hp hq y
  else if h : 0 < x ∧ x < width p q t ∧ 0 < y ∧ y < height p q t then
    Sum.inr (Sum.inr ⟨t, ⟨x - 1, by omega⟩, ⟨y - 1, by omega⟩⟩)
  else base p q

@[simp] theorem tileVertex_top {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (t : Fin 12) (x : ℕ) :
    tileVertex hp hq t x 0 = (topWord p q t).at hp hq x := by simp [tileVertex]

@[simp] theorem tileVertex_bottom {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (t : Fin 12) (x : ℕ) :
    tileVertex hp hq t x (height p q t) = (bottomWord p q t).at hp hq x := by
  have hh : height p q t ≠ 0 := by have := height_ge_five hp hq t; omega
  simp [tileVertex, hh]

theorem tileVertex_left {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (t : Fin 12) (y : ℕ) (hy : y ≤ height p q t) :
    tileVertex hp hq t 0 y = (leftWord p q t).at hp hq y := by
  by_cases hy0 : y = 0
  · subst y; simp
  by_cases hyh : y = height p q t
  · subst y
    rw [tileVertex_bottom]
    simp only [Word.at_zero]
    exact (Word.at_end hp hq (leftWord p q t)).symm
  · simp [tileVertex, hy0, hyh]

theorem tileVertex_right {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (t : Fin 12) (y : ℕ) (hy : y ≤ height p q t) :
    tileVertex hp hq t (width p q t) y = (rightWord p q t).at hp hq y := by
  have hw : width p q t ≠ 0 := by have := width_ge_five hp hq t; omega
  by_cases hy0 : y = 0
  · subst y
    rw [tileVertex_top]
    change (topWord p q t).at hp hq ((topWord p q t).length p q) = _
    simp
  by_cases hyh : y = height p q t
  · subst y
    rw [tileVertex_bottom, ← bottom_length, ← right_length]
    simp
  · simp [tileVertex, hy0, hyh, hw]

def interiorAt {p q : ℕ} (t : Fin 12) (x y : ℕ)
    (hx0 : 0 < x) (hx : x < width p q t)
    (hy0 : 0 < y) (hy : y < height p q t) : Vertex p q :=
  Sum.inr (Sum.inr ⟨t, ⟨x - 1, by omega⟩, ⟨y - 1, by omega⟩⟩)

theorem tileVertex_interior {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (t : Fin 12) (x y : ℕ)
    (hx0 : 0 < x) (hx : x < width p q t)
    (hy0 : 0 < y) (hy : y < height p q t) :
    tileVertex hp hq t x y = interiorAt t x y hx0 hx hy0 hy := by
  simp [tileVertex, interiorAt, Nat.ne_of_gt hx0, Nat.ne_of_lt hx,
    Nat.ne_of_gt hy0, Nat.ne_of_lt hy, hx0, hx, hy0, hy]

theorem Word.at_ne_interior {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (w : Word) (z : ℕ) (t : Fin 12) (x y : ℕ)
    (hx0 : 0 < x) (hx : x < width p q t)
    (hy0 : 0 < y) (hy : y < height p q t) :
    w.at hp hq z ≠ interiorAt t x y hx0 hx hy0 hy := by
  have hc : ∀ (l : Fin 4) (a : ℕ),
      cycleAt hp hq l a ≠ interiorAt t x y hx0 hx hy0 hy := by
    intro l a
    unfold cycleAt cyclePoint
    split <;> simp [base, interiorAt]
  cases hs : w.second with
  | none => simpa only [Word.at, hs] using hc w.first z
  | some k =>
    simp only [Word.at, hs]
    split
    · exact hc w.first z
    · exact hc k (z - w.headLength p q)

theorem interiorAt_x_injective {p q : ℕ} (t : Fin 12) (x x' y : ℕ)
    (hx0 : 0 < x) (hx : x < width p q t)
    (hx0' : 0 < x') (hx' : x' < width p q t)
    (hy0 : 0 < y) (hy : y < height p q t)
    (heq : interiorAt t x y hx0 hx hy0 hy = interiorAt t x' y hx0' hx' hy0 hy) :
    x = x' := by
  have hpair : (⟨x - 1, by omega⟩ : Fin (width p q t - 1)) = ⟨x' - 1, by omega⟩ := by
    simpa [interiorAt] using heq
  have hv := congrArg Fin.val hpair
  change x - 1 = x' - 1 at hv
  omega

theorem interiorAt_y_injective {p q : ℕ} (t : Fin 12) (x y y' : ℕ)
    (hx0 : 0 < x) (hx : x < width p q t)
    (hy0 : 0 < y) (hy : y < height p q t)
    (hy0' : 0 < y') (hy' : y' < height p q t)
    (heq : interiorAt t x y hx0 hx hy0 hy = interiorAt t x y' hx0 hx hy0' hy') :
    y = y' := by
  have hpair : (⟨y - 1, by omega⟩ : Fin (height p q t - 1)) = ⟨y' - 1, by omega⟩ := by
    simpa [interiorAt] using heq
  have hv := congrArg Fin.val hpair
  change y - 1 = y' - 1 at hv
  omega

theorem horizontal_ne {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (t : Fin 12) (x y : ℕ) (hx : x < width p q t) (hy : y ≤ height p q t) :
    tileVertex hp hq t x y ≠ tileVertex hp hq t (x + 1) y := by
  have hw := width_ge_five hp hq t
  by_cases hy0 : y = 0
  · subst y
    simpa only [tileVertex_top] using (topWord p q t).at_succ_ne hp hq x
  by_cases hyh : y = height p q t
  · subst y
    simpa only [tileVertex_bottom] using (bottomWord p q t).at_succ_ne hp hq x
  have hyp : 0 < y := by omega
  have hylt : y < height p q t := by omega
  by_cases hx0 : x = 0
  · subst x
    rw [tileVertex_left hp hq t y hy,
      tileVertex_interior hp hq t 1 y (by omega) (by omega) hyp hylt]
    exact (leftWord p q t).at_ne_interior hp hq y t 1 y
      (by omega) (by omega) hyp hylt
  have hxp : 0 < x := by omega
  by_cases hxend : x + 1 = width p q t
  · rw [tileVertex_interior hp hq t x y hxp hx hyp hylt, hxend,
      tileVertex_right hp hq t y hy]
    exact ((rightWord p q t).at_ne_interior hp hq y t x y hxp hx hyp hylt).symm
  have hxnext : x + 1 < width p q t := by omega
  rw [tileVertex_interior hp hq t x y hxp hx hyp hylt,
    tileVertex_interior hp hq t (x + 1) y (by omega) hxnext hyp hylt]
  intro heq
  have he := interiorAt_x_injective t x (x + 1) y hxp hx (by omega) hxnext hyp hylt heq
  omega

theorem vertical_ne {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (t : Fin 12) (x y : ℕ) (hx : x ≤ width p q t) (hy : y < height p q t) :
    tileVertex hp hq t x y ≠ tileVertex hp hq t x (y + 1) := by
  have hh := height_ge_five hp hq t
  by_cases hx0 : x = 0
  · subst x
    rw [tileVertex_left hp hq t y (by omega), tileVertex_left hp hq t (y + 1) (by omega)]
    exact (leftWord p q t).at_succ_ne hp hq y
  by_cases hxw : x = width p q t
  · subst x
    rw [tileVertex_right hp hq t y (by omega), tileVertex_right hp hq t (y + 1) (by omega)]
    exact (rightWord p q t).at_succ_ne hp hq y
  have hxp : 0 < x := by omega
  have hxlt : x < width p q t := by omega
  by_cases hy0 : y = 0
  · subst y
    rw [tileVertex_top,
      tileVertex_interior hp hq t x 1 hxp hxlt (by omega) (by omega)]
    exact (topWord p q t).at_ne_interior hp hq x t x 1
      hxp hxlt (by omega) (by omega)
  have hyp : 0 < y := by omega
  by_cases hyend : y + 1 = height p q t
  · rw [tileVertex_interior hp hq t x y hxp hxlt hyp hy, hyend, tileVertex_bottom]
    exact ((bottomWord p q t).at_ne_interior hp hq x t x y hxp hxlt hyp hy).symm
  have hynext : y + 1 < height p q t := by omega
  rw [tileVertex_interior hp hq t x y hxp hxlt hyp hy,
    tileVertex_interior hp hq t x (y + 1) hxp hxlt (by omega) hynext]
  intro heq
  have he := interiorAt_y_injective t x y (y + 1) hxp hxlt hyp hy (by omega) hynext heq
  omega

def HorizontalStep {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (u v : Vertex p q) : Prop :=
  ∃ (t : Fin 12) (x y : ℕ), x < width p q t ∧ y ≤ height p q t ∧
    u = tileVertex hp hq t x y ∧ v = tileVertex hp hq t (x + 1) y

def VerticalStep {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (u v : Vertex p q) : Prop :=
  ∃ (t : Fin 12) (x y : ℕ), x ≤ width p q t ∧ y < height p q t ∧
    u = tileVertex hp hq t x y ∧ v = tileVertex hp hq t x (y + 1)

/-- The actual finite simple graph, obtained by identifying precisely
the named boundary positions and retaining each private grid interior. -/
def graph (p q : ℕ) (hp : 5 ≤ p) (hq : 5 ≤ q) : SimpleGraph (Vertex p q) :=
  SimpleGraph.fromRel (fun u v => HorizontalStep hp hq u v ∨ VerticalStep hp hq u v)

theorem horizontal_adj {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (t : Fin 12) (x y : ℕ) (hx : x < width p q t) (hy : y ≤ height p q t) :
    (graph p q hp hq).Adj (tileVertex hp hq t x y) (tileVertex hp hq t (x + 1) y) :=
  ⟨horizontal_ne hp hq t x y hx hy, Or.inl (Or.inl ⟨t, x, y, hx, hy, rfl, rfl⟩)⟩

theorem vertical_adj {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (t : Fin 12) (x y : ℕ) (hx : x ≤ width p q t) (hy : y < height p q t) :
    (graph p q hp hq).Adj (tileVertex hp hq t x y) (tileVertex hp hq t x (y + 1)) :=
  ⟨vertical_ne hp hq t x y hx hy, Or.inl (Or.inr ⟨t, x, y, hx, hy, rfl, rfl⟩)⟩

theorem HorizontalStep.adj {p q : ℕ} {hp : 5 ≤ p} {hq : 5 ≤ q} {u v : Vertex p q}
    (h : HorizontalStep hp hq u v) : (graph p q hp hq).Adj u v := by
  obtain ⟨t, x, y, hx, hy, rfl, rfl⟩ := h
  exact horizontal_adj hp hq t x y hx hy

theorem VerticalStep.adj {p q : ℕ} {hp : 5 ≤ p} {hq : 5 ≤ q} {u v : Vertex p q}
    (h : VerticalStep hp hq u v) : (graph p q hp hq).Adj u v := by
  obtain ⟨t, x, y, hx, hy, rfl, rfl⟩ := h
  exact vertical_adj hp hq t x y hx hy

@[simp] theorem cycleAt_mod {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (l : Fin 4) (x : ℕ) :
    cycleAt hp hq l (x % cycleLength p q l) = cycleAt hp hq l x := by
  simp [cycleAt]

theorem cycleAt_mod_succ {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (l : Fin 4) (x : ℕ) :
    cycleAt hp hq l (x % cycleLength p q l + 1) = cycleAt hp hq l (x + 1) := by
  simp [cycleAt, Nat.add_mod]

@[simp] theorem cycleAt_add_period {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (l : Fin 4) (x : ℕ) :
    cycleAt hp hq l (x + cycleLength p q l) = cycleAt hp hq l x := by
  simp [cycleAt]

theorem cycle_adj {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (l : Fin 4) (x : ℕ) (hx : x < cycleLength p q l) :
    (graph p q hp hq).Adj (cycleAt hp hq l x) (cycleAt hp hq l (x + 1)) := by
  fin_cases l
  · have h : x < height p q 0 := by simpa [height, leftWord, single,
        Word.length, Word.headLength, cycleLength] using hx
    have hadj := vertical_adj hp hq 0 0 x (by omega) h
    rw [tileVertex_left hp hq 0 x (by omega), tileVertex_left hp hq 0 (x + 1) (by omega)] at hadj
    simpa [leftWord, single, Word.at] using hadj
  · have h : x < height p q 1 := by simpa [height, leftWord, single,
        Word.length, Word.headLength, cycleLength] using hx
    have hadj := vertical_adj hp hq 1 0 x (by omega) h
    rw [tileVertex_left hp hq 1 x (by omega), tileVertex_left hp hq 1 (x + 1) (by omega)] at hadj
    simpa [leftWord, single, Word.at] using hadj
  · have h : x < width p q 0 := by simpa [width, topWord, single,
        Word.length, Word.headLength, cycleLength] using hx
    have hadj := horizontal_adj hp hq 0 x 0 h (by omega)
    simpa [topWord, single, Word.at] using hadj
  · have h : x < width p q 2 := by simpa [width, topWord, single,
        Word.length, Word.headLength, cycleLength] using hx
    have hadj := horizontal_adj hp hq 2 x 0 h (by omega)
    simpa [topWord, single, Word.at] using hadj

theorem cycle_adj_all {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    (l : Fin 4) (x : ℕ) :
    (graph p q hp hq).Adj (cycleAt hp hq l x) (cycleAt hp hq l (x + 1)) := by
  simpa only [cycleAt_mod, cycleAt_mod_succ] using
    cycle_adj hp hq l (x % cycleLength p q l) (Nat.mod_lt _ (cycleLength_pos hp hq l))

theorem Word.step_adj {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (w : Word) (x : ℕ) :
    (graph p q hp hq).Adj (w.at hp hq x) (w.at hp hq (x + 1)) := by
  cases hs : w.second with
  | none => simpa only [Word.at, hs] using cycle_adj_all hp hq w.first x
  | some k =>
    by_cases hx : x < w.headLength p q
    · by_cases hxs : x + 1 < w.headLength p q
      · simpa [Word.at, hs, hx, hxs] using cycle_adj_all hp hq w.first x
      · have heq : x + 1 = w.headLength p q := by omega
        have hb : cycleAt hp hq w.first (x + 1) = base p q := by
          rw [heq]; exact cycleAt_multiple hp hq w.first w.copies
        have hadj := cycle_adj_all hp hq w.first x
        rw [hb] at hadj
        simpa [Word.at, hs, hx, hxs, heq] using hadj
    · have hxs : ¬ x + 1 < w.headLength p q := by omega
      have hsub : x + 1 - w.headLength p q = (x - w.headLength p q) + 1 := by omega
      simpa [Word.at, hs, hx, hxs, hsub] using cycle_adj_all hp hq k (x - w.headLength p q)

instance (p q : ℕ) : TopologicalSpace (Vertex p q) := ⊥
instance (p q : ℕ) : DiscreteTopology (Vertex p q) := ⟨rfl⟩

theorem constant_of_edge_invariant {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q)
    {A : Type*} (g : Vertex p q → A)
    (hedge : ∀ u v, (graph p q hp hq).Adj u v → g u = g v) :
    ∀ u, g u = g (base p q) := by
  have hcycle : ∀ l n, g (cycleAt hp hq l n) = g (base p q) := by
    intro l n
    induction n with
    | zero => simp
    | succ n ih => exact (hedge _ _ (cycle_adj_all hp hq l n)).symm.trans ih
  have hword : ∀ w n, g (Word.at hp hq w n) = g (base p q) := by
    intro w n
    cases hs : w.second with
    | none => simpa only [Word.at, hs] using hcycle w.first n
    | some l => simp only [Word.at, hs]; split <;> exact hcycle _ _
  have htile : ∀ t x y, x ≤ width p q t → y ≤ height p q t →
      g (tileVertex hp hq t x y) = g (base p q) := by
    intro t x y hx hy
    induction x with
    | zero => rw [tileVertex_left hp hq t y hy]; exact hword _ _
    | succ x ih =>
      exact (hedge _ _ (horizontal_adj hp hq t x y (by omega) hy)).symm.trans (ih (by omega))
  rintro (_ | (⟨l,z⟩ | ⟨t,x,y⟩))
  · rfl
  · have heq : cycleAt hp hq l z.val.val = Sum.inr (Sum.inl ⟨l,z⟩) := by
      simp [cycleAt, Nat.mod_eq_of_lt z.val.isLt, cyclePoint, z.property]
    rw [← heq]
    exact hcycle _ _
  · have hx : x.val + 1 < width p q t := by have := x.isLt; omega
    have hy : y.val + 1 < height p q t := by have := y.isLt; omega
    have heq : tileVertex hp hq t (x.val+1) (y.val+1) =
        Sum.inr (Sum.inr ⟨t,x,y⟩) := by
      rw [tileVertex_interior hp hq t _ _ (by omega) hx (by omega) hy]
      simp only [interiorAt, Nat.add_sub_cancel]
    rw [← heq]
    exact htile t _ _ (by omega) (by omega)

end AbelianTargets.TwelveTiles

