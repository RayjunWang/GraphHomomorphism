import AbelianTargets.TwelveTileDirections

namespace AbelianTargets.TwelveTiles

variable {p q m : ℕ} {hp : 5 ≤ p} {hq : 5 ≤ q}
variable {V : Type*} {H : SimpleGraph V}

@[simp] theorem width_one (p q : ℕ) : width p q 1 = p := by
  norm_num [width, topWord, single, Word.length, Word.headLength, cycleLength]

@[simp] theorem height_one (p q : ℕ) : height p q 1 = q := by
  norm_num [height, leftWord, single, Word.length, Word.headLength, cycleLength]

theorem tile_one_horizontal_wrap (hp : 5 ≤ p) (hq : 5 ≤ q)
    (y : ℕ) (hy : y ≤ q) : tileVertex hp hq 1 p y = tileVertex hp hq 1 0 y := by
  rw [show tileVertex hp hq 1 p y = tileVertex hp hq 1 (width p q 1) y from
    congrArg (fun z => tileVertex hp hq 1 z y) (width_one p q).symm]
  rw [tileVertex_right hp hq 1 y (by simpa using hy),
    tileVertex_left hp hq 1 y (by simpa using hy)]
  rfl

theorem tile_one_vertical_wrap (hp : 5 ≤ p) (hq : 5 ≤ q) (x : ℕ) :
    tileVertex hp hq 1 x q = tileVertex hp hq 1 x 0 := by
  rw [show tileVertex hp hq 1 x q = tileVertex hp hq 1 x (height p q 1) from
    congrArg (fun z => tileVertex hp hq 1 x z) (height_one p q).symm]
  rw [tileVertex_bottom, tileVertex_top]
  rfl

theorem tile_one_horizontal_mod (hp : 5 ≤ p) (hq : 5 ≤ q)
    (x y : ℕ) (hx : x < p) (hy : y ≤ q) :
    tileVertex hp hq 1 ((x+1)%p) y = tileVertex hp hq 1 (x+1) y := by
  by_cases hxp : x + 1 < p
  · rw [Nat.mod_eq_of_lt hxp]
  · have heq : x + 1 = p := by omega
    rw [heq, Nat.mod_self]
    exact (tile_one_horizontal_wrap hp hq y hy).symm

theorem tile_one_vertical_mod (hp : 5 ≤ p) (hq : 5 ≤ q)
    (x y : ℕ) (hy : y < q) :
    tileVertex hp hq 1 x ((y+1)%q) = tileVertex hp hq 1 x (y+1) := by
  by_cases hyp : y + 1 < q
  · rw [Nat.mod_eq_of_lt hyp]
  · have heq : y + 1 = q := by omega
    rw [heq, Nat.mod_self]
    exact (tile_one_vertical_wrap hp hq x).symm

def torusVertex (hp : 5 ≤ p) (hq : 5 ≤ q) (z : ZMod p × ZMod q) : Vertex p q :=
  tileVertex hp hq 1 z.1.val z.2.val

theorem torusVertex_horizontal_step (hp : 5 ≤ p) (hq : 5 ≤ q)
    (i : ZMod p) (j : ZMod q) :
    HorizontalStep hp hq (torusVertex hp hq (i,j)) (torusVertex hp hq (i+1,j)) := by
  letI : NeZero p := ⟨by omega⟩
  letI : NeZero q := ⟨by omega⟩
  refine ⟨1,i.val,j.val,by simpa using i.val_lt,by simpa using j.val_lt.le,rfl,?_⟩
  unfold torusVertex
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (show 1 < p by omega)]
  exact tile_one_horizontal_mod hp hq i.val j.val i.val_lt j.val_lt.le

theorem torusVertex_vertical_step (hp : 5 ≤ p) (hq : 5 ≤ q)
    (i : ZMod p) (j : ZMod q) :
    VerticalStep hp hq (torusVertex hp hq (i,j)) (torusVertex hp hq (i,j+1)) := by
  letI : NeZero p := ⟨by omega⟩
  letI : NeZero q := ⟨by omega⟩
  refine ⟨1,i.val,j.val,by simpa using i.val_lt.le,by simpa using j.val_lt,rfl,?_⟩
  unfold torusVertex
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (show 1 < q by omega)]
  exact tile_one_vertical_mod hp hq i.val j.val j.val_lt

theorem UniformDirections.distinct_axes (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (D : UniformDirections laws f) (hcop : p.Coprime q) : D.horizontal.axis ≠ D.vertical.axis := by
  apply coprime_torus_directions_distinct_axes (by omega) (by omega) hcop laws
    (fun z => f (torusVertex hp hq z)) D.horizontal D.vertical
    (fun i j => f.map_adj (torusVertex_horizontal_step hp hq i j).adj)
    (fun i j => f.map_adj (torusVertex_vertical_step hp hq i j).adj)
  · intro i j
    exact D.horizontal_step_eq laws f (torusVertex_horizontal_step hp hq i j)
  · intro i j
    exact D.vertical_step_eq laws f (torusVertex_vertical_step hp hq i j)

/-- Full one-factor direction rigidity, including the two distinct axes. -/
theorem factor_rigidity (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (hpodd : Odd p) (hcop : p.Coprime q) :
    ∃ D : UniformDirections laws f, D.horizontal.axis ≠ D.vertical.axis := by
  obtain ⟨D⟩ := exists_uniformDirections laws f hpodd hcop
  exact ⟨D,D.distinct_axes laws f hcop⟩

end AbelianTargets.TwelveTiles
