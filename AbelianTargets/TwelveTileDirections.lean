import AbelianTargets.TwelveTileUniform
import AbelianTargets.PrimitiveDirections
import AbelianTargets.TorusRigidity

namespace AbelianTargets.TwelveTiles

open scoped BigOperators

variable {p q m : ℕ} {hp : 5 ≤ p} {hq : 5 ≤ q}
variable {V : Type*} {H : SimpleGraph V}

def cycleDirections (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (l : Fin 4) : Fin (cycleLength p q l) → SignedDirection m :=
  fun x => laws.direction (f.map_adj (cycle_adj_all hp hq l x.val))

theorem cycleTotal_eq_sum (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (l : Fin 4) : cycleTotal laws f l = ∑ x, (cycleDirections laws f l x).vector :=
  (Fin.sum_univ_eq_sum_range (cycleVector laws f l) _).symm

theorem cycleVector_mod (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (l : Fin 4) (x : ℕ) :
    cycleVector laws f l (x % cycleLength p q l) = cycleVector laws f l x := by
  unfold cycleVector
  apply edgeVector_congr
  · exact cycleAt_mod hp hq l x
  · exact cycleAt_mod_succ hp hq l x

theorem cycleVector_constant_of_total (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (l : Fin 4) (u : SignedDirection m)
    (ht : cycleTotal laws f l = cycleLength p q l • u.vector) :
    ∀ x, cycleVector laws f l x = u.vector := by
  rw [cycleTotal_eq_sum] at ht
  have hs := signedDirection_sum_saturation (cycleDirections laws f l) u ht
  intro x
  rw [← cycleVector_mod laws f l x]
  exact congrArg SignedDirection.vector (hs ⟨x % cycleLength p q l, Nat.mod_lt x (cycleLength_pos hp hq l)⟩)

structure UniformDirections (laws : DirectionLaws H m) (f : graph p q hp hq →g H) where
  horizontal : SignedDirection m
  vertical : SignedDirection m
  horizontal_eq : ∀ t x y, x < width p q t → y ≤ height p q t →
    horizontalVector laws f t x y = horizontal.vector
  vertical_eq : ∀ t x y, x ≤ width p q t → y < height p q t →
    verticalVector laws f t x y = vertical.vector

/-- The constant-direction part of Lemma 7.4 for one literal twelve-tile
factor, obtained from the long-tile equations, coprimality and saturation. -/
theorem exists_uniformDirections (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (hpodd : Odd p) (hcop : p.Coprime q) : Nonempty (UniformDirections laws f) := by
  have hh := cycle_totals_horizontal_relation laws f
  rw [cycleTotal_eq_sum, cycleTotal_eq_sum] at hh
  change q • (∑ x : Fin p, (cycleDirections laws f 2 x).vector) =
    p • (∑ x : Fin q, (cycleDirections laws f 3 x).vector) at hh
  obtain ⟨u, huc, hud⟩ := signedDirection_coprime_periods hpodd hcop
    (cycleDirections laws f 2) (cycleDirections laws f 3) hh
  have hvv := cycle_totals_vertical_relation laws f
  rw [cycleTotal_eq_sum, cycleTotal_eq_sum] at hvv
  change q • (∑ x : Fin p, (cycleDirections laws f 0 x).vector) =
    p • (∑ x : Fin q, (cycleDirections laws f 1 x).vector) at hvv
  obtain ⟨v, hva, hvb⟩ := signedDirection_coprime_periods hpodd hcop
    (cycleDirections laws f 0) (cycleDirections laws f 1) hvv
  have hu : ∀ l : Fin 4, 2 ≤ l.val → ∀ x, cycleVector laws f l x = u.vector := by
    intro l hl
    fin_cases l
    · norm_num at hl
    · norm_num at hl
    · apply cycleVector_constant_of_total laws f 2 u
      rw [cycleTotal_eq_sum]; exact huc
    · apply cycleVector_constant_of_total laws f 3 u
      rw [cycleTotal_eq_sum]; exact hud
  have hv : ∀ l : Fin 4, l.val < 2 → ∀ x, cycleVector laws f l x = v.vector := by
    intro l hl
    fin_cases l
    · apply cycleVector_constant_of_total laws f 0 v
      rw [cycleTotal_eq_sum]; exact hva
    · apply cycleVector_constant_of_total laws f 1 v
      rw [cycleTotal_eq_sum]; exact hvb
    · norm_num at hl
    · norm_num at hl
  exact ⟨⟨u,v,horizontalVector_constant_of_cycles laws f u v hu hv,
    verticalVector_constant_of_cycles laws f u v hu hv⟩⟩

theorem UniformDirections.horizontal_step_eq (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (D : UniformDirections laws f) {u v : Vertex p q} (h : HorizontalStep hp hq u v) :
    edgeVector laws f h.adj = D.horizontal.vector := by
  obtain ⟨t,x,y,hx,hy,rfl,rfl⟩ := h
  have he := D.horizontal_eq t x y hx hy
  simpa only [horizontalVector, dif_pos (show x < width p q t ∧ y ≤ height p q t from ⟨hx,hy⟩)] using he

theorem UniformDirections.vertical_step_eq (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (D : UniformDirections laws f) {u v : Vertex p q} (h : VerticalStep hp hq u v) :
    edgeVector laws f h.adj = D.vertical.vector := by
  obtain ⟨t,x,y,hx,hy,rfl,rfl⟩ := h
  have he := D.vertical_eq t x y hx hy
  simpa only [verticalVector, dif_pos (show x ≤ width p q t ∧ y < height p q t from ⟨hx,hy⟩)] using he

theorem cycle_horizontalStep (hp : 5 ≤ p) (hq : 5 ≤ q)
    (l : Fin 4) (hl : 2 ≤ l.val) (n : ℕ) (hn : n < cycleLength p q l) :
    HorizontalStep hp hq (cycleAt hp hq l n) (cycleAt hp hq l (n+1)) := by
  fin_cases l
  · norm_num at hl
  · norm_num at hl
  · refine ⟨0,n,0,by simpa [width,topWord,single,Word.length,Word.headLength] using hn,
      Nat.zero_le _,?_,?_⟩ <;> simp [topWord,single,Word.at]
  · refine ⟨2,n,0,by simpa [width,topWord,single,Word.length,Word.headLength] using hn,
      Nat.zero_le _,?_,?_⟩ <;> simp [topWord,single,Word.at]

theorem cycle_verticalStep (hp : 5 ≤ p) (hq : 5 ≤ q)
    (l : Fin 4) (hl : l.val < 2) (n : ℕ) (hn : n < cycleLength p q l) :
    VerticalStep hp hq (cycleAt hp hq l n) (cycleAt hp hq l (n+1)) := by
  fin_cases l
  · refine ⟨0,0,n,Nat.zero_le _,by simpa [height,leftWord,single,Word.length,Word.headLength] using hn,?_,?_⟩
    · rw [tileVertex_left hp hq 0 n (by simpa [height,leftWord,single,Word.length,Word.headLength] using hn.le)]
      rfl
    · rw [tileVertex_left hp hq 0 (n+1) (by simpa [height,leftWord,single,Word.length,Word.headLength] using Nat.succ_le_of_lt hn)]
      rfl
  · refine ⟨1,0,n,Nat.zero_le _,by simpa [height,leftWord,single,Word.length,Word.headLength] using hn,?_,?_⟩
    · rw [tileVertex_left hp hq 1 n (by simpa [height,leftWord,single,Word.length,Word.headLength] using hn.le)]
      rfl
    · rw [tileVertex_left hp hq 1 (n+1) (by simpa [height,leftWord,single,Word.length,Word.headLength] using Nat.succ_le_of_lt hn)]
      rfl
  · norm_num at hl
  · norm_num at hl

theorem UniformDirections.cycleVector_horizontal (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (D : UniformDirections laws f) (l : Fin 4) (hl : 2 ≤ l.val) (n : ℕ) :
    cycleVector laws f l n = D.horizontal.vector := by
  rw [← cycleVector_mod laws f l n]
  exact D.horizontal_step_eq laws f (cycle_horizontalStep hp hq l hl _ (Nat.mod_lt n (cycleLength_pos hp hq l)))

theorem UniformDirections.cycleVector_vertical (laws : DirectionLaws H m) (f : graph p q hp hq →g H)
    (D : UniformDirections laws f) (l : Fin 4) (hl : l.val < 2) (n : ℕ) :
    cycleVector laws f l n = D.vertical.vector := by
  rw [← cycleVector_mod laws f l n]
  exact D.vertical_step_eq laws f (cycle_verticalStep hp hq l hl _ (Nat.mod_lt n (cycleLength_pos hp hq l)))

end AbelianTargets.TwelveTiles
