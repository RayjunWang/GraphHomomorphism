import AbelianTargets.RectangularCells
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Global coordinate estimates from literal integer cells

On a coordinate line, any integer rectangle containing the midpoint of a
unit interval contains the entire interval. Consequently a uniform coordinate
estimate on covering cells gives the same estimate globally. This avoids any
loss proportional to the number of cells crossed by a line segment.
-/

namespace AbelianTargets

noncomputable section

open scoped NNReal

theorem lipschitz_real_of_integer_intervals {Z : Type*} [PseudoMetricSpace Z]
    (f : ℝ → Z) (K : ℝ≥0)
    (h : ∀ n : ℤ, ∀ x ∈ Set.Icc (n : ℝ) ((n : ℝ)+1),
      ∀ y ∈ Set.Icc (n : ℝ) ((n : ℝ)+1), dist (f x) (f y) ≤ K * |x-y|) :
    LipschitzWith K f := by
  have hint : ∀ n m : ℤ, n ≤ m → dist (f n) (f m) ≤ K * ((m : ℝ)-(n : ℝ)) := by
    intro n
    apply Int.leInduction
    · simp
    · intro m hnm ih
      have hm := h m m (by constructor <;> linarith)
        ((m : ℝ)+1) (by constructor <;> linarith)
      have he : |(m : ℝ)-((m : ℝ)+1)| = 1 := by norm_num
      rw [he, mul_one] at hm
      have ht := dist_triangle (f n) (f m) (f ((m : ℝ)+1))
      push_cast
      linarith
  have hordered : ∀ x y : ℝ, x ≤ y → dist (f x) (f y) ≤ K * (y-x) := by
    intro x y hxy
    let n := Int.floor x
    let m := Int.floor y
    have hnx : (n : ℝ) ≤ x := Int.floor_le x
    have hxn : x ≤ (n : ℝ)+1 := (Int.lt_floor_add_one x).le
    have hmy : (m : ℝ) ≤ y := Int.floor_le y
    have hym : y ≤ (m : ℝ)+1 := (Int.lt_floor_add_one y).le
    have hnm : n ≤ m := Int.floor_mono hxy
    by_cases he : n = m
    · have hh := h n x ⟨hnx,hxn⟩ y (by simpa [he] using And.intro hmy hym)
      rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at hh
      simpa only [neg_sub] using hh
    · have hnm' : n+1 ≤ m := by omega
      have hx := h n x ⟨hnx,hxn⟩ ((n : ℝ)+1) (by constructor <;> linarith)
      have hy := h m (m : ℝ) (by constructor <;> linarith) y ⟨hmy,hym⟩
      rw [abs_of_nonpos (sub_nonpos.mpr hxn), neg_sub] at hx
      rw [abs_of_nonpos (sub_nonpos.mpr hmy), neg_sub] at hy
      have hi := hint (n+1) m hnm'
      push_cast at hi
      calc
        _ ≤ dist (f x) (f ((n : ℝ)+1)) + dist (f ((n : ℝ)+1)) (f y) :=
          dist_triangle _ _ _
        _ ≤ dist (f x) (f ((n : ℝ)+1)) +
            (dist (f ((n : ℝ)+1)) (f m) + dist (f m) (f y)) :=
          add_le_add le_rfl (dist_triangle _ _ _)
        _ ≤ K * ((n : ℝ)+1-x) + (K * ((m : ℝ)-((n : ℝ)+1)) + K*(y-(m : ℝ))) :=
          add_le_add hx (add_le_add hi hy)
        _ = K * (y-x) := by ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
    exact hordered x y hxy
  · rw [dist_comm (f x) (f y), abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hordered y x hyx

namespace RectangularCell

/-- A rectangle with integer endpoints that contains a unit midpoint contains
the whole coordinate unit interval. -/
theorem coordinate_unit_interval {d : ℕ} (R : RectangularCell d)
    (z : RealCoordinates d) (i : Fin d) (n : ℤ)
    (hz : Function.update z i ((n : ℝ)+1/2) ∈ R.closedBox) :
    ∀ t ∈ Set.Icc (n : ℝ) ((n : ℝ)+1), Function.update z i t ∈ R.closedBox := by
  intro t ht j
  by_cases hji : j = i
  · subst j
    have hi := hz i
    simp only [Function.update_self] at hi ⊢
    have hlo : R.lower i ≤ n := by
      by_contra hbad
      have hh : n+1 ≤ R.lower i := by omega
      have hh' : (n : ℝ)+1 ≤ (R.lower i : ℝ) := by exact_mod_cast hh
      linarith
    have hhi : n+1 ≤ R.upper i := by
      by_contra hbad
      have hh : R.upper i ≤ n := by omega
      have hh' : (R.upper i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hh
      linarith
    constructor
    · exact (show (R.lower i : ℝ) ≤ (n : ℝ) by exact_mod_cast hlo).trans ht.1
    · exact ht.2.trans (show (n : ℝ)+1 ≤ (R.upper i : ℝ) by exact_mod_cast hhi)
  · simpa only [Function.update_of_ne hji] using hz j

end RectangularCell

theorem lipschitz_coordinate_of_cell_cover {d : ℕ} {ι Z : Type*} [PseudoMetricSpace Z]
    (R : ι → RectangularCell d) (cover : ∀ z, ∃ c, z ∈ (R c).closedBox)
    (f : RealCoordinates d → Z) (i : Fin d) (K : ℝ≥0)
    (hcell : ∀ c z x y, Function.update z i x ∈ (R c).closedBox →
      Function.update z i y ∈ (R c).closedBox →
      dist (f (Function.update z i x)) (f (Function.update z i y)) ≤ K*|x-y|)
    (z : RealCoordinates d) : LipschitzWith K (fun t => f (Function.update z i t)) := by
  apply lipschitz_real_of_integer_intervals
  intro n x hx y hy
  obtain ⟨c,hc⟩ := cover (Function.update z i ((n : ℝ)+1/2))
  exact hcell c z x y ((R c).coordinate_unit_interval z i n hc x hx)
    ((R c).coordinate_unit_interval z i n hc y hy)

/-- Continuous cell maps agreeing as a global function glue over any locally
finite closed rectangular cover. -/
theorem continuous_of_rectangular_cell_cover {d : ℕ} {ι Z : Type*} [TopologicalSpace Z]
    (R : ι → RectangularCell d) (hlocal : LocallyFinite (fun c => (R c).closedBox))
    (cover : ∀ z, ∃ c, z ∈ (R c).closedBox) (f : RealCoordinates d → Z)
    (hc : ∀ c, ContinuousOn f (R c).closedBox) : Continuous f := by
  apply hlocal.continuous _ (fun c => (R c).isClosed_closedBox) hc
  ext z
  simpa only [Set.mem_iUnion, Set.mem_univ, iff_true] using cover z

end

end AbelianTargets
