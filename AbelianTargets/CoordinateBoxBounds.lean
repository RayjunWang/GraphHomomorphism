import AbelianTargets.RectangularCells
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Coordinate bounds on a rectangular cell imply a full metric bound -/

namespace AbelianTargets

open scoped BigOperators NNReal

noncomputable section

def coordinateHybrid {d : ℕ} (x y : RealCoordinates d) (s : Finset (Fin d)) :
    RealCoordinates d := fun i => if i ∈ s then y i else x i

theorem coordinateHybrid_mem {d : ℕ} (R : RectangularCell d)
    {x y : RealCoordinates d} (hx : x ∈ R.closedBox) (hy : y ∈ R.closedBox)
    (s : Finset (Fin d)) : coordinateHybrid x y s ∈ R.closedBox := by
  intro i
  simp only [coordinateHybrid]
  split_ifs
  · exact hy i
  · exact hx i

theorem coordinate_box_dist_le {d : ℕ} {Z : Type*} [PseudoMetricSpace Z]
    (R : RectangularCell d) (f : RealCoordinates d → Z) (K : Fin d → ℝ≥0)
    (hcoord : ∀ i x y, x ∈ R.closedBox → y ∈ R.closedBox →
      (∀ j, j ≠ i → x j=y j) → dist (f x) (f y) ≤ K i * |x i-y i|)
    {x y : RealCoordinates d} (hx : x ∈ R.closedBox) (hy : y ∈ R.closedBox) :
    dist (f x) (f y) ≤ ∑ i, (K i : ℝ)*|x i-y i| := by
  classical
  have h : ∀ s : Finset (Fin d), dist (f x) (f (coordinateHybrid x y s)) ≤
      ∑ i ∈ s, (K i : ℝ)*|x i-y i| := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have he : coordinateHybrid x y ∅ = x := by funext i; simp [coordinateHybrid]
      simp [he]
    | @insert i s hi ih =>
      have hp := coordinateHybrid_mem R hx hy s
      have hq := coordinateHybrid_mem R hx hy (insert i s)
      have hh := hcoord i (coordinateHybrid x y s) (coordinateHybrid x y (insert i s)) hp hq
        (fun j hj => by simp [coordinateHybrid,Finset.mem_insert,hj])
      simp only [coordinateHybrid,hi,if_false,Finset.mem_insert_self,if_true] at hh
      calc
        _ ≤ dist (f x) (f (coordinateHybrid x y s)) +
            dist (f (coordinateHybrid x y s)) (f (coordinateHybrid x y (insert i s))) :=
          dist_triangle _ _ _
        _ ≤ (∑ j ∈ s, (K j : ℝ)*|x j-y j|) + (K i : ℝ)*|x i-y i| := add_le_add ih hh
        _ = _ := by rw [Finset.sum_insert hi]; ring
  have hall := h Finset.univ
  have he : coordinateHybrid x y Finset.univ = y := by
    funext i; simp [coordinateHybrid]
  simpa only [he] using hall

theorem lipschitzOn_rectangularCell_of_coordinates {d : ℕ} {Z : Type*} [PseudoMetricSpace Z]
    (R : RectangularCell d) (f : RealCoordinates d → Z) (K : Fin d → ℝ≥0)
    (hcoord : ∀ i x y, x ∈ R.closedBox → y ∈ R.closedBox →
      (∀ j, j ≠ i → x j=y j) → dist (f x) (f y) ≤ K i * |x i-y i|) :
    LipschitzOnWith (∑ i, K i) f R.closedBox := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  calc
    _ ≤ ∑ i, (K i : ℝ)*|x i-y i| := coordinate_box_dist_le R f K hcoord hx hy
    _ ≤ ∑ i, (K i : ℝ)*dist x y := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (K i).2
    _ = (∑ i, K i : ℝ≥0)*dist x y := by rw [← Finset.sum_mul]; simp

end

end AbelianTargets
