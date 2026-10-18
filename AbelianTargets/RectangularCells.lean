import AbelianTargets.ParityFields
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Integer rectangular cells and their point faces

These are literal closed rectangles, including degenerate coordinates. The
relative interior keeps a degenerate coordinate fixed. `faceAt` is the smallest
coordinate face containing a given point, rather than a chosen abstract cell.
-/

namespace AbelianTargets

noncomputable section

structure RectangularCell (d : ℕ) where
  lower : Fin d → ℤ
  upper : Fin d → ℤ
  ordered : ∀ i, lower i ≤ upper i
  deriving DecidableEq

namespace RectangularCell

variable {d : ℕ}

def closedBox (R : RectangularCell d) : Set (RealCoordinates d) :=
  {x | ∀ i, (R.lower i : ℝ) ≤ x i ∧ x i ≤ (R.upper i : ℝ)}

def relativeInterior (R : RectangularCell d) : Set (RealCoordinates d) :=
  {x | ∀ i, if R.lower i = R.upper i then x i = (R.lower i : ℝ)
    else (R.lower i : ℝ) < x i ∧ x i < (R.upper i : ℝ)}

def varyingAxes (R : RectangularCell d) : Finset (Fin d) :=
  Finset.univ.filter (fun i => R.lower i < R.upper i)

def rank (R : RectangularCell d) : ℕ := R.varyingAxes.card

def boundary (R : RectangularCell d) : Set (RealCoordinates d) :=
  R.closedBox \ R.relativeInterior

theorem relativeInterior_subset (R : RectangularCell d) :
    R.relativeInterior ⊆ R.closedBox := by
  intro x hx i
  have hi := hx i
  by_cases h : R.lower i = R.upper i
  · simp only [h, if_true] at hi
    simpa [hi, h]
  · simp only [h, if_false] at hi
    exact ⟨hi.1.le, hi.2.le⟩

theorem isClosed_closedBox (R : RectangularCell d) : IsClosed R.closedBox := by
  change IsClosed {x : RealCoordinates d | ∀ i,
    (R.lower i : ℝ) ≤ x i ∧ x i ≤ (R.upper i : ℝ)}
  have he : {x : RealCoordinates d | ∀ i,
      (R.lower i : ℝ) ≤ x i ∧ x i ≤ (R.upper i : ℝ)} =
      ⋂ i, {x : RealCoordinates d | (R.lower i : ℝ) ≤ x i ∧ x i ≤ (R.upper i : ℝ)} := by
    ext x; simp
  rw [he]
  exact isClosed_iInter fun i =>
    (isClosed_le continuous_const (continuous_apply i : Continuous (fun x : RealCoordinates d => x i))).inter
      (isClosed_le (continuous_apply i : Continuous (fun x : RealCoordinates d => x i)) continuous_const)

theorem closedBox_nonempty (R : RectangularCell d) : R.closedBox.Nonempty := by
  refine ⟨fun i => (R.lower i : ℝ), fun i => ⟨le_rfl, ?_⟩⟩
  change (R.lower i : ℝ) ≤ (R.upper i : ℝ)
  exact_mod_cast R.ordered i

theorem relativeInterior_nonempty (R : RectangularCell d) :
    R.relativeInterior.Nonempty := by
  refine ⟨fun i => ((R.lower i : ℝ) + (R.upper i : ℝ)) / 2, ?_⟩
  intro i
  by_cases h : R.lower i = R.upper i
  · simp [h]
  · simp only [h, if_false]
    have hi : (R.lower i : ℝ) < (R.upper i : ℝ) := by
      exact_mod_cast lt_of_le_of_ne (R.ordered i) h
    constructor <;> linarith

def faceAt (R : RectangularCell d) (x : RealCoordinates d) : RectangularCell d where
  lower i := if x i = (R.upper i : ℝ) then R.upper i else R.lower i
  upper i := if x i = (R.lower i : ℝ) then R.lower i else R.upper i
  ordered i := by
    split_ifs with hu hl hl
    · have h : R.lower i = R.upper i := by
        exact_mod_cast (hl.symm.trans hu)
      omega
    · exact le_rfl
    · exact le_rfl
    · exact R.ordered i

theorem faceAt_subset (R : RectangularCell d) (x : RealCoordinates d) :
    (R.faceAt x).closedBox ⊆ R.closedBox := by
  intro y hy i
  have hi := hy i
  have h := R.ordered i
  have h' : (R.lower i : ℝ) ≤ (R.upper i : ℝ) := by exact_mod_cast h
  simp only [faceAt] at hi
  split_ifs at hi <;> constructor <;> linarith

theorem mem_relativeInterior_faceAt (R : RectangularCell d)
    {x : RealCoordinates d} (hx : x ∈ R.closedBox) :
    x ∈ (R.faceAt x).relativeInterior := by
  intro i
  have hi := hx i
  by_cases hu : x i = (R.upper i : ℝ)
  · by_cases hl : x i = (R.lower i : ℝ)
    · have he : R.lower i = R.upper i := by exact_mod_cast hl.symm.trans hu
      simp [relativeInterior, faceAt, hu, hl, he]
    · simp [relativeInterior, faceAt, hu, hl]
  · by_cases hl : x i = (R.lower i : ℝ)
    · simp [faceAt, hu, hl, eq_comm]
    · have he : R.lower i ≠ R.upper i := by
        intro he
        have hi' : (R.lower i : ℝ) = (R.upper i : ℝ) := by rw [he]
        exact hl (le_antisymm (hi.2.trans hi'.symm.le) hi.1)
      simp only [relativeInterior, faceAt, hu, hl, if_false, he]
      exact ⟨lt_of_le_of_ne hi.1 (Ne.symm hl), lt_of_le_of_ne hi.2 hu⟩

/-- Coordinatewise intersections stay literal integer rectangles whenever
the two closed boxes meet. -/
def intersect (R S : RectangularCell d) (h : (R.closedBox ∩ S.closedBox).Nonempty) :
    RectangularCell d where
  lower i := max (R.lower i) (S.lower i)
  upper i := min (R.upper i) (S.upper i)
  ordered i := by
    obtain ⟨x, hxR, hxS⟩ := h
    have hRR := R.ordered i
    have hSS := S.ordered i
    have hRS : R.lower i ≤ S.upper i := by
      exact_mod_cast (hxR i).1.trans (hxS i).2
    have hSR : S.lower i ≤ R.upper i := by
      exact_mod_cast (hxS i).1.trans (hxR i).2
    exact max_le (le_min hRR hRS) (le_min hSR hSS)

theorem closedBox_intersect (R S : RectangularCell d)
    (h : (R.closedBox ∩ S.closedBox).Nonempty) :
    (R.intersect S h).closedBox = R.closedBox ∩ S.closedBox := by
  ext x
  simp only [closedBox, intersect, Set.mem_setOf_eq, Set.mem_inter_iff,
    Int.cast_max, Int.cast_min, max_le_iff, le_min_iff]
  constructor
  · intro hx
    exact ⟨fun i => ⟨(hx i).1.1, (hx i).2.1⟩,
      fun i => ⟨(hx i).1.2, (hx i).2.2⟩⟩
  · rintro ⟨hxR, hxS⟩ i
    exact ⟨⟨(hxR i).1, (hxS i).1⟩, ⟨(hxR i).2, (hxS i).2⟩⟩

def translate (R : RectangularCell d) (a : Fin d → ℤ) : RectangularCell d where
  lower i := R.lower i + a i
  upper i := R.upper i + a i
  ordered i := by have h := R.ordered i; omega

theorem mem_closedBox_translate (R : RectangularCell d) (a : Fin d → ℤ)
    (x : RealCoordinates d) :
    (fun i => x i + (a i : ℝ)) ∈ (R.translate a).closedBox ↔ x ∈ R.closedBox := by
  simp [closedBox, translate]

theorem rank_translate (R : RectangularCell d) (a : Fin d → ℤ) :
    (R.translate a).rank = R.rank := by
  simp [rank, varyingAxes, translate]

end RectangularCell

end

end AbelianTargets
