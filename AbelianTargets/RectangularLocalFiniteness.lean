import AbelianTargets.RectangularCells
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval

/-!
# Local finiteness of bounded integer rectangles

Integer endpoints and a uniform coordinate diameter bound alone give a
locally finite family of distinct rectangles. Thus the same conclusion
applies both to retained full tiles and to their lower-dimensional strata.
-/

namespace AbelianTargets

noncomputable section

namespace RectangularCell

variable {d : ℕ}

theorem endpoint_pair_injective :
    Function.Injective (fun R : RectangularCell d => (R.lower,R.upper)) := by
  intro R S h
  cases R
  cases S
  cases h
  rfl

theorem finite_bounded_endpoints (a b : Fin d → ℤ) :
    {R : RectangularCell d | ∀ i,
      a i ≤ R.lower i ∧ R.lower i ≤ b i ∧ a i ≤ R.upper i ∧ R.upper i ≤ b i}.Finite := by
  have hfin : {u : Fin d → ℤ | ∀ i, u i ∈ Set.Icc (a i) (b i)}.Finite :=
    Set.Finite.pi' (fun i => Set.finite_Icc (a i) (b i))
  apply Set.Finite.of_injOn (f := fun R : RectangularCell d => (R.lower,R.upper))
    (t := {u : Fin d → ℤ | ∀ i, u i ∈ Set.Icc (a i) (b i)} ×ˢ
      {u : Fin d → ℤ | ∀ i, u i ∈ Set.Icc (a i) (b i)}) _ endpoint_pair_injective.injOn
    (hfin.prod hfin)
  intro R hR
  exact ⟨fun i => ⟨(hR i).1, (hR i).2.1⟩,
    fun i => ⟨(hR i).2.2.1, (hR i).2.2.2⟩⟩

def HasBoundedSides (K : Fin d → ℕ) (R : RectangularCell d) : Prop :=
  ∀ i, R.upper i-R.lower i ≤ (K i : ℤ)

theorem finite_meeting_ball (K : Fin d → ℕ) (x : RealCoordinates d) :
    {R : RectangularCell d | HasBoundedSides K R ∧
      (R.closedBox ∩ Metric.ball x 1).Nonempty}.Finite := by
  let a : Fin d → ℤ := fun i => Int.ceil (x i-1-(K i : ℝ))
  let b : Fin d → ℤ := fun i => Int.floor (x i+1+(K i : ℝ))
  apply (finite_bounded_endpoints a b).subset
  rintro R ⟨hR,y,hy,hyx⟩ i
  have hi : |y i-x i| ≤ 1 := by
    have hh : dist (y i) (x i) ≤ dist y x := dist_le_pi_dist y x i
    have hball : dist y x < 1 := hyx
    rw [Real.dist_eq] at hh
    exact hh.trans hball.le
  have hlohi := hy i
  have hord : (R.lower i : ℝ) ≤ (R.upper i : ℝ) := by exact_mod_cast R.ordered i
  have hdiam : (R.upper i : ℝ)-(R.lower i : ℝ) ≤ (K i : ℝ) := by
    exact_mod_cast hR i
  have hi' := abs_le.mp hi
  have hlower : x i-1-(K i : ℝ) ≤ (R.lower i : ℝ) := by linarith
  have hupper : (R.upper i : ℝ) ≤ x i+1+(K i : ℝ) := by linarith
  have ha : a i ≤ R.lower i := Int.ceil_le.mpr hlower
  have hb : R.upper i ≤ b i := Int.le_floor.mpr hupper
  exact ⟨ha,(R.ordered i).trans hb,ha.trans (R.ordered i),hb⟩

theorem locallyFinite_boundedSides (K : Fin d → ℕ) :
    LocallyFinite (fun R : {R : RectangularCell d // HasBoundedSides K R} => R.1.closedBox) := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), ?_⟩
  have hf := (finite_meeting_ball K x).preimage
    (f := fun R : {R : RectangularCell d // HasBoundedSides K R} => R.1)
    Subtype.val_injective.injOn
  apply hf.subset
  intro R hR
  exact ⟨R.2,hR⟩

theorem locallyFinite_of_boundedSides {ι : Type*} (R : ι → RectangularCell d)
    (hR : Function.Injective R) (K : Fin d → ℕ) (hK : ∀ c, HasBoundedSides K (R c)) :
    LocallyFinite (fun c => (R c).closedBox) := by
  let r : ι → {R : RectangularCell d // HasBoundedSides K R} := fun c => ⟨R c,hK c⟩
  have hr : Function.Injective r := by
    intro c c' h
    apply hR
    exact congrArg Subtype.val h
  exact (locallyFinite_boundedSides K).comp_injective hr

theorem finite_incident_of_boundedSides {ι : Type*} (R : ι → RectangularCell d)
    (hR : Function.Injective R) (K : Fin d → ℕ) (hK : ∀ c, HasBoundedSides K (R c))
    (x : RealCoordinates d) : {c | x ∈ (R c).closedBox}.Finite :=
  (locallyFinite_of_boundedSides R hR K hK).point_finite x

end RectangularCell

end

end AbelianTargets
