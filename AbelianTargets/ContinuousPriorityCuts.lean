import AbelianTargets.PriorityCuts
import Mathlib.Topology.Instances.Int
import Mathlib.Order.Filter.Finite

/-!
# Continuity of finite priority-cut processing

The marker index type may be infinite. For each fixed index, the finite
neighbor list, priority, and integer center vary continuously with the
parameter. The neighbor-list space is given a discrete topology. Every
finite stage of the actual `priorityCutIteration` is then continuous.
This is a local continuity result; constructing an orbit-coordinate
parameterization of marker indices and the final CW atlas is separate.
-/

namespace AbelianTargets

noncomputable section
open Filter Topology

private theorem locally_equal_of_continuous {Y A : Type*}
    [TopologicalSpace Y] [TopologicalSpace A] [DiscreteTopology A]
    {f : Y → A} (hf : Continuous f) (y : Y) :
    ∀ᶠ z in 𝓝 y, f z = f y := by
  exact hf.continuousAt.eventually ((isOpen_discrete ({f y} : Set A)).mem_nhds rfl)

theorem earlierPriorityCuts_congr {I : Type*} {P : ℕ}
    (N N' : PriorityNeighborhood I P) (old old' : I → ℤ × ℤ)
    (n : ℕ) (x : I) (hnear : N.nearby x = N'.nearby x)
    (hpriority : ∀ i ∈ N'.nearby x, N.priority i = N'.priority i)
    (hold : ∀ i ∈ N'.nearby x, old i = old' i) :
    earlierPriorityCuts N old n x = earlierPriorityCuts N' old' n x := by
  classical
  unfold earlierPriorityCuts
  have hfilter : (N.nearby x).filter (fun i => (N.priority i).val < n) =
      (N'.nearby x).filter (fun i => (N'.priority i).val < n) := by
    rw [hnear]
    apply Finset.filter_congr
    intro i hi
    rw [hpriority i hi]
  apply Finset.biUnion_congr hfilter
  intro i hi
  have hi' : i ∈ N'.nearby x := by
    rw [hnear] at hi
    exact (Finset.mem_filter.mp hi).1
  rw [hold i hi']

/-- A finite number of priority stages needs only finitely many local
inputs at each parameter. No finiteness assumption on `I` is needed. -/
theorem continuous_priorityCutIteration {Y I : Type*}
    [TopologicalSpace Y] [TopologicalSpace (Finset I)]
    [DiscreteTopology (Finset I)] {P L : ℕ}
    (N : Y → PriorityNeighborhood I P)
    (hP : 1 ≤ P) (hL : 32 * P ≤ L) (center : Y → I → ℤ)
    (hnear : ∀ i, Continuous (fun y => (N y).nearby i))
    (hpriority : ∀ i, Continuous (fun y => (N y).priority i))
    (hcenter : ∀ i, Continuous (fun y => center y i)) :
    ∀ n i, Continuous (fun y => priorityCutIteration (N y) hP hL (center y) n i) := by
  classical
  intro n
  induction n with
  | zero =>
      intro i
      simpa only [priorityCutIteration] using
        (continuous_of_discreteTopology (f := fun z : ℤ =>
          (z-3*L,z+2*L))).comp (hcenter i)
  | succ n ih =>
      intro i
      apply continuous_iff_continuousAt.mpr
      intro y
      have hn := locally_equal_of_continuous (hnear i) y
      have hp := locally_equal_of_continuous (hpriority i) y
      have hc := locally_equal_of_continuous (hcenter i) y
      have ho := locally_equal_of_continuous (ih i) y
      have hs : ∀ᶠ z in 𝓝 y, ∀ j ∈ (N y).nearby i,
          (N z).priority j = (N y).priority j ∧
            priorityCutIteration (N z) hP hL (center z) n j =
              priorityCutIteration (N y) hP hL (center y) n j := by
        apply ((N y).nearby i).eventually_all.mpr
        intro j hj
        exact (locally_equal_of_continuous (hpriority j) y).and
          (locally_equal_of_continuous (ih j) y)
      have he : ∀ᶠ z in 𝓝 y,
          priorityCutIteration (N z) hP hL (center z) (n+1) i =
            priorityCutIteration (N y) hP hL (center y) (n+1) i := by
        filter_upwards [hn, hp, hc, ho, hs] with z hn hp hc ho hs
        have hearlier := earlierPriorityCuts_congr (N z) (N y)
          (priorityCutIteration (N z) hP hL (center z) n)
          (priorityCutIteration (N y) hP hL (center y) n) n i hn
          (fun j hj => (hs j hj).1) (fun j hj => (hs j hj).2)
        simp only [priorityCutIteration, hp, hc]
        split_ifs
        · simp only [hearlier]
        · exact ho
      have he' : (fun z => priorityCutIteration (N z) hP hL (center z) (n+1) i)
          =ᶠ[𝓝 y] (fun _ => priorityCutIteration (N y) hP hL (center y) (n+1) i) := he
      exact continuousAt_const.congr he'.symm

/-- In particular, the separated final cuts produced after processing all
`P` priorities vary continuously with continuous local input data. -/
theorem continuous_priorityCuts {Y I : Type*}
    [TopologicalSpace Y] [TopologicalSpace (Finset I)]
    [DiscreteTopology (Finset I)] {P L : ℕ}
    (N : Y → PriorityNeighborhood I P)
    (hP : 1 ≤ P) (hL : 32 * P ≤ L) (center : Y → I → ℤ)
    (hnear : ∀ i, Continuous (fun y => (N y).nearby i))
    (hpriority : ∀ i, Continuous (fun y => (N y).priority i))
    (hcenter : ∀ i, Continuous (fun y => center y i)) (i : I) :
    Continuous (fun y => priorityCutIteration (N y) hP hL (center y) P i) :=
  continuous_priorityCutIteration N hP hL center hnear hpriority hcenter P i

end
end AbelianTargets
