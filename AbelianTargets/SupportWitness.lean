import AbelianTargets.SupportTorsion
import AbelianTargets.ProbabilityMap
import AbelianTargets.Nonisolated

/-!
# Support-space data from an arbitrary odd torsion target

This file removes the intermediate total-neighbor-choice hypothesis.
Every finite graph satisfying the actual odd torsion condition supplies
the two swapped paths and a nullhomotopy of their alternating power.
-/

namespace AbelianTargets

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {V : Type*} [Fintype V] (H : SimpleGraph V)

/-- The concrete geometric data needed to map the two generator edges and
fill the relation cells of the parity cover. -/
structure SupportTorsionData where
  base : SupportPair H
  a : Path base (SupportPair.swap H base)
  b : Path (SupportPair.swap H base) base
  b_swap : ∀ t, b t = SupportPair.swap H (a t)
  power : ℕ
  power_pos : 0 < power
  null_power : (pathLoopPower (a.trans b) power).Homotopic (Path.refl base)

namespace SupportTorsionData

variable {H}

theorem boundary_null (D : SupportTorsionData H) :
    (D.a.trans ((pathLoopPower (D.a.trans D.b) D.power).trans D.a).symm).Homotopic
      (Path.refl D.base) :=
  presentation_boundary_nullhomotopic D.a _ D.null_power

theorem other_boundary_null (D : SupportTorsionData H) :
    ((D.a.trans ((pathLoopPower (D.a.trans D.b) D.power).trans D.a).symm).map
      (SupportPair.continuous_swap H)).Homotopic (Path.refl (SupportPair.swap H D.base)) := by
  simpa using D.boundary_null.map (SupportPair.swapMap H)

variable {W : Type*} [Fintype W] {J : SimpleGraph W}

private theorem map_loopPower {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : X} (P : Path p p) {f : X → Y} (hf : Continuous f) (n : ℕ) :
    (pathLoopPower P n).map hf = pathLoopPower (P.map hf) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (P.trans (pathLoopPower P n)).map hf = (P.map hf).trans (pathLoopPower (P.map hf) n)
    rw [Path.map_trans, ih]

/-- Graph homomorphisms preserve the actual path and nullhomotopy data. -/
def map (f : H →g J) (D : SupportTorsionData H) : SupportTorsionData J := by
  let p := SupportPair.map f D.base
  let a : Path p (SupportPair.swap J p) :=
    (D.a.map (SupportPair.continuous_map f)).cast rfl (SupportPair.map_swap f D.base).symm
  let b : Path (SupportPair.swap J p) p :=
    (D.b.map (SupportPair.continuous_map f)).cast (SupportPair.map_swap f D.base).symm rfl
  have hab : ∀ t, b t = SupportPair.swap J (a t) := by
    intro t
    change SupportPair.map f (D.b t) = SupportPair.swap J (SupportPair.map f (D.a t))
    rw [D.b_swap, SupportPair.map_swap]
  have hloop : (D.a.trans D.b).map (SupportPair.continuous_map f) = a.trans b := by
    apply Path.ext
    funext t
    simp only [Path.map_trans, Path.trans_apply]
    split_ifs <;> rfl
  refine {
    base := p
    a := a
    b := b
    b_swap := hab
    power := D.power
    power_pos := D.power_pos
    null_power := ?_ }
  have hnull := D.null_power.map (SupportPair.continuousMap f)
  simpa only [map_loopPower, hloop] using hnull

end SupportTorsionData

/-- Every finite target with odd reduced torsion has genuine equivariant
generator paths and genuine filled relation-cell boundary paths. -/
theorem supportTorsionData_of_oddTorsion (hH : HasOddTorsion H) :
    Nonempty (SupportTorsionData H) := by
  classical
  let J := NonisolatedGraph H
  letI : Fintype (nonisolatedVertices H) := Fintype.ofFinite _
  obtain ⟨a, γ, hodd, N, hN, hnull⟩ := hasOddTorsion_nonisolated H hH
  let s := nonisolatedNeighbor H
  have hs : ∀ v, J.Adj v (s v) := nonisolatedNeighbor_adj H
  let α := oddSupportPath J s hs γ hodd
  let β := swappedReturnPath J α
  obtain ⟨k, hk, hP⟩ := oddSupportPath_torsion J s hs γ hodd hnull
  have hkpos : 0 < k := by omega
  let D : SupportTorsionData J := {
    base := SupportPair.vertex J (hs a)
    a := α
    b := β
    b_swap := fun _ => rfl
    power := k
    power_pos := hkpos
    null_power := hP }
  exact ⟨D.map (SimpleGraph.Embedding.induce (nonisolatedVertices H)).toHom⟩

theorem supportTorsionData_of_oddInvolution (hH : HasOddInvolution H) :
    Nonempty (SupportTorsionData H) :=
  supportTorsionData_of_oddTorsion H hH.hasOddTorsion

end

end AbelianTargets
