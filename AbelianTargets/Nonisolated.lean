import AbelianTargets.ReducedWalks

/-!
# Removing isolated target vertices

The nonisolated induced graph has a total neighbor selection.  Retraction
onto it preserves the odd torsion hypotheses of the target paper.
-/

namespace AbelianTargets

noncomputable section

variable {V : Type*} (H : SimpleGraph V)

def nonisolatedVertices : Set V := {v | ∃ w, H.Adj v w}

def NonisolatedGraph : SimpleGraph (nonisolatedVertices H) := H.induce (nonisolatedVertices H)

theorem nonisolated_neighbor (v : nonisolatedVertices H) :
    ∃ w : nonisolatedVertices H, (NonisolatedGraph H).Adj v w := by
  obtain ⟨w, hw⟩ := v.property
  exact ⟨⟨w, ⟨v.val, hw.symm⟩⟩, hw⟩

def nonisolatedNeighbor (v : nonisolatedVertices H) : nonisolatedVertices H :=
  Classical.choose (nonisolated_neighbor H v)

theorem nonisolatedNeighbor_adj (v : nonisolatedVertices H) :
    (NonisolatedGraph H).Adj v (nonisolatedNeighbor H v) :=
  Classical.choose_spec (nonisolated_neighbor H v)

def nonisolatedRetraction (b : nonisolatedVertices H) : H →g NonisolatedGraph H := by
  classical
  exact {
    toFun := fun v => if hv : v ∈ nonisolatedVertices H then ⟨v, hv⟩ else b
    map_rel' := by
      intro u v huv
      have hu : u ∈ nonisolatedVertices H := ⟨v, huv⟩
      have hv : v ∈ nonisolatedVertices H := ⟨u, huv.symm⟩
      simpa only [dif_pos hu, dif_pos hv] using huv }

theorem oddWalk_nonisolated {b : V} (γ : H.Walk b b) (hodd : Odd γ.length) :
    b ∈ nonisolatedVertices H := by
  cases γ with
  | nil => simp only [SimpleGraph.Walk.length_nil] at hodd; exact (Nat.not_odd_zero hodd).elim
  | cons h p => exact ⟨_, h⟩

theorem hasOddTorsion_nonisolated (h : HasOddTorsion H) : HasOddTorsion (NonisolatedGraph H) := by
  obtain ⟨b, γ, hodd, N, hN, hnull⟩ := h
  let b' : nonisolatedVertices H := ⟨b, oddWalk_nonisolated H γ hodd⟩
  let f := nonisolatedRetraction H b'
  exact ⟨f b, γ.map f, by simpa using hodd, N, hN, by
    simpa only [loopPower_map, SimpleGraph.Walk.map_nil] using hnull.map f⟩

theorem hasOddInvolution_nonisolated (h : HasOddInvolution H) : HasOddInvolution (NonisolatedGraph H) := by
  obtain ⟨b, γ, hodd, hnull⟩ := h
  let b' : nonisolatedVertices H := ⟨b, oddWalk_nonisolated H γ hodd⟩
  let f := nonisolatedRetraction H b'
  exact ⟨f b, γ.map f, by simpa using hodd, by
    simpa only [loopPower_map, SimpleGraph.Walk.map_nil] using hnull.map f⟩

end

end AbelianTargets
