import AbelianTargets.AppendedEdgeRows

/-! Constructing the complete moving-endpoint data from literal appended edge rows. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section
variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Face : Finset V → Prop}

def appendedSpliceData (ι : V → E) {S : Set E} {Δ C : ℝ≥0}
    (hc : FaceCharts Face ι S Δ) (hC : ∀ a b, dist (ι a) (ι b) ≤ C)
    (n : ℕ) (x p q : V) (w : List V)
    (hx : w.head? = some x) (hz : w.getLast? = some p) (hv : ValidRow Face w)
    (hf : Face {p,q}) (hlen : w.length ≤ n+1)
    (R T : BasedRow n (ι x) (ι q))
    (hR : R.vertices = listRow ι q (w++[q]))
    (F : R.path.Homotopy T.path) (hFS : ∀ t, F t ∈ S)
    (hFL : ∀ r, LipschitzWith (Δ*(n+1)) (F.eval r))
    (hFJ : ∃ J : ℝ≥0, LipschitzWith J F) :
    BottomSpliceData n (ι x) (ι p) (ι q) S Δ where
  leftRow := listRow ι p w
  carrySource := R
  carryTarget := T
  left_source := listRow_zero ι hx
  left_target := by
    unfold listRow
    rw [list_getD_terminal hz (n+2) (by omega)]
  left_edges := fun j _ => listRow_edges ι hv hz Δ hc.edge_bound j
  seam_edges := by rw [hR]; exact appended_seam_edges ι hc hv hz hf n hlen
  left_charts := by rw [hR]; exact appended_rows_charts ι hc hv hz hf n hlen
  corresponding_bound := by
    rw [hR]
    exact ⟨C,appended_rows_corresponding_bound ι C hC w p q n⟩
  edge_bound := hc.edge_bound p q hf
  edge_chart := by
    obtain ⟨F,hconv,hsub,hm⟩ := hc.chart _ hf
    exact ⟨F,hconv,hsub,hm p (by simp),hm q (by simp)⟩
  carry := F
  carry_mem := hFS
  carry_speed := hFL
  carry_joint := hFJ

end
end AbelianTargets.FixedSlots
