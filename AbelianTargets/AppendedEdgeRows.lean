import AbelianTargets.BottomEdgeSplice
import AbelianTargets.PaddedRowCoordinates

/-! The concrete row data used in the first half of a bottom-edge splice. -/

namespace AbelianTargets
open scoped NNReal
noncomputable section

variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Face : Finset V → Prop}

theorem ValidRow.append_endpoint {w : List V} {p q : V} (h : ValidRow Face w)
    (hz : w.getLast? = some p) (hf : Face {p,q}) (hd : FaceDownward Face) :
    ValidRow Face (w++[q]) := by
  constructor
  · apply h.chain.append (.singleton q)
    intro a ha b hb
    have ha' : a = p := (by simpa only [hz,Option.mem_some_iff] using ha : p=a).symm
    have hb' : b = q := (by simpa only [List.head?_cons,Option.mem_some_iff] using hb : q=b).symm
    simpa only [ha',hb'] using hf
  · intro v hv
    simp only [List.mem_append,List.mem_singleton] at hv
    obtain hv | rfl := hv
    · exact h.vertices _ hv
    · exact hd hf (by intro a ha; have he := Finset.mem_singleton.mp ha; subst a; simp)

namespace FixedSlots

theorem listRow_edges (ι : V → E) {w : List V} {p : V}
    (hv : ValidRow Face w) (hz : w.getLast? = some p) (Δ : ℝ≥0)
    (hedge : ∀ a b, Face {a,b} → dist (ι a) (ι b) ≤ Δ) (j : ℕ) :
    dist (listRow ι p w j) (listRow ι p w (j+1)) ≤ Δ := by
  by_cases hj : j+1 < w.length
  · exact hedge _ _ (hv.edge_getD p j hj)
  · have h₀ := list_getD_terminal hz j (by omega)
    have h₁ := list_getD_terminal hz (j+1) (by omega)
    simp only [listRow,h₀,h₁,dist_self]
    exact Δ.property

theorem appended_seam_mem {F : Set E} (ι : V → E) {w : List V} {p q : V}
    (hz : w.getLast? = some p) (n : ℕ) (hF : Convex ℝ F)
    (hp : ι p ∈ F) (hq : ι q ∈ F) (j : ℕ) (hj : w.length-1 ≤ j) :
    appendRowEndpoint (listRow ι q (w++[q])) n (mix (ι p) (ι q) halfPoint) j ∈ F := by
  unfold appendRowEndpoint
  split
  · unfold listRow
    rw [getD_append_endpoint w p q]
    split
    · rw [list_getD_terminal hz j hj]
      exact hp
    · exact hq
  · exact mix_mem hF hp hq halfPoint

theorem appended_rows_charts (ι : V → E) {S : Set E} {Δ : ℝ≥0}
    (hc : FaceCharts Face ι S Δ) {w : List V} {p q : V}
    (hv : ValidRow Face w) (hz : w.getLast? = some p) (hf : Face {p,q})
    (n : ℕ) (hlen : w.length ≤ n+1) :
    ∀ j ≤ n+1, ∃ F : Set E, Convex ℝ F ∧ F ⊆ S ∧
      listRow ι p w j ∈ F ∧ listRow ι p w (j+1) ∈ F ∧
      appendRowEndpoint (listRow ι q (w++[q])) n (mix (ι p) (ι q) halfPoint) j ∈ F ∧
      appendRowEndpoint (listRow ι q (w++[q])) n (mix (ι p) (ι q) halfPoint) (j+1) ∈ F := by
  intro j hj
  by_cases hj' : j+1 < w.length
  · obtain ⟨F,hconv,hsub,hm⟩ := hc.chart _ (hv.edge_getD p j hj')
    have h₀ : appendRowEndpoint (listRow ι q (w++[q])) n
        (mix (ι p) (ι q) halfPoint) j = listRow ι p w j := by
      simp only [appendRowEndpoint,if_pos (show j ≤ n+1 by omega),listRow,
        getD_append_endpoint w p q,if_pos (show j < w.length by omega)]
    have h₁ : appendRowEndpoint (listRow ι q (w++[q])) n
        (mix (ι p) (ι q) halfPoint) (j+1) = listRow ι p w (j+1) := by
      simp only [appendRowEndpoint,if_pos (show j+1 ≤ n+1 by omega),listRow,
        getD_append_endpoint w p q,if_pos hj']
    refine ⟨F,hconv,hsub,hm _ (by simp),hm _ (by simp),?_,?_⟩
    · rw [h₀]; exact hm _ (by simp)
    · rw [h₁]; exact hm _ (by simp)
  · obtain ⟨F,hconv,hsub,hm⟩ := hc.chart _ hf
    have hp := hm p (by simp)
    have hq := hm q (by simp)
    refine ⟨F,hconv,hsub,?_,?_,appended_seam_mem ι hz n hconv hp hq j (by omega),
      appended_seam_mem ι hz n hconv hp hq (j+1) (by omega)⟩
    · simpa only [listRow,list_getD_terminal hz j (by omega)] using hp
    · simpa only [listRow,list_getD_terminal hz (j+1) (by omega)] using hp

theorem appended_seam_edges (ι : V → E) {S : Set E} {Δ : ℝ≥0}
    (hc : FaceCharts Face ι S Δ) {w : List V} {p q : V}
    (hv : ValidRow Face w) (hz : w.getLast? = some p) (hf : Face {p,q})
    (n : ℕ) (hlen : w.length ≤ n+1) : ∀ j ≤ n+1,
    dist (appendRowEndpoint (listRow ι q (w++[q])) n (mix (ι p) (ι q) halfPoint) j)
      (appendRowEndpoint (listRow ι q (w++[q])) n (mix (ι p) (ι q) halfPoint) (j+1)) ≤ Δ := by
  intro j hj
  by_cases hj' : j ≤ n
  · simp only [appendRowEndpoint,if_pos (show j ≤ n+1 by omega),
      if_pos (show j+1 ≤ n+1 by omega)]
    apply listRow_edges ι (hv.append_endpoint hz hf hc.downward) (by simp) Δ hc.edge_bound
  · have he : j = n+1 := by omega
    subst j
    simp only [appendRowEndpoint,if_pos (le_refl (n+1)),
      if_neg (show ¬n+1+1 ≤ n+1 by omega),listRow,getD_append_endpoint w p q,
      if_neg (show ¬n+1 < w.length by omega)]
    have h := (mix_lipschitz (ι p) (ι q) Δ (hc.edge_bound p q hf)).dist_le_mul 1 halfPoint
    rw [mix_one] at h
    exact h.trans (mul_le_of_le_one_right Δ.property (interval_dist_le_one _ _))

theorem appended_rows_corresponding_bound (ι : V → E) (C : ℝ≥0)
    (hC : ∀ a b, dist (ι a) (ι b) ≤ C) (w : List V) (p q : V) (n : ℕ) :
    ∀ j ≤ n+2, dist (listRow ι p w j)
      (appendRowEndpoint (listRow ι q (w++[q])) n (mix (ι p) (ι q) halfPoint) j) ≤ C := by
  intro j hj
  unfold appendRowEndpoint listRow
  split
  · exact hC _ _
  · have h := mix_dist_le_of_le (hC (w.getD j p) p) (hC (w.getD j p) q) halfPoint
    simpa only [mix_self] using h

end FixedSlots
end
end AbelianTargets
