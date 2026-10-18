import AbelianTargets.FixedRowCharts

/-! A complete realization of padded combinatorial row moves by endpoint-fixed
homotopies. The path-time constant depends only on the common slot budget. -/

namespace AbelianTargets

open scoped NNReal

variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Face : Finset V → Prop}

structure FaceCharts (Face : Finset V → Prop) (ι : V → E) (S : Set E) (Δ : ℝ≥0) : Prop where
  downward : FaceDownward Face
  chart : ∀ s, Face s → ∃ F : Set E, Convex ℝ F ∧ F ⊆ S ∧ ∀ v ∈ s, ι v ∈ F
  edge_bound : ∀ a b, Face {a,b} → dist (ι a) (ι b) ≤ Δ

namespace FixedSlots

theorem canonicalRow_homotopy_mem (ι : V → E) {n : ℕ} {x z : V} {w u : List V}
    (hx : w.head? = some x) (hz : w.getLast? = some z) (hw : w.length = n+2)
    (hx' : u.head? = some x) (hz' : u.getLast? = some z) (hu : u.length = n+2)
    {S : Set E} {Δ : ℝ≥0} (hc : FaceCharts Face ι S Δ)
    (hquad : ∀ j ≤ n, Face {w.getD j z,w.getD (j+1) z,u.getD j z,u.getD (j+1) z})
    (t : unitInterval × unitInterval) :
    ((canonicalRow ι n x z w hx hz hw).homotopy
      (canonicalRow ι n x z u hx' hz' hu)) t ∈ S := by
  let R := canonicalRow ι n x z w hx hz hw
  let T := canonicalRow ι n x z u hx' hz' hu
  change rowHomotopy R.vertices T.vertices n (R.source.trans T.source.symm)
    (R.target.trans T.target.symm) t ∈ S
  apply rowHomotopy_mem_charts R.vertices T.vertices n (R.source.trans T.source.symm)
    (R.target.trans T.target.symm) _ t
  intro j hj
  obtain ⟨F,hconv,hsub,hv⟩ := hc.chart _ (hquad j hj)
  refine ⟨F,hconv,hsub,?_,?_,?_,?_⟩ <;>
    apply hv <;> simp

theorem fixedRowMoves_realize (ι : V → E) {S : Set E} {Δ : ℝ≥0}
    (hc : FaceCharts Face ι S Δ) {w u : List V} (h : FixedRowMoves Face w u)
    (n : ℕ) (x z : V) (hx : w.head? = some x) (hz : w.getLast? = some z)
    (hw : w.length = n+2) (hv : ValidRow Face w) :
    ∃ F : (canonicalRow ι n x z w hx hz hw).path.Homotopy
      (canonicalRow ι n x z u (h.head_eq.symm.trans hx) (h.last_eq.symm.trans hz)
        (h.length_eq.symm.trans hw)).path,
      (∀ t, F t ∈ S) ∧ ∀ r, LipschitzWith (Δ*(n+1)) (F.eval r) := by
  induction h with
  | refl w =>
    let R := canonicalRow ι n x z w hx hz hw
    refine ⟨R.homotopy R,?_,R.homotopy_path_time_lipschitz R Δ
      (canonicalRow_edges ι hx hz hw hv Δ hc.edge_bound)
      (canonicalRow_edges ι hx hz hw hv Δ hc.edge_bound)⟩
    intro t
    apply canonicalRow_homotopy_mem ι hx hz hw hx hz hw hc _ t
    intro j hj
    apply hc.downward (hv.edge_getD z j (by omega))
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
    tauto
  | replace a b b' c hf p s =>
    let h : FixedRowMoves Face (p++[a,b,c]++s) (p++[a,b',c]++s) :=
      .replace a b b' c hf p s
    let hx' := h.head_eq.symm.trans hx
    let hz' := h.last_eq.symm.trans hz
    let hu := h.length_eq.symm.trans hw
    let R := canonicalRow ι n x z (p++[a,b,c]++s) hx hz hw
    let T := canonicalRow ι n x z (p++[a,b',c]++s) hx' hz' hu
    refine ⟨R.homotopy T,?_,R.homotopy_path_time_lipschitz T Δ
      (canonicalRow_edges ι hx hz hw hv Δ hc.edge_bound)
      (canonicalRow_edges ι hx' hz' hu ((h.valid_iff hc.downward).mp hv) Δ hc.edge_bound)⟩
    intro t
    apply canonicalRow_homotopy_mem ι hx hz hw hx' hz' hu hc _ t
    intro j hj
    exact contextual_four_corners_face hc.downward p s a b b' c z hf hv j (by omega)
  | @symm w u h ih =>
    obtain ⟨F,hFS,hFL⟩ := ih (h.head_eq.trans hx) (h.last_eq.trans hz)
      (h.length_eq.trans hw) ((h.valid_iff hc.downward).mpr hv)
    refine ⟨F.symm,?_,?_⟩
    · intro t
      exact hFS (unitInterval.symm t.1,t.2)
    · intro r
      exact hFL (unitInterval.symm r)
  | @trans w u v h₁ h₂ ih₁ ih₂ =>
    obtain ⟨F,hFS,hFL⟩ := ih₁ hx hz hw hv
    obtain ⟨G,hGS,hGL⟩ := ih₂ (h₁.head_eq.symm.trans hx) (h₁.last_eq.symm.trans hz)
      (h₁.length_eq.symm.trans hw) ((h₁.valid_iff hc.downward).mp hv)
    refine ⟨F.trans G,?_,homotopy_trans_path_lipschitz F G hFL hGL⟩
    intro t
    rw [Path.Homotopy.trans_apply]
    split
    · exact hFS _
    · exact hGS _

end FixedSlots

end AbelianTargets
