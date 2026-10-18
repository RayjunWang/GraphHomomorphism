import AbelianTargets.FixedRowRealization
import AbelianTargets.JointHomotopyGluing

/-! The padded-row realization is jointly Lipschitz as well as uniformly
Lipschitz in path time. Its finite joint constant may depend on the row count. -/

namespace AbelianTargets
open scoped NNReal

theorem homotopy_symm_joint_lipschitz {Z : Type*} [MetricSpace Z]
    {p q : Z} {P Q : Path p q} (F : P.Homotopy Q) {J : ℝ≥0}
    (hF : LipschitzWith J F) : LipschitzWith J F.symm := by
  have hr : LipschitzWith 1 (fun t : unitInterval × unitInterval =>
      (unitInterval.symm t.1,t.2)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hd : dist (unitInterval.symm x.1) (unitInterval.symm y.1) = dist x.1 y.1 := by
      change |(1-(x.1 : ℝ))-(1-(y.1 : ℝ))| = |(x.1 : ℝ)-(y.1 : ℝ)|
      rw [show (1-(x.1 : ℝ))-(1-(y.1 : ℝ)) = -((x.1 : ℝ)-(y.1 : ℝ)) by ring,abs_neg]
    change max _ _ ≤ (1 : ℝ)*max _ _
    rw [hd,one_mul]
  simpa only [mul_one] using hF.comp hr

namespace FixedSlots
variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Face : Finset V → Prop}

theorem fixedRowMoves_realize_joint (ι : V → E) {S : Set E} {Δ C : ℝ≥0}
    (hc : FaceCharts Face ι S Δ) (hC : ∀ a b, dist (ι a) (ι b) ≤ C)
    {w u : List V} (h : FixedRowMoves Face w u)
    (n : ℕ) (x z : V) (hx : w.head? = some x) (hz : w.getLast? = some z)
    (hw : w.length = n+2) (hv : ValidRow Face w) :
    ∃ F : (canonicalRow ι n x z w hx hz hw).path.Homotopy
      (canonicalRow ι n x z u (h.head_eq.symm.trans hx) (h.last_eq.symm.trans hz)
        (h.length_eq.symm.trans hw)).path,
      (∀ t, F t ∈ S) ∧ (∀ r, LipschitzWith (Δ*(n+1)) (F.eval r)) ∧
        ∃ J : ℝ≥0, LipschitzWith J F := by
  induction h with
  | refl w =>
    let R := canonicalRow ι n x z w hx hz hw
    have he := canonicalRow_edges ι hx hz hw hv Δ hc.edge_bound
    refine ⟨R.homotopy R,?_,R.homotopy_path_time_lipschitz R Δ he he,
      Δ*(n+1)+C,?_⟩
    · intro t
      apply canonicalRow_homotopy_mem ι hx hz hw hx hz hw hc _ t
      intro j hj
      apply hc.downward (hv.edge_getD z j (by omega))
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
      tauto
    · exact rowHomotopy_joint_lipschitz R.vertices R.vertices n
        (R.source.trans R.source.symm) (R.target.trans R.target.symm) Δ C he he
        (fun j _ => hC _ _)
  | replace a b b' c hf p s =>
    let h : FixedRowMoves Face (p++[a,b,c]++s) (p++[a,b',c]++s) :=
      .replace a b b' c hf p s
    let hx' := h.head_eq.symm.trans hx
    let hz' := h.last_eq.symm.trans hz
    let hu := h.length_eq.symm.trans hw
    let R := canonicalRow ι n x z (p++[a,b,c]++s) hx hz hw
    let T := canonicalRow ι n x z (p++[a,b',c]++s) hx' hz' hu
    have he₀ := canonicalRow_edges ι hx hz hw hv Δ hc.edge_bound
    have he₁ := canonicalRow_edges ι hx' hz' hu ((h.valid_iff hc.downward).mp hv) Δ hc.edge_bound
    refine ⟨R.homotopy T,?_,R.homotopy_path_time_lipschitz T Δ he₀ he₁,Δ*(n+1)+C,?_⟩
    · intro t
      apply canonicalRow_homotopy_mem ι hx hz hw hx' hz' hu hc _ t
      intro j hj
      exact contextual_four_corners_face hc.downward p s a b b' c z hf hv j (by omega)
    · exact rowHomotopy_joint_lipschitz R.vertices T.vertices n
        (R.source.trans T.source.symm) (R.target.trans T.target.symm) Δ C he₀ he₁
        (fun j _ => hC _ _)
  | @symm w u h ih =>
    obtain ⟨F,hFS,hFL,J,hFJ⟩ := ih (h.head_eq.trans hx) (h.last_eq.trans hz)
      (h.length_eq.trans hw) ((h.valid_iff hc.downward).mpr hv)
    exact ⟨F.symm,(fun t => hFS (unitInterval.symm t.1,t.2)),
      (fun r => hFL (unitInterval.symm r)),J,homotopy_symm_joint_lipschitz F hFJ⟩
  | @trans w u v h₁ h₂ ih₁ ih₂ =>
    obtain ⟨F,hFS,hFL,J,hFJ⟩ := ih₁ hx hz hw hv
    obtain ⟨G,hGS,hGL,L,hGJ⟩ := ih₂ (h₁.head_eq.symm.trans hx) (h₁.last_eq.symm.trans hz)
      (h₁.length_eq.symm.trans hw) ((h₁.valid_iff hc.downward).mp hv)
    refine ⟨F.trans G,?_,homotopy_trans_path_lipschitz F G hFL hGL,
      4*max J L,homotopy_trans_joint_lipschitz F G hFJ hGJ⟩
    intro t
    rw [Path.Homotopy.trans_apply]
    split
    · exact hFS _
    · exact hGS _

end FixedSlots
end AbelianTargets
