import AbelianTargets.FixedRowRealization
import AbelianTargets.CarrierCharts

/-! Literal interval-carrier row moves, realized in barycentric coordinates. -/

namespace AbelianTargets

open scoped NNReal

noncomputable section

namespace IntervalCarriers

def liftVertex {K : ℕ} {A B : ℤ} (base : CarrierVertex K A B) (v : Vertex) :
    CarrierVertex K A B := if h : v ∈ carrierVertices K A B then ⟨v,h⟩ else base

theorem liftVertex_val {K : ℕ} {A B : ℤ} (base : CarrierVertex K A B) (v : Vertex)
    (hv : v ∈ carrierVertices K A B) : (liftVertex base v).1 = v := by
  simp only [liftVertex,dif_pos hv]

def vertexMass {K : ℕ} {A B : ℤ} (base : CarrierVertex K A B) (v : Vertex) :
    CarrierVertex K A B → ℝ := (Probability.dirac (liftVertex base v)).mass

theorem carrierFace_charts {m K : ℕ} {A B : ℤ} (base : CarrierVertex K A B) :
    FaceCharts (CarrierFace m K A B) (vertexMass base) (ambientRealization m K A B) 1 := by
  refine ⟨?_,?_,?_⟩
  · intro s t h ht
    exact h.downward ht
  · intro s hs
    let t := s.image (liftVertex base)
    have ht : t.image Subtype.val = s := by
      ext v
      simp only [t,Finset.mem_image]
      constructor
      · rintro ⟨u,⟨w,hw,rfl⟩,rfl⟩
        simpa only [liftVertex_val base w (hs.vertices hw)] using hw
      · intro hv
        exact ⟨liftVertex base v,⟨v,hv,rfl⟩,liftVertex_val base v (hs.vertices hv)⟩
    refine ⟨Probability.faceChart t,Probability.faceChart_convex t,
      faceChart_subset_ambient t (ht ▸ hs),?_⟩
    intro v hv
    exact Probability.dirac_mem_faceChart t _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  · intro a b _
    exact Probability.dist_le_one _ _

end IntervalCarriers

theorem BoundedTriangleRows.length_bounds {V : Type*} [DecidableEq V]
    {Face : Finset V → Prop} {B : ℕ} {w u : List V} (h : BoundedTriangleRows Face B w u) :
    w.length ≤ B ∧ u.length ≤ B := by
  induction h with
  | refl w hw => exact ⟨hw,hw⟩
  | triangle a b c hf p s hw hu => exact ⟨hw,hu⟩
  | pause a p s hw hu => exact ⟨hw,hu⟩
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ⟨ih₁.1,ih₂.2⟩

namespace FixedSlots

variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Face : Finset V → Prop}

theorem boundedTriangleRows_realize (ι : V → E) {S : Set E} {Δ : ℝ≥0}
    (hc : FaceCharts Face ι S Δ) {B : ℕ} {w u : List V}
    (h : BoundedTriangleRows Face B w u) (x z : V)
    (hx : w.head? = some x) (hz : w.getLast? = some z) (hv : ValidRow Face w) :
    ∃ F : (canonicalRow ι B x z (padRow (B+2) z w) (padRow_head hx _)
      (padRow_last hz _) (padRow_length (h.length_bounds.1.trans (by omega)))).path.Homotopy
      (canonicalRow ι B x z (padRow (B+2) z u)
        (padRow_head (h.head_eq.symm.trans hx) _) (padRow_last (h.last_eq.symm.trans hz) _)
        (padRow_length (h.length_bounds.2.trans (by omega)))).path,
      (∀ t, F t ∈ S) ∧ ∀ r, LipschitzWith (Δ*(B+1)) (F.eval r) := by
  exact fixedRowMoves_realize ι hc (h.toFixedRows hc.downward (by omega) z hv hz)
    B x z (padRow_head hx _) (padRow_last hz _)
    (padRow_length (h.length_bounds.1.trans (by omega))) (hv.pad hz _)

end FixedSlots

end

end AbelianTargets
