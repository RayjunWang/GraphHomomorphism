import AbelianTargets.CarrierRowRealization
import AbelianTargets.ControlledRowRealization

/-! Bounded carrier row certificates have actual jointly Lipschitz realizations. -/

namespace AbelianTargets
open scoped NNReal
noncomputable section

namespace FixedSlots
variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Face : Finset V → Prop}

theorem boundedTriangleRows_realize_joint (ι : V → E) {S : Set E} {Δ C : ℝ≥0}
    (hc : FaceCharts Face ι S Δ) (hC : ∀ a b, dist (ι a) (ι b) ≤ C)
    {B : ℕ} {w u : List V} (h : BoundedTriangleRows Face B w u) (x z : V)
    (hx : w.head? = some x) (hz : w.getLast? = some z) (hv : ValidRow Face w) :
    ∃ F : (canonicalRow ι B x z (padRow (B+2) z w) (padRow_head hx _)
      (padRow_last hz _) (padRow_length (h.length_bounds.1.trans (by omega)))).path.Homotopy
      (canonicalRow ι B x z (padRow (B+2) z u)
        (padRow_head (h.head_eq.symm.trans hx) _) (padRow_last (h.last_eq.symm.trans hz) _)
        (padRow_length (h.length_bounds.2.trans (by omega)))).path,
      (∀ t, F t ∈ S) ∧ (∀ r, LipschitzWith (Δ*(B+1)) (F.eval r)) ∧
        ∃ J : ℝ≥0, LipschitzWith J F := by
  exact fixedRowMoves_realize_joint ι hc hC (h.toFixedRows hc.downward (by omega) z hv hz)
    B x z (padRow_head hx _) (padRow_last hz _)
    (padRow_length (h.length_bounds.1.trans (by omega))) (hv.pad hz _)

end FixedSlots

namespace IntervalCarriers

@[simp] theorem WordPath.vertices_head {m : ℕ} {x z : Vertex} {w : List BSLetter}
    (p : WordPath m x w z) : p.vertices.head? = some x := by
  cases p <;> rfl

@[simp] theorem WordPath.vertices_last {m : ℕ} {x z : Vertex} {w : List BSLetter}
    (p : WordPath m x w z) : p.vertices.getLast? = some z := by
  induction p with
  | nil x => rfl
  | cons h p ih =>
    cases p with
    | nil y => rfl
    | cons h' q => simpa only [WordPath.vertices,List.getLast?_cons_cons] using ih

def carrierBase (K R : ℕ) : CarrierVertex K 0 R :=
  ⟨(0,0),mem_carrierVertices.mpr ⟨le_rfl,by positivity,Nat.zero_le _⟩⟩

def carryRowBudget (m R : ℕ) : ℕ := (m+1)*(Nat.log m R+1)+2*m+5

theorem exists_joint_carrier_carry (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n < R) :
    ∃ (p : WordPath m (0,0) (compressedWord m hm n++[BSLetter.a]) ((n+1:ℕ),0))
      (q : WordPath m (0,0) (compressedWord m hm (n+1)) ((n+1:ℕ),0))
      (hp : ∀ v ∈ p.vertices, v ∈ carrierVertices (Nat.log m R) 0 R)
      (hq : ∀ v ∈ q.vertices, v ∈ carrierVertices (Nat.log m R) 0 R),
      let B := carryRowBudget m R
      let ι := vertexMass (carrierBase (Nat.log m R) R)
      ∃ (hpl : p.vertices.length ≤ B) (hql : q.vertices.length ≤ B)
        (F : (FixedSlots.canonicalRow ι B (0,0) ((n+1:ℕ),0)
          (padRow (B+2) ((n+1:ℕ),0) p.vertices) (padRow_head p.vertices_head _)
          (padRow_last p.vertices_last _) (padRow_length (hpl.trans (by omega)))).path.Homotopy
          (FixedSlots.canonicalRow ι B (0,0) ((n+1:ℕ),0)
          (padRow (B+2) ((n+1:ℕ),0) q.vertices) (padRow_head q.vertices_head _)
          (padRow_last q.vertices_last _) (padRow_length (hql.trans (by omega)))).path),
        (∀ t, F t ∈ ambientRealization m (Nat.log m R) 0 R) ∧
        (∀ r, LipschitzWith (B+1) (F.eval r)) ∧ ∃ J : ℝ≥0, LipschitzWith J F := by
  obtain ⟨p,q,hp,hq,hrows⟩ := exists_bounded_carrier_carry_rows m hm R n hn
  have hl := hrows.length_bounds
  refine ⟨p,q,hp,hq,hl.1,hl.2,?_⟩
  obtain ⟨F,hFS,hFL,hFJ⟩ := FixedSlots.boundedTriangleRows_realize_joint
    (vertexMass (carrierBase (Nat.log m R) R)) (carrierFace_charts _) (C := 1)
    (fun a b => Probability.dist_le_one _ _) hrows (0,0) ((n+1:ℕ),0)
    p.vertices_head p.vertices_last (p.validRow (by omega) hp)
  exact ⟨F,hFS,by simpa only [one_mul] using hFL,hFJ⟩

end IntervalCarriers
end
end AbelianTargets
