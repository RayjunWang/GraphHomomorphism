import AbelianTargets.FixedSlotPadding

/-! # Canonical endpoint-padded rows and their exact fixed-slot endpoints -/

namespace AbelianTargets

variable {V : Type*} [DecidableEq V] {Face : Finset V → Prop}

theorem FixedRowMoves.valid_iff {w u : List V} (h : FixedRowMoves Face w u)
    (hd : FaceDownward Face) : ValidRow Face w ↔ ValidRow Face u := by
  induction h with
  | refl w => rfl
  | replace a b b' c hf p s =>
      have hf₀ : Face {a,b,c} := hd hf (by
        intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
        obtain rfl | rfl | rfl := hv <;> simp)
      have hf₁ : Face {a,b',c} := hd hf (by
        intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
        obtain rfl | rfl | rfl := hv <;> simp)
      exact (validRow_triangle_iff hd a b c hf₀ p s).trans
        (validRow_triangle_iff hd a b' c hf₁ p s).symm
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem ValidRow.pad {w : List V} (h : ValidRow Face w) {z : V}
    (hz : w.getLast? = some z) (N : ℕ) : ValidRow Face (padRow N z w) := by
  have hzmem : z ∈ w := List.mem_of_mem_getLast? (by simp [hz])
  have hzface := h.vertices z hzmem
  have hzz : Face {z,z} := by simpa using hzface
  have hrep : ∀ k, List.IsChain (fun a b => Face {a,b}) (List.replicate k z) := by
    intro k
    induction k with
    | zero => exact .nil
    | succ k ih =>
      cases k with
      | zero => exact .singleton z
      | succ k => exact .cons_cons hzz ih
  constructor
  · apply h.chain.append (hrep _)
    intro a ha b hb
    have ha' : a = z := (by simpa only [hz,Option.mem_some_iff] using ha : z = a).symm
    have hb' : b = z := by
      cases hk : N-w.length with
      | zero => simp [hk] at hb
      | succ k =>
        have hb'' : z = b := by
          simpa only [hk,List.replicate_succ,List.head?_cons,Option.mem_some_iff] using hb
        exact hb''.symm
    simpa only [ha',hb'] using hzz
  · intro v hv
    simp only [padRow,List.mem_append] at hv
    obtain hv | hv := hv
    · exact h.vertices v hv
    · have hv' : v = z := (List.mem_replicate.mp hv).2
      simpa only [hv'] using hzface

theorem padRow_head {w : List V} {x z : V} (hx : w.head? = some x) (N : ℕ) :
    (padRow N z w).head? = some x := by
  cases w with
  | nil => simp at hx
  | cons a w => simpa only [padRow,List.cons_append,List.head?_cons] using hx

theorem padRow_last {w : List V} {z : V} (hz : w.getLast? = some z) (N : ℕ) :
    (padRow N z w).getLast? = some z := by
  unfold padRow
  cases hk : N-w.length with
  | zero => simpa only [List.replicate_zero,List.append_nil] using hz
  | succ k =>
    have hl : (z :: List.replicate k z).getLast? = some z := by
      clear hk
      induction k with
      | zero => rfl
      | succ k ih => simpa only [List.replicate_succ,List.getLast?_cons_cons] using ih
    simpa only [List.replicate_succ,List.getLast?_append_cons] using hl

theorem ValidRow.edge_getD {w : List V} (h : ValidRow Face w) (z : V)
    (j : ℕ) (hj : j+1 < w.length) : Face {w.getD j z,w.getD (j+1) z} := by
  have h' := h.chain.getElem j hj
  have hj₀ : j < w.length := by omega
  simpa only [← List.getElem_eq_getD (h := hj₀) z,
    ← List.getElem_eq_getD (h := hj) z] using h'

namespace FixedSlots

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def listRow (ι : V → E) (z : V) (w : List V) : ℕ → E := fun j => ι (w.getD j z)

theorem listRow_zero (ι : V → E) {x z : V} {w : List V}
    (hx : w.head? = some x) : listRow ι z w 0 = ι x := by
  cases w with
  | nil => simp at hx
  | cons a w =>
      have ha : a = x := Option.some.inj hx
      simp only [listRow,List.getD_cons_zero,ha]

theorem listRow_last (ι : V → E) {n : ℕ} {z : V} {w : List V}
    (hlen : w.length = n+2) (hz : w.getLast? = some z) : listRow ι z w (n+1) = ι z := by
  have hi : n+1 = w.length-1 := by omega
  simp only [listRow,List.getD_eq_getElem?_getD,hi,← List.getLast?_eq_getElem?,hz,Option.getD_some]

def canonicalRow (ι : V → E) (n : ℕ) (x z : V) (w : List V)
    (hx : w.head? = some x) (hz : w.getLast? = some z) (hlen : w.length = n+2) :
    BasedRow n (ι x) (ι z) where
  vertices := listRow ι z w
  source := listRow_zero ι hx
  target := listRow_last ι hlen hz

theorem canonicalRow_edges (ι : V → E) {n : ℕ} {x z : V} {w : List V}
    (hx : w.head? = some x) (hz : w.getLast? = some z) (hlen : w.length = n+2)
    (hvalid : ValidRow Face w) (Δ : ℝ≥0)
    (hedge : ∀ a b, Face {a,b} → dist (ι a) (ι b) ≤ Δ) :
    ∀ j ≤ n, dist ((canonicalRow ι n x z w hx hz hlen).vertices j)
      ((canonicalRow ι n x z w hx hz hlen).vertices (j+1)) ≤ Δ := by
  intro j hj
  apply hedge
  exact hvalid.edge_getD z j (by omega)

end FixedSlots

end AbelianTargets
