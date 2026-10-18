import AbelianTargets.RowValidity

/-!
# Canonical common-slot padding of every bounded cellular row chain

Each row is padded only at its endpoint. A triangle collapse becomes
one equal-slot local replacement followed by pause transport through
the entire remaining tail. A pause deletion is exactly pause transport.
The reverse moves are their inverse chains, so expansions automatically
use the pauses supplied by the common budget.
-/

namespace AbelianTargets

variable {V : Type*} [DecidableEq V] {Face : Finset V → Prop}

def padRow (N : ℕ) (z : V) (w : List V) : List V :=
  w ++ List.replicate (N-w.length) z

theorem padRow_length {N : ℕ} {z : V} {w : List V} (hw : w.length ≤ N) :
    (padRow N z w).length = N := by
  simp only [padRow,List.length_append,List.length_replicate]
  omega

theorem padded_triangle_move (hd : FaceDownward Face) (N : ℕ) (z a b c : V)
    (hf : Face {a,b,c}) (p s : List V)
    (hv : ValidRow Face (p++[a,b,c]++s))
    (hz : (p++[a,b,c]++s).getLast? = some z)
    (hlen : (p++[a,b,c]++s).length ≤ N) :
    FixedRowMoves Face (padRow N z (p++[a,b,c]++s))
      (padRow N z (p++[a,c]++s)) := by
  let k := N-(p++[a,b,c]++s).length
  have hk : N-(p++[a,c]++s).length = k+1 := by
    dsimp [k]
    simp only [List.length_append,List.length_cons,List.length_nil] at hlen ⊢
    omega
  have hf' : Face {a,b,a,c} := by
    have heq : ({a,b,a,c} : Finset V) = {a,b,c} := by ext v; simp [or_assoc,or_left_comm,or_comm]
    rw [heq]
    exact hf
  have hshort := (validRow_triangle_iff hd a b c hf p s).mp hv
  have hchain : List.IsChain (fun a b => Face {a,b}) (a::c::s) := by
    have hc := hshort.chain
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hc
    exact (List.isChain_split.mp hc).2
  have hlast : (a::c::s).getLast? = some z := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,
      List.getLast?_append_cons,List.getLast?_cons_cons] using hz
  have htail := edgeRow_of_chain_last hchain hlast
  have h₁ : FixedRowMoves Face
      (p++[a,b,c]++s++List.replicate k z)
      (p++[a,a,c]++s++List.replicate k z) := by
    simpa only [List.append_assoc] using FixedRowMoves.replace a b a c hf' p (s++List.replicate k z)
  have h₂ := htail.slide_pause_to_end.context p (List.replicate k z)
  have h₂' : FixedRowMoves Face
      (p++[a,a,c]++s++List.replicate k z)
      (p++[a,c]++s++List.replicate (k+1) z) := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.replicate_succ] using h₂
  simpa only [padRow,k,hk] using h₁.trans h₂'

theorem padded_pause_move (N : ℕ) (z a : V) (p s : List V)
    (hv : ValidRow Face (p++[a,a]++s))
    (hz : (p++[a,a]++s).getLast? = some z)
    (hlen : (p++[a,a]++s).length ≤ N) :
    FixedRowMoves Face (padRow N z (p++[a,a]++s))
      (padRow N z (p++[a]++s)) := by
  let k := N-(p++[a,a]++s).length
  have hk : N-(p++[a]++s).length = k+1 := by
    dsimp [k]
    simp only [List.length_append,List.length_cons,List.length_nil] at hlen ⊢
    omega
  have hshort := (validRow_pause_iff a p s).mp hv
  have hchain : List.IsChain (fun a b => Face {a,b}) (a::s) := by
    have hc := hshort.chain
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hc
    exact (List.isChain_split.mp hc).2
  have hlast : (a::s).getLast? = some z := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,
      List.getLast?_append_cons,List.getLast?_cons_cons] using hz
  have h := (edgeRow_of_chain_last hchain hlast).slide_pause_to_end.context p (List.replicate k z)
  change FixedRowMoves Face ((p++[a,a]++s)++List.replicate k z)
    ((p++[a]++s)++List.replicate (N-(p++[a]++s).length) z)
  rw [hk]
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.replicate_succ] using h

/-- Complete bounded-row to common-slot adapter. The canonical padding
is the same at every endpoint and every stage; no new homotopy axiom is
used. -/
theorem BoundedTriangleRows.toFixedRows {B N : ℕ} {w u : List V}
    (h : BoundedTriangleRows Face B w u) (hd : FaceDownward Face) (hBN : B ≤ N)
    (z : V) : ValidRow Face w → w.getLast? = some z →
      FixedRowMoves Face (padRow N z w) (padRow N z u) := by
  induction h with
  | refl w hl => intro hv hz; exact .refl _
  | triangle a b c hf p s hw hu =>
      intro hv hz
      exact padded_triangle_move hd N z a b c hf p s hv hz (hw.trans hBN)
  | pause a p s hw hu =>
      intro hv hz
      exact padded_pause_move N z a p s hv hz (hw.trans hBN)
  | symm h ih =>
      intro hv hz
      exact (ih ((h.valid_iff hd).mpr hv) (h.last_eq.trans hz)).symm
  | trans h₁ h₂ ih₁ ih₂ =>
      intro hv hz
      exact (ih₁ hv hz).trans (ih₂ ((h₁.valid_iff hd).mp hv) (h₁.last_eq.symm.trans hz))

end AbelianTargets
