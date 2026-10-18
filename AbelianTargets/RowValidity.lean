import AbelianTargets.PauseSliding
import Mathlib.Data.List.Chain

/-! # Valid edge rows and preservation under the actual cellular moves -/

namespace AbelianTargets

variable {V : Type*} [DecidableEq V] {Face : Finset V → Prop}

def FaceDownward (Face : Finset V → Prop) : Prop :=
  ∀ ⦃s t : Finset V⦄, Face s → t ⊆ s → Face t

structure ValidRow (Face : Finset V → Prop) (w : List V) : Prop where
  chain : List.IsChain (fun a b => Face {a,b}) w
  vertices : ∀ a ∈ w, Face {a}

theorem face_pair_of_triangle (hd : FaceDownward Face) {a b c : V}
    (hf : Face {a,b,c}) : Face {a,b} ∧ Face {b,c} ∧ Face {a,c} := by
  constructor
  · apply hd hf
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
    obtain rfl | rfl := hv <;> simp
  · constructor
    · apply hd hf
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
      obtain rfl | rfl := hv <;> simp
    · apply hd hf
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
      obtain rfl | rfl := hv <;> simp

theorem face_vertices_of_triangle (hd : FaceDownward Face) {a b c : V}
    (hf : Face {a,b,c}) : Face {a} ∧ Face {b} ∧ Face {c} := by
  have hp := face_pair_of_triangle hd hf
  constructor
  · apply hd hp.1
    intro v hv
    have hv' : v = a := Finset.mem_singleton.mp hv
    subst v
    simp
  · constructor
    · apply hd hp.1
      intro v hv
      have hv' : v = b := Finset.mem_singleton.mp hv
      subst v
      simp
    · apply hd hp.2.2
      intro v hv
      have hv' : v = c := Finset.mem_singleton.mp hv
      subst v
      simp

theorem validRow_triangle_iff (hd : FaceDownward Face) (a b c : V)
    (hf : Face {a,b,c}) (p s : List V) :
    ValidRow Face (p++[a,b,c]++s) ↔ ValidRow Face (p++[a,c]++s) := by
  obtain ⟨hab,hbc,hac⟩ := face_pair_of_triangle hd hf
  obtain ⟨ha,hb,hc⟩ := face_vertices_of_triangle hd hf
  have hchain : List.IsChain (fun a b => Face {a,b}) (p++[a,b,c]++s) ↔
      List.IsChain (fun a b => Face {a,b}) (p++[a,c]++s) := by
    simp only [List.append_assoc,List.cons_append,List.nil_append,List.isChain_append_cons_cons,
      List.isChain_cons_cons,hab,hbc,hac,true_and,and_true]
  have hvert : (∀ v ∈ p++[a,b,c]++s, Face {v}) ↔
      (∀ v ∈ p++[a,c]++s, Face {v}) := by
    simp only [List.mem_append,List.mem_cons,List.mem_nil_iff,or_false,or_assoc]
    constructor
    · intro h v hv
      apply h v
      obtain hv | rfl | rfl | hv := hv
      · exact Or.inl hv
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hv)))
    · intro h v hv
      obtain hv | rfl | rfl | rfl | hv := hv
      · exact h v (Or.inl hv)
      · exact ha
      · exact hb
      · exact hc
      · exact h v (Or.inr (Or.inr (Or.inr hv)))
  exact ⟨fun h => ⟨hchain.mp h.chain,hvert.mp h.vertices⟩,
    fun h => ⟨hchain.mpr h.chain,hvert.mpr h.vertices⟩⟩

theorem validRow_pause_iff (a : V) (p s : List V) :
    ValidRow Face (p++[a,a]++s) ↔ ValidRow Face (p++[a]++s) := by
  have hvert : (∀ v ∈ p++[a,a]++s, Face {v}) ↔
      (∀ v ∈ p++[a]++s, Face {v}) := by
    simp [List.forall_mem_append,and_assoc]
  constructor
  · intro h
    have ha : Face {a} := h.vertices a (by simp)
    have haa : Face {a,a} := by simpa using ha
    have hc := h.chain
    simp only [List.append_assoc,List.cons_append,List.nil_append,List.isChain_append_cons_cons,
      haa,true_and,and_true] at hc
    refine ⟨?_,hvert.mp h.vertices⟩
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using (List.isChain_split.mpr hc)
  · intro h
    have ha : Face {a} := h.vertices a (by simp)
    have haa : Face {a,a} := by simpa using ha
    constructor
    · have hc := h.chain
      simp only [List.append_assoc,List.cons_append,List.nil_append] at hc
      have hc' := List.isChain_split.mp hc
      simpa only [List.append_assoc,List.cons_append,List.nil_append,List.isChain_append_cons_cons,
        haa,true_and,and_true] using hc'
    · exact hvert.mpr h.vertices

theorem BoundedTriangleRows.valid_iff {B : ℕ} {w z : List V}
    (h : BoundedTriangleRows Face B w z) (hd : FaceDownward Face) :
    ValidRow Face w ↔ ValidRow Face z := by
  induction h with
  | refl w hl => rfl
  | triangle a b c hf p s hw hz => exact validRow_triangle_iff hd a b c hf p s
  | pause a p s hw hz => exact validRow_pause_iff a p s
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem EdgeRow.isChain {a z : V} {tail : List V} (h : EdgeRow Face a tail z) :
    List.IsChain (fun a b => Face {a,b}) (a::tail) := by
  induction h with
  | nil a => exact .singleton a
  | cons hf h ih => exact .cons_cons hf ih

theorem EdgeRow.last {a z : V} {tail : List V} (h : EdgeRow Face a tail z) :
    (a::tail).getLast? = some z := by
  induction h with
  | nil a => rfl
  | @cons a b z tail hf h ih =>
    simpa only [List.getLast?_cons_cons] using ih

theorem edgeRow_of_chain_last {a z : V} {tail : List V}
    (hc : List.IsChain (fun a b => Face {a,b}) (a::tail))
    (hz : (a::tail).getLast? = some z) : EdgeRow Face a tail z := by
  induction tail generalizing a with
  | nil =>
      have ha : a = z := Option.some.inj hz
      subst z
      exact .nil a
  | cons b tail ih =>
      have hpair := List.isChain_cons_cons.mp hc
      exact .cons hpair.1 (ih hpair.2 (by simpa only [List.getLast?_cons_cons] using hz))

namespace IntervalCarriers

theorem WordPath.validRow {m K : ℕ} {A B : ℤ} {x z : Vertex} {w : List BSLetter}
    (hm : 1 ≤ m) (p : WordPath m x w z)
    (hp : ∀ v ∈ p.vertices, v ∈ carrierVertices K A B) :
    ValidRow (CarrierFace m K A B) p.vertices := by
  have hc := (p.edgeRow hm hp).isChain
  have hrow : p.vertices = x :: p.vertices.tail := by cases p <;> rfl
  refine ⟨by simpa only [← hrow] using hc,?_⟩
  intro v hv
  exact Or.inl ⟨v,hp v hv,Finset.Subset.refl _⟩

end IntervalCarriers

end AbelianTargets
