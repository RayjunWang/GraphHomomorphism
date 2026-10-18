import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The literal finite interval-carrier skeleton

Vertices are the pairs representing `a^r t^j`. Horizontal edges at height
`j` have displacement `m^j`, vertical edges change height by one, and a
relation polygon has `m` lower edges and one upper edge. This module checks
finiteness, nesting, translation covariance, and all vertices of the
relation polygons. The controlled geometric contraction is a separate
obligation; a finite graph skeleton alone does not supply that contraction.
-/

namespace AbelianTargets.IntervalCarriers

abbrev Vertex := ℤ × ℕ

def translate (s : ℤ) (v : Vertex) : Vertex := (v.1 + s, v.2)

def HorizontalStep (m : ℕ) (x y : Vertex) : Prop :=
  y = (x.1 + (m : ℤ) ^ x.2, x.2)

def VerticalStep (x y : Vertex) : Prop := y = (x.1, x.2 + 1)

def graph (m : ℕ) : SimpleGraph Vertex :=
  SimpleGraph.fromRel (fun x y => HorizontalStep m x y ∨ VerticalStep x y)

theorem horizontal_adj {m : ℕ} (hm : 1 ≤ m) {x y : Vertex}
    (h : HorizontalStep m x y) : (graph m).Adj x y := by
  refine ⟨?_, Or.inl (Or.inl h)⟩
  intro heq
  have hpow : 0 < (m : ℤ) ^ x.2 := pow_pos (by exact_mod_cast (show 0 < m by omega)) _
  have hcoord : x.1 = x.1 + (m : ℤ) ^ x.2 := congrArg Prod.fst (heq.trans h)
  omega

theorem vertical_adj {m : ℕ} {x y : Vertex} (h : VerticalStep x y) :
    (graph m).Adj x y := by
  refine ⟨?_, Or.inl (Or.inr h)⟩
  intro heq
  have hcoord : x.2 = x.2 + 1 := congrArg Prod.snd (heq.trans h)
  omega

theorem horizontal_translate {m : ℕ} {x y : Vertex} (s : ℤ)
    (h : HorizontalStep m x y) : HorizontalStep m (translate s x) (translate s y) := by
  rcases x with ⟨r,j⟩
  subst y
  simp only [HorizontalStep, translate]
  congr 1
  ring

theorem vertical_translate {x y : Vertex} (s : ℤ) (h : VerticalStep x y) :
    VerticalStep (translate s x) (translate s y) := by
  rcases x with ⟨r,j⟩
  subst y
  rfl

def carrierVertices (K : ℕ) (A B : ℤ) : Finset Vertex :=
  (Finset.Icc A B) ×ˢ (Finset.range (K + 1))

@[simp] theorem mem_carrierVertices {K : ℕ} {A B : ℤ} {v : Vertex} :
    v ∈ carrierVertices K A B ↔ A ≤ v.1 ∧ v.1 ≤ B ∧ v.2 ≤ K := by
  simp only [carrierVertices, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
  omega

def carrierGraph (m K : ℕ) (A B : ℤ) :
    SimpleGraph {v : Vertex // v ∈ carrierVertices K A B} :=
  (graph m).induce {v | v ∈ carrierVertices K A B}

/-- Literal nesting at a common height. -/
theorem carrierVertices_mono {K : ℕ} {A B C D : ℤ}
    (hAC : A ≤ C) (hDB : D ≤ B) :
    carrierVertices K C D ⊆ carrierVertices K A B := by
  intro v hv
  obtain ⟨hC,hD,hK⟩ := mem_carrierVertices.mp hv
  exact mem_carrierVertices.mpr ⟨hAC.trans hC,hD.trans hDB,hK⟩

/-- Literal covariance of vertices under the `a`-translations. -/
theorem translate_mem_carrierVertices {K : ℕ} {A B : ℤ} (s : ℤ) (v : Vertex) :
    translate s v ∈ carrierVertices K (A+s) (B+s) ↔ v ∈ carrierVertices K A B := by
  simp only [mem_carrierVertices, translate]
  omega

def carrierTranslation (m K : ℕ) (A B s : ℤ) :
    carrierGraph m K A B ≃g carrierGraph m K (A+s) (B+s) where
  toFun v := ⟨translate s v, (translate_mem_carrierVertices s v).mpr v.property⟩
  invFun v := ⟨translate (-s) v, by
    have hv := (translate_mem_carrierVertices (-s) v).mpr v.property
    simpa using hv⟩
  left_inv v := by apply Subtype.ext; simp [translate]
  right_inv v := by apply Subtype.ext; simp [translate]
  map_rel_iff' := by
    intro x y
    change (graph m).Adj (translate s x.val) (translate s y.val) ↔ (graph m).Adj x.val y.val
    constructor
    · intro h
      obtain ⟨hne,hrel | hrel⟩ := h
      · refine ⟨?_,Or.inl ?_⟩
        · intro he; apply hne; rw [he]
        · obtain hhor | hver := hrel
          · left
            have h := horizontal_translate (-s) hhor
            simpa [translate] using h
          · right
            have h := vertical_translate (-s) hver
            simpa [translate] using h
      · refine ⟨?_,Or.inr ?_⟩
        · intro he; apply hne; rw [he]
        · obtain hhor | hver := hrel
          · left
            have h := horizontal_translate (-s) hhor
            simpa [translate] using h
          · right
            have h := vertical_translate (-s) hver
            simpa [translate] using h
    · intro h
      obtain ⟨hne,hrel | hrel⟩ := h
      · refine ⟨?_,Or.inl ?_⟩
        · intro he
          apply hne
          have h := congrArg (translate (-s)) he
          simpa [translate] using h
        · exact hrel.imp (horizontal_translate s) (vertical_translate s)
      · refine ⟨?_,Or.inr ?_⟩
        · intro he
          apply hne
          have h := congrArg (translate (-s)) he
          simpa [translate] using h
        · exact hrel.imp (horizontal_translate s) (vertical_translate s)

/-- Lower vertices of a relation polygon. -/
def lowerVertex (m : ℕ) (r : ℤ) (j n : ℕ) : Vertex :=
  (r + n * (m : ℤ)^j, j)

theorem lowerVertex_step (m : ℕ) (r : ℤ) (j n : ℕ) :
    HorizontalStep m (lowerVertex m r j n) (lowerVertex m r j (n+1)) := by
  simp only [HorizontalStep, lowerVertex, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

/-- The right-hand vertical side of the actual relation polygon. -/
theorem lowerVertex_upper (m : ℕ) (r : ℤ) (j : ℕ) :
    VerticalStep (lowerVertex m r j m) (r+(m : ℤ)^(j+1),j+1) := by
  simp only [VerticalStep, lowerVertex, pow_succ]
  congr 1
  ring

theorem upperVertex_step (m : ℕ) (r : ℤ) (j : ℕ) :
    HorizontalStep m (r,j+1) (r+(m : ℤ)^(j+1),j+1) := rfl

/-- Finitely many actual relation polygons in a common-height carrier. -/
def carrierCells (m K : ℕ) (A B : ℤ) : Finset Vertex :=
  (carrierVertices K A B).filter (fun v => v.2 < K ∧ v.1+(m : ℤ)^(v.2+1) ≤ B)

theorem carrierCells_mono {m K : ℕ} {A B C D : ℤ}
    (hAC : A ≤ C) (hDB : D ≤ B) :
    carrierCells m K C D ⊆ carrierCells m K A B := by
  intro v hv
  obtain ⟨hvert,hj,hr⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨carrierVertices_mono hAC hDB hvert,hj,hr.trans hDB⟩

/-- All `m+1` lower vertices lie in the finite carrier, with no
assumption about a chosen subdivision or contraction. -/
theorem lowerVertex_mem_of_cell {m K : ℕ} {A B r : ℤ} {j n : ℕ}
    (hcell : (r,j) ∈ carrierCells m K A B) (hn : n ≤ m) :
    lowerVertex m r j n ∈ carrierVertices K A B := by
  obtain ⟨hvert,hj,hr⟩ := Finset.mem_filter.mp hcell
  change r + (m : ℤ)^(j+1) ≤ B at hr
  obtain ⟨hA,hB,hK⟩ := mem_carrierVertices.mp hvert
  have hnonneg : 0 ≤ (m : ℤ)^j := pow_nonneg (by positivity) _
  have hnm : (n : ℤ) ≤ m := by exact_mod_cast hn
  have hprod : (n : ℤ)*(m : ℤ)^j ≤ (m : ℤ)^(j+1) := by
    calc
      _ ≤ (m : ℤ)*(m : ℤ)^j := mul_le_mul_of_nonneg_right hnm hnonneg
      _ = _ := by rw [pow_succ]; ring
  apply mem_carrierVertices.mpr
  simp only [lowerVertex]
  refine ⟨?_,?_,hK⟩
  · have : 0 ≤ (n : ℤ)*(m : ℤ)^j := mul_nonneg (by positivity) hnonneg
    omega
  · omega

end AbelianTargets.IntervalCarriers

