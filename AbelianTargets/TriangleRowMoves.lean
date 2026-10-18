import AbelianTargets.CarrierTriangulation

/-! # Bounded elementary row moves and polygon fan contraction -/

namespace AbelianTargets

inductive BoundedTriangleRows {V : Type*} [DecidableEq V]
    (Face : Finset V → Prop) (B : ℕ) : List V → List V → Prop
  | refl (w) (hlen : w.length ≤ B) : BoundedTriangleRows Face B w w
  | triangle (a b c : V) (hface : Face {a,b,c}) (p s : List V)
      (hw : (p++[a,b,c]++s).length ≤ B) (hz : (p++[a,c]++s).length ≤ B) :
      BoundedTriangleRows Face B (p++[a,b,c]++s) (p++[a,c]++s)
  | pause (a : V) (p s : List V)
      (hw : (p++[a,a]++s).length ≤ B) (hz : (p++[a]++s).length ≤ B) :
      BoundedTriangleRows Face B (p++[a,a]++s) (p++[a]++s)
  | symm {w z} : BoundedTriangleRows Face B w z → BoundedTriangleRows Face B z w
  | trans {u v w} : BoundedTriangleRows Face B u v → BoundedTriangleRows Face B v w →
      BoundedTriangleRows Face B u w

theorem BoundedTriangleRows.mono {V : Type*} [DecidableEq V] {Face : Finset V → Prop}
    {B C : ℕ} {w z : List V} (h : BoundedTriangleRows Face B w z) (hBC : B ≤ C) :
    BoundedTriangleRows Face C w z := by
  induction h with
  | refl w hl => exact .refl w (hl.trans hBC)
  | triangle a b c hf p s hw hz => exact .triangle a b c hf p s (hw.trans hBC) (hz.trans hBC)
  | pause a p s hw hz => exact .pause a p s (hw.trans hBC) (hz.trans hBC)
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem BoundedTriangleRows.context {V : Type*} [DecidableEq V] {Face : Finset V → Prop}
    {B : ℕ} {w z : List V} (h : BoundedTriangleRows Face B w z) (p s : List V) :
    BoundedTriangleRows Face (B+p.length+s.length) (p++w++s) (p++z++s) := by
  induction h with
  | refl w hl => exact .refl _ (by simp only [List.length_append]; omega)
  | triangle a b c hf p₀ s₀ hw hz =>
      have h' := BoundedTriangleRows.triangle (B := B+p.length+s.length) a b c hf
        (p++p₀) (s₀++s)
        (by simp only [List.length_append] at hw ⊢; omega)
        (by simp only [List.length_append] at hz ⊢; omega)
      simpa only [List.append_assoc] using h'
  | pause a p₀ s₀ hw hz =>
      have h' := BoundedTriangleRows.pause (Face := Face) (B := B+p.length+s.length) a
        (p++p₀) (s₀++s)
        (by simp only [List.length_append] at hw ⊢; omega)
        (by simp only [List.length_append] at hz ⊢; omega)
      simpa only [List.append_assoc] using h'
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

inductive FanChain {V : Type*} [DecidableEq V] (Face : Finset V → Prop) (u : V) :
    List V → V → Prop
  | single (v) : FanChain Face u [v] v
  | cons {v w rest last} (hf : Face {u,v,w}) (h : FanChain Face u (w::rest) last) :
      FanChain Face u (v::w::rest) last

/-- Successive triangle collapses contract the edge row of a polygon
fan to its last radial edge, and never increase the row length. -/
theorem FanChain.contract {V : Type*} [DecidableEq V] {Face : Finset V → Prop}
    {u last : V} {vs : List V} (h : FanChain Face u vs last) {B : ℕ}
    (hlen : (u::vs).length ≤ B) : BoundedTriangleRows Face B (u::vs) [u,last] := by
  induction h with
  | single v => exact .refl _ hlen
  | @cons v w rest last hf h ih =>
      have hstep : BoundedTriangleRows Face B (u::v::w::rest) (u::w::rest) := by
        simpa only [List.nil_append,List.cons_append,List.append_nil] using
          BoundedTriangleRows.triangle u v w hf [] rest
            (by simpa only [List.nil_append,List.cons_append,List.append_nil] using hlen)
            (by simp only [List.length_append,List.length_cons,List.length_nil] at hlen ⊢; omega)
      exact hstep.trans (ih (by simp only [List.length_cons] at hlen ⊢; omega))

end AbelianTargets
