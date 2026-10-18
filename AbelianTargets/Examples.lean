import AbelianTargets.ReducedWalks

/-!
# A concrete odd involution in the complete graph on four vertices

The example uses actual graph walks and the generated reduced homotopy
relation. Every adjacency and every homotopy move is checked by Lean.
-/

namespace AbelianTargets

/-- The four-vertex complete simple graph from the paper's introduction. -/
abbrev K4 : SimpleGraph (Fin 4) := SimpleGraph.completeGraph (Fin 4)

/-- The odd triangle `(0,1,2,0)`. -/
def k4Triangle : K4.Walk 0 0 :=
  .cons (v := 1) (by decide) (.cons (v := 2) (by decide) (.cons (by decide) .nil))

@[simp] theorem k4Triangle_length : k4Triangle.length = 3 := rfl

/-- Two copies of the triangle cancel in the reduced homotopy relation.

The explicit sequence is
`0120120 → 0123120 → 0103120 → 03120 → 0`.
Its two initial steps replace a middle vertex of a two-edge segment;
the remaining steps delete a spur and a closed four-walk.
-/
theorem k4Triangle_square_null :
    ReducedHomotopic K4 (loopPower K4 k4Triangle 2) .nil := by
  let p02 : K4.Walk 0 2 := .cons (v := 1) (by decide) (.cons (by decide) .nil)
  let p21via0 : K4.Walk 2 1 := .cons (v := 0) (by decide) (.cons (by decide) .nil)
  let p21via3 : K4.Walk 2 1 := .cons (v := 3) (by decide) (.cons (by decide) .nil)
  let p10 : K4.Walk 1 0 := .cons (v := 2) (by decide) (.cons (by decide) .nil)
  let p01 : K4.Walk 0 1 := .cons (by decide) .nil
  let p13via2 : K4.Walk 1 3 := .cons (v := 2) (by decide) (.cons (by decide) .nil)
  let p13via0 : K4.Walk 1 3 := .cons (v := 0) (by decide) (.cons (by decide) .nil)
  let p30 : K4.Walk 3 0 :=
    .cons (v := 1) (by decide) (.cons (v := 2) (by decide) (.cons (by decide) .nil))
  let w1 : K4.Walk 0 0 := p02.append (p21via3.append p10)
  let w2 : K4.Walk 0 0 := p01.append (p13via0.append p30)
  let w3 : K4.Walk 0 0 := .cons (by decide) p30
  have h1 : ReducedHomotopic K4 (loopPower K4 k4Triangle 2) w1 := by
    have h := ReducedHomotopic.append (ReducedHomotopic.refl p02)
      (ReducedHomotopic.append
        (ReducedHomotopic.two_step p21via0 p21via3 rfl rfl)
        (ReducedHomotopic.refl p10))
    simpa only [loopPower_succ, loopPower_zero, SimpleGraph.Walk.append_nil,
      k4Triangle, p02, p21via0, p21via3, p10, w1,
      SimpleGraph.Walk.cons_append, SimpleGraph.Walk.nil_append] using h
  have h2 : ReducedHomotopic K4 w1 w2 := by
    have h := ReducedHomotopic.append (ReducedHomotopic.refl p01)
      (ReducedHomotopic.append
        (ReducedHomotopic.two_step p13via2 p13via0 rfl rfl)
        (ReducedHomotopic.refl p30))
    exact h
  have h3 : ReducedHomotopic K4 w2 w3 := by
    have h := ReducedHomotopic.append
      (ReducedHomotopic.spur (by decide : K4.Adj (0 : Fin 4) 1))
      (ReducedHomotopic.refl w3)
    exact h
  have h4 : ReducedHomotopic K4 w3 .nil := .four _ rfl
  exact h1.trans (h2.trans (h3.trans h4))

/-- `K₄` satisfies the exact hypothesis of Theorem 1.4. -/
theorem k4_hasOddInvolution : HasOddInvolution K4 :=
  ⟨0, k4Triangle, by decide, k4Triangle_square_null⟩

/-- The same witness satisfies the hypothesis of Proposition 7.1. -/
theorem k4_hasOddTorsion : HasOddTorsion K4 := k4_hasOddInvolution.hasOddTorsion

/-- The odd triangle is a nonidentity element of the actual reduced group. -/
theorem k4Triangle_class_ne_one :
    ReducedFundamentalGroup.ofWalk K4 0 k4Triangle ≠ 1 := by
  intro h
  exact odd_not_reduced_null (by decide : Odd k4Triangle.length)
    ((ReducedFundamentalGroup.ofWalk_eq_one_iff _).mp h)

/-- Its square is the group identity. -/
theorem k4Triangle_class_square :
    (ReducedFundamentalGroup.ofWalk K4 0 k4Triangle) ^ 2 = 1 := by
  rw [← ReducedFundamentalGroup.ofWalk_loopPower]
  exact (ReducedFundamentalGroup.ofWalk_eq_one_iff _).mpr k4Triangle_square_null

end AbelianTargets
