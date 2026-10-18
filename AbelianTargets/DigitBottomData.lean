import AbelianTargets.AppendedSpliceData
import AbelianTargets.BottomIntervalMap

/-! Actual compressed digit paths supply every moving-endpoint splice datum. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

def bottomWordPath (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n ≤ R) :
    WordPath m (0,0) (compressedWord m hm n) ((n : ℤ),0) :=
  Classical.choose ((compressedWord_positive m hm n).mono
    (Nat.log_mono_right hn) |>.exists_carrier_path hn)

theorem bottomWordPath_mem (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n ≤ R) :
    ∀ v ∈ (bottomWordPath m hm R n hn).vertices, v ∈ carrierVertices (Nat.log m R) 0 R :=
  Classical.choose_spec ((compressedWord_positive m hm n).mono
    (Nat.log_mono_right hn) |>.exists_carrier_path hn)

def bottomAStep (m n : ℕ) : WordPath m ((n : ℤ),0) [BSLetter.a] (((n+1 : ℕ) : ℤ),0) :=
  .cons (by simp [LetterStep,HorizontalStep,Nat.cast_add]) (.nil _)

def bottomRow (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n ≤ R) :
    ℕ → (CarrierVertex (Nat.log m R) 0 R → ℝ) :=
  FixedSlots.listRow (vertexMass (carrierBase (Nat.log m R) R)) ((n : ℤ),0)
    (bottomWordPath m hm R n hn).vertices

theorem bottomRow_terminal (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n ≤ R)
    (j : ℕ) (hj : (compressedWord m hm n).length ≤ j) :
    bottomRow m hm R n hn j = bottomMass (Nat.log m R) R n := by
  unfold bottomRow FixedSlots.listRow
  rw [list_getD_terminal (bottomWordPath m hm R n hn).vertices_last j (by
    rw [WordPath.vertices_length]
    omega)]
  rfl

theorem exists_bottomSpliceData (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n < R) :
    ∃ D : FixedSlots.BottomSpliceData (carryRowBudget m R)
      (bottomMass (Nat.log m R) R 0) (bottomMass (Nat.log m R) R n)
      (bottomMass (Nat.log m R) R (n+1))
      (ambientRealization m (Nat.log m R) 0 R) 1,
      D.leftRow = bottomRow m hm R n (by omega) ∧
      D.carryTarget.vertices = bottomRow m hm R (n+1) (by omega) := by
  let B := carryRowBudget m R
  let ι := vertexMass (carrierBase (Nat.log m R) R)
  let pn := bottomWordPath m hm R n (show n ≤ R by omega)
  let q := bottomWordPath m hm R (n+1) (show n+1 ≤ R by omega)
  let p := pn.append (bottomAStep m n)
  obtain ⟨p₀,q₀,hp₀,hq₀,hrows⟩ := exists_bounded_carrier_carry_rows m hm R n hn
  have hpv : p₀.vertices = p.vertices := p₀.vertices_eq p
  have hqv : q₀.vertices = q.vertices := q₀.vertices_eq q
  rw [hpv,hqv] at hrows
  have hp : ∀ v ∈ p.vertices, v ∈ carrierVertices (Nat.log m R) 0 R := by
    simpa only [hpv] using hp₀
  have hq : ∀ v ∈ q.vertices, v ∈ carrierVertices (Nat.log m R) 0 R := by
    simpa only [hqv] using hq₀
  have hverts : p.vertices = pn.vertices++[(((n+1 : ℕ) : ℤ),0)] := by
    simp only [p,WordPath.vertices_append_tail,bottomAStep,WordPath.vertices,List.tail_cons]
  have hl := hrows.length_bounds
  let U := FixedSlots.canonicalRow ι B (0,0) (((n+1 : ℕ) : ℤ),0)
    (padRow (B+2) (((n+1 : ℕ) : ℤ),0) p.vertices) (padRow_head p.vertices_head _)
    (padRow_last p.vertices_last _) (padRow_length (hl.1.trans (by dsimp [B,carryRowBudget]; omega)))
  let T := FixedSlots.canonicalRow ι B (0,0) (((n+1 : ℕ) : ℤ),0)
    (padRow (B+2) (((n+1 : ℕ) : ℤ),0) q.vertices) (padRow_head q.vertices_head _)
    (padRow_last q.vertices_last _) (padRow_length (hl.2.trans (by dsimp [B,carryRowBudget]; omega)))
  obtain ⟨F,hFS,hFL,hFJ⟩ := FixedSlots.boundedTriangleRows_realize_joint ι
    (carrierFace_charts _) (C := 1) (fun a b => Probability.dist_le_one _ _) hrows
    (0,0) (((n+1 : ℕ) : ℤ),0) p.vertices_head p.vertices_last (p.validRow (by omega) hp)
  have hU : U.vertices = FixedSlots.listRow ι (((n+1 : ℕ) : ℤ),0)
      (pn.vertices++[(((n+1 : ℕ) : ℤ),0)]) := by
    funext j
    change ι ((padRow (B+2) (((n+1 : ℕ) : ℤ),0) p.vertices).getD j (((n+1 : ℕ) : ℤ),0)) = _
    rw [padRow_getD,hverts]
    rfl
  have hface : CarrierFace m (Nat.log m R) 0 R {((n : ℤ),0),(((n+1 : ℕ) : ℤ),0)} := by
    exact Or.inr (Or.inl ⟨_,(bottomVertex _ R n (by omega)).property,
      _,(bottomVertex _ R (n+1) (by omega)).property,
      (show LetterStep m BSLetter.a ((n : ℤ),0) (((n+1 : ℕ) : ℤ),0) from by
        simp [LetterStep,HorizontalStep,Nat.cast_add]).adj (by omega),Finset.Subset.refl _⟩)
  have hlen : pn.vertices.length ≤ B+1 := by
    rw [WordPath.vertices_length]
    have hh := compressedWord_interval_uniform_length m hm R n (show n ≤ R by omega)
    dsimp [B,carryRowBudget]
    omega
  let D := FixedSlots.appendedSpliceData ι (carrierFace_charts _) (C := 1)
    (fun a b => Probability.dist_le_one _ _) B (0,0) ((n : ℤ),0) (((n+1 : ℕ) : ℤ),0)
    pn.vertices pn.vertices_head pn.vertices_last (pn.validRow (by omega)
      (bottomWordPath_mem m hm R n (by omega))) hface hlen U T hU F hFS
    (by simpa only [one_mul] using hFL) hFJ
  refine ⟨D,rfl,?_⟩
  funext j
  change ι ((padRow (B+2) (((n+1 : ℕ) : ℤ),0) q.vertices).getD j (((n+1 : ℕ) : ℤ),0)) = _
  rw [padRow_getD]
  rfl

end
end AbelianTargets.IntervalCarriers

