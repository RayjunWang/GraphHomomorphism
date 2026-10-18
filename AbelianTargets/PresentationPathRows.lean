import AbelianTargets.CarrierFanMoves

/-! # Edge-labelled sides of the actual presentation polygon -/

namespace AbelianTargets.IntervalCarriers

theorem lowerVertex_comp (m : ℕ) (c : Vertex) (l n : ℕ) :
    lowerVertex m (lowerVertex m c.1 c.2 l).1 (lowerVertex m c.1 c.2 l).2 n =
      lowerVertex m c.1 c.2 (l+n) := by
  simp only [lowerVertex,Nat.cast_add]
  congr 1
  ring

theorem lowerRow_shift (m : ℕ) (c : Vertex) (l n k : ℕ) :
    lowerRow m (lowerVertex m c.1 c.2 l) n k = lowerRow m c (l+n) k := by
  induction k generalizing n with
  | zero => simp only [lowerRow,lowerVertex_comp]
  | succ k ih =>
      simp only [lowerRow,lowerVertex_comp,ih,Nat.add_assoc]

theorem WordPath.aWord_vertices {m n : ℕ} {c z : Vertex}
    (p : WordPath m c (aWord n) z) : p.vertices = lowerRow m c 0 n := by
  induction n generalizing c with
  | zero => cases p; cases z; simp [WordPath.vertices,lowerRow,lowerVertex]
  | succ n ih =>
      have hword : aWord (n+1) = BSLetter.a :: aWord n := by
        simp only [aWord,List.replicate_succ]
      let p' := p.castWord hword
      have hp : p'.vertices = p.vertices := p.vertices_castWord hword
      rw [← hp]
      cases p' with
      | @cons s c y z w h q =>
        have hy : y = lowerVertex m c.1 c.2 1 := by
          simpa only [LetterStep,HorizontalStep,lowerVertex,Nat.cast_one,one_mul] using h
        have hq := ih q
        simp only [WordPath.vertices,hq,hy,lowerRow_shift,zero_add,lowerRow]
        have hc : lowerVertex m c.1 c.2 0 = c := by cases c; simp [lowerVertex]
        rw [hc]

theorem WordPath.relation_endpoint {m : ℕ} {c z : Vertex}
    (p : WordPath m c [BSLetter.t,BSLetter.a,BSLetter.tInv] z) :
    z = lowerVertex m c.1 c.2 m := by
  cases p with
  | cons ht p =>
    cases p with
    | cons ha p =>
      cases p with
      | cons hd p =>
        cases p
        have ht' := ht
        have ha' := ha
        have hd' := hd
        simp only [LetterStep,VerticalStep,HorizontalStep] at ht' ha' hd'
        rw [ht'] at ha'
        rw [ha'] at hd'
        have hx := congrArg Prod.fst hd'
        have hj := congrArg Prod.snd hd'
        apply Prod.ext
        · simp only [lowerVertex,pow_succ] at hx ⊢
          simpa only [mul_comm] using hx.symm
        · simp only [lowerVertex] at hj ⊢
          omega

theorem WordPath.relation_vertices {m : ℕ} {c z : Vertex}
    (p : WordPath m c [BSLetter.t,BSLetter.a,BSLetter.tInv] z) :
    p.vertices = [lowerVertex m c.1 c.2 0,upperLeft c.1 c.2,
      upperRight m c.1 c.2,lowerVertex m c.1 c.2 m] := by
  have hz := p.relation_endpoint
  cases p with
  | cons ht p =>
    cases p with
    | cons ha p =>
      cases p with
      | cons hd p =>
        cases p
        simp only [LetterStep,VerticalStep,HorizontalStep] at ht ha
        rw [ht] at ha
        simp only [WordPath.vertices,ht,ha,hz]
        have hc : lowerVertex m c.1 c.2 0 = c := by cases c; simp [lowerVertex]
        rw [hc]
        rfl

/-- Exact labelled relation sides inherit the bounded fan row
homotopy, including their literal vertex lists. -/
theorem presentation_path_rows {m K : ℕ} {A B : ℤ} {c z z' : Vertex}
    (hm : 2 ≤ m) (hc : c ∈ carrierCells m K A B)
    (p : WordPath m c [BSLetter.t,BSLetter.a,BSLetter.tInv] z)
    (q : WordPath m c (aWord m) z') :
    BoundedTriangleRows (CarrierFace m K A B) (m+2) q.vertices p.vertices := by
  rw [q.aWord_vertices,p.relation_vertices]
  exact presentation_polygon_rows hm hc

/-- Every actual two-edge backtrack contracts through its edge face
and one pause deletion, using at most three vertex entries. -/
theorem WordPath.two_edge_spur_rows {m K : ℕ} {A B : ℤ} {c : Vertex} {s t : BSLetter}
    (hm : 1 ≤ m) (p : WordPath m c [s,t] c)
    (hvertices : ∀ v ∈ p.vertices, v ∈ carrierVertices K A B) :
    BoundedTriangleRows (CarrierFace m K A B) 3 p.vertices [c] := by
  cases p with
  | @cons s c y c w h p =>
    cases p with
    | cons h' p =>
      cases p
      have hc : c ∈ carrierVertices K A B := hvertices c (by simp [WordPath.vertices])
      have hy : y ∈ carrierVertices K A B := hvertices y (by simp [WordPath.vertices])
      have hf : CarrierFace m K A B {c,y,c} := by
        apply Or.inr
        apply Or.inl
        refine ⟨c,hc,y,hy,h.adj hm,?_⟩
        intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
        obtain rfl | rfl | rfl := hv
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inl rfl
      have h₁ : BoundedTriangleRows (CarrierFace m K A B) 3 [c,y,c] [c,c] := by
        simpa only [List.nil_append,List.append_nil] using
          BoundedTriangleRows.triangle c y c hf [] [] (by simp) (by simp)
      have h₂ : BoundedTriangleRows (CarrierFace m K A B) 3 [c,c] [c] := by
        simpa only [List.nil_append,List.append_nil] using
          BoundedTriangleRows.pause (Face := CarrierFace m K A B) c [] [] (by simp) (by simp)
      exact h₁.trans h₂

end AbelianTargets.IntervalCarriers
