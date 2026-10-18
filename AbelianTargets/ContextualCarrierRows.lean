import AbelianTargets.PresentationPathRows
import AbelianTargets.WordPathHelpers

/-! # Literal path contexts preserve the bounded fan row homotopies -/

namespace AbelianTargets.IntervalCarriers

theorem LetterStep.source_unique {m : ℕ} {s : BSLetter} {x y z : Vertex}
    (h : LetterStep m s x y) (h' : LetterStep m s z y) : x = z := by
  cases s with
  | a =>
      have hx₁ := congrArg Prod.fst h
      have hx₂ := congrArg Prod.snd h
      have hz₁ := congrArg Prod.fst h'
      have hz₂ := congrArg Prod.snd h'
      dsimp [LetterStep,HorizontalStep] at *
      have hj : x.2 = z.2 := by omega
      apply Prod.ext
      · rw [hj] at hx₁
        omega
      · exact hj
  | t =>
      have hx₁ := congrArg Prod.fst h
      have hx₂ := congrArg Prod.snd h
      have hz₁ := congrArg Prod.fst h'
      have hz₂ := congrArg Prod.snd h'
      apply Prod.ext <;> dsimp [LetterStep,VerticalStep] at * <;> omega
  | tInv => exact h.trans h'.symm

theorem WordPath.startpoint_eq {m : ℕ} {x y z : Vertex} {w : List BSLetter}
    (p : WordPath m x w z) (q : WordPath m y w z) : x = y := by
  induction p generalizing y with
  | nil x => cases q; rfl
  | @cons s x a z w h p ih =>
      cases q with
      | @cons s' y b z w' h' q =>
        have hab := ih q
        subst b
        exact h.source_unique h'

theorem WordPath.vertices_append_tail {m : ℕ} {x y z : Vertex}
    {w u : List BSLetter} (p : WordPath m x w y) (q : WordPath m y u z) :
    (p.append q).vertices = p.vertices ++ q.vertices.tail := by
  induction p with
  | nil x => cases q <;> rfl
  | cons h p ih => simp only [WordPath.append,WordPath.vertices,ih,List.cons_append]

theorem WordPath.dropLast_vertices_length {m : ℕ} {x y : Vertex}
    {w : List BSLetter} (p : WordPath m x w y) : p.vertices.dropLast.length = w.length := by
  rw [List.length_dropLast,p.vertices_length]
  omega

theorem WordPath.tail_vertices_length {m : ℕ} {x y : Vertex}
    {w : List BSLetter} (p : WordPath m x w y) : p.vertices.tail.length = w.length := by
  rw [List.length_tail,p.vertices_length]
  omega

theorem WordPath.parts {m : ℕ} {x z : Vertex} (a w b : List BSLetter)
    (p : WordPath m x (a++w++b) z) :
    ∃ (c d : Vertex) (u : WordPath m x a c) (v : WordPath m c w d)
      (s : WordPath m d b z), p.vertices = ((u.append v).append s).vertices := by
  let p' := p.castWord (List.append_assoc a w b)
  obtain ⟨c,u,t,_⟩ := p'.split a (w++b)
  obtain ⟨d,v,s,_⟩ := t.split w b
  exact ⟨c,d,u,v,s,p.vertices_eq ((u.append v).append s)⟩

theorem WordPath.local_vertices_of_parts {m : ℕ} {x c d z : Vertex}
    {a w b : List BSLetter} (p : WordPath m x a c) (v : WordPath m c w d)
    (s : WordPath m d b z) {t : Vertex} (ht : t ∈ v.vertices) :
    t ∈ ((p.append v).append s).vertices := by
  rw [WordPath.mem_vertices_append,WordPath.mem_vertices_append]
  exact Or.inl (Or.inr ht)

/-- Row homotopies can be inserted into the exact edge-labelled path
context. The context adds precisely its number of edges to the budget. -/
theorem WordPath.triangleRows_context {m : ℕ} {Face : Finset Vertex → Prop}
    {B : ℕ} {x a b z : Vertex} {pw w u sw : List BSLetter}
    (p : WordPath m x pw a) (q : WordPath m b sw z)
    (v : WordPath m a w b) (v' : WordPath m a u b)
    (h : BoundedTriangleRows Face B v.vertices v'.vertices) :
    BoundedTriangleRows Face (B+pw.length+sw.length)
      ((p.append v).append q).vertices ((p.append v').append q).vertices := by
  have h' := h.context p.vertices.dropLast q.vertices.tail
  rw [p.dropLast_vertices_length,q.tail_vertices_length] at h'
  rw [WordPath.vertices_append_tail (p.append v) q,
    WordPath.vertices_append_tail (p.append v') q,
    WordPath.vertices_append p v,WordPath.vertices_append p v']
  simpa only [List.append_assoc] using h'

/-- A presentation polygon move in an arbitrary actual path context
still has a concrete bounded triangle-row certificate. -/
theorem contextual_presentation_path_rows {m K : ℕ} {A B : ℤ}
    {x c b z : Vertex} {pw sw : List BSLetter}
    (hm : 2 ≤ m) (hc : c ∈ carrierCells m K A B)
    (p : WordPath m x pw c) (q : WordPath m b sw z)
    (v : WordPath m c [BSLetter.t,BSLetter.a,BSLetter.tInv] b)
    (v' : WordPath m c (aWord m) b) :
    BoundedTriangleRows (CarrierFace m K A B) (m+2+pw.length+sw.length)
      ((p.append v').append q).vertices ((p.append v).append q).vertices :=
  p.triangleRows_context q v' v (presentation_path_rows hm hc v v')

theorem relation_start_cell_of_carrier_path {m K : ℕ} {A B : ℤ} {c z : Vertex}
    (p : WordPath m c [BSLetter.t,BSLetter.a,BSLetter.tInv] z)
    (hvertices : ∀ v ∈ p.vertices, v ∈ carrierVertices K A B) :
    c ∈ carrierCells m K A B := by
  cases p with
  | @cons s c c₁ z w ht p =>
    cases p with
    | @cons s' c₁ c₂ z w' ha p =>
      have hc : c ∈ carrierVertices K A B := hvertices c (by simp [WordPath.vertices])
      have hc₁ : c₁ ∈ carrierVertices K A B := hvertices c₁ (by simp [WordPath.vertices])
      have hc₂ : c₂ ∈ carrierVertices K A B := hvertices c₂ (by
        simp only [WordPath.vertices,List.mem_cons]
        exact Or.inr (Or.inr p.start_mem_vertices))
      have hstep₁ : c₁ = (c.1,c.2+1) := ht
      have hstep₂ : c₂ = (c₁.1+(m:ℤ)^c₁.2,c₁.2) := ha
      obtain ⟨_,_,hj⟩ := mem_carrierVertices.mp hc₁
      obtain ⟨_,hr,_⟩ := mem_carrierVertices.mp hc₂
      refine Finset.mem_filter.mpr ⟨hc,?_,?_⟩
      · rw [hstep₁] at hj
        simp only at hj
        omega
      · simpa only [hstep₂,hstep₁] using hr

end AbelianTargets.IntervalCarriers

namespace AbelianTargets

open IntervalCarriers

/-- Every primitive presentation or backtrack move is realized by
triangle and pause moves of actual finite-carrier vertex rows. -/
theorem BSCellMove.local_carrier_rows {m K : ℕ} {A B : ℤ} {w u : List BSLetter}
    (hm : 2 ≤ m) (h : BSCellMove m w u) {c d : Vertex}
    (p : WordPath m c w d) (q : WordPath m c u d)
    (hp : ∀ v ∈ p.vertices, v ∈ carrierVertices K A B)
    (hq : ∀ v ∈ q.vertices, v ∈ carrierVertices K A B) :
    BoundedTriangleRows (CarrierFace m K A B) (m+2) p.vertices q.vertices := by
  induction h with
  | relation =>
      exact (presentation_path_rows hm (relation_start_cell_of_carrier_path p hp) p q).symm
  | cancelDownUp =>
      cases q
      exact (p.two_edge_spur_rows (by omega) hp).mono (by omega)
  | cancelUpDown =>
      cases q
      exact (p.two_edge_spur_rows (by omega) hp).mono (by omega)
  | symm h ih => exact (ih q p hq hp).symm

theorem BSCellMove.context_carrier_rows {m K : ℕ} {A B : ℤ} {w u : List BSLetter}
    (hm : 2 ≤ m) (h : BSCellMove m w u) (a b : List BSLetter) {x z : Vertex}
    (p : WordPath m x (a++w++b) z) (q : WordPath m x (a++u++b) z)
    (hp : ∀ v ∈ p.vertices, v ∈ carrierVertices K A B)
    (hq : ∀ v ∈ q.vertices, v ∈ carrierVertices K A B) :
    BoundedTriangleRows (CarrierFace m K A B) (m+2+a.length+b.length) p.vertices q.vertices := by
  obtain ⟨c,d,pre,v,s,heq⟩ := p.parts a w b
  obtain ⟨c',d',pre',v',s',heq'⟩ := q.parts a u b
  have hc : c = c' := pre.endpoint_eq pre'
  have hd : d = d' := s.startpoint_eq s'
  subst c'
  subst d'
  have hv : ∀ t ∈ v.vertices, t ∈ carrierVertices K A B := by
    intro t ht
    apply hp
    rw [heq]
    exact pre.local_vertices_of_parts v s ht
  have hv' : ∀ t ∈ v'.vertices, t ∈ carrierVertices K A B := by
    intro t ht
    apply hq
    rw [heq']
    exact pre'.local_vertices_of_parts v' s' ht
  have hlocal := h.local_carrier_rows hm v v' hv hv'
  have hglobal := pre.triangleRows_context s v v' hlocal
  rw [heq,heq']
  have hpref := pre.vertices_eq pre'
  have hsuff := s.vertices_eq s'
  rw [WordPath.vertices_append_tail (pre'.append v') s',WordPath.vertices_append pre' v',
    ← hpref,← hsuff]
  rw [WordPath.vertices_append_tail (pre.append v) s,WordPath.vertices_append pre v,
    WordPath.vertices_append_tail (pre.append v') s,WordPath.vertices_append pre v'] at hglobal
  rw [WordPath.vertices_append_tail (pre.append v) s,WordPath.vertices_append pre v]
  exact hglobal

/-- The whole digital certificate realizes as a bounded sequence of
actual carrier fan triangle and pause moves. The length budget remains
logarithmic; the extra additive constant depends only on the base. -/
theorem SafeBSHomotopic.triangle_carrier_rows {m B K n R : ℕ} {w u : List BSLetter}
    (hm : 2 ≤ m) (h : SafeBSHomotopic m B K n w u) (hn : n ≤ R) :
    ∀ (p : WordPath m (0,0) w ((n:ℤ),0)) (q : WordPath m (0,0) u ((n:ℤ),0)),
      (∀ v ∈ p.vertices, v ∈ carrierVertices K 0 R) →
      (∀ v ∈ q.vertices, v ∈ carrierVertices K 0 R) →
      BoundedTriangleRows (CarrierFace m K 0 R) (B+m+2) p.vertices q.vertices := by
  induction h with
  | refl w hl hs =>
      intro p q hp hq
      rw [← p.vertices_eq q]
      exact .refl _ (by rw [p.vertices_length]; omega)
  | @cell w u h a b hw hu hsw hsu =>
      intro p q hp hq
      apply (h.context_carrier_rows hm a b p q hp hq).mono
      simp only [List.length_append] at hw
      omega
  | symm h ih =>
      intro p q hp hq
      exact (ih q p hq hp).symm
  | @trans w v u h₁ h₂ ih₁ ih₂ =>
      intro p q hp hq
      obtain ⟨s,hs⟩ := h₁.shapes.2.exists_path 0 0
      let mid : WordPath m (0,0) v ((n:ℤ),0) := s.copy rfl (by simp)
      have hmid : ∀ t ∈ mid.vertices, t ∈ carrierVertices K 0 R := by
        intro t ht
        rw [WordPath.vertices_copy] at ht
        obtain ⟨hlo,hhi,_,hj⟩ := hs t ht
        apply mem_carrierVertices.mpr
        have hnR : (n:ℤ) ≤ R := by exact_mod_cast hn
        simp only [pow_zero,mul_one,zero_add] at hhi hj
        exact ⟨hlo,by omega,hj⟩
      exact (ih₁ p mid hp hmid).trans (ih₂ mid q hmid hq)

theorem PositiveBSWord.exists_carrier_path {m K n R : ℕ} {w : List BSLetter}
    (h : PositiveBSWord m K n w) (hn : n ≤ R) :
    ∃ p : WordPath m (0,0) w ((n:ℤ),0),
      ∀ v ∈ p.vertices, v ∈ carrierVertices K 0 R := by
  obtain ⟨p,hp⟩ := h.exists_path 0 0
  let q : WordPath m (0,0) w ((n:ℤ),0) := p.copy rfl (by simp)
  refine ⟨q,?_⟩
  intro v hv
  rw [WordPath.vertices_copy] at hv
  obtain ⟨hlo,hhi,_,hj⟩ := hp v hv
  have hnR : (n:ℤ) ≤ R := by exact_mod_cast hn
  simp only [pow_zero,mul_one,zero_add] at hhi hj
  exact mem_carrierVertices.mpr ⟨hlo,by omega,hj⟩

/-- The digital carry is an actual bounded cellular row homotopy in
the literal finite carrier. Its common row budget is explicit and
logarithmic, uniformly for every adjacent bottom pair in the interval. -/
theorem exists_bounded_carrier_carry_rows (m : ℕ) (hm : 2 ≤ m) (R n : ℕ)
    (hn : n < R) :
    ∃ (p : WordPath m (0,0) (compressedWord m hm n++[BSLetter.a]) ((n+1:ℕ),0))
      (q : WordPath m (0,0) (compressedWord m hm (n+1)) ((n+1:ℕ),0)),
      (∀ v ∈ p.vertices, v ∈ carrierVertices (Nat.log m R) 0 R) ∧
      (∀ v ∈ q.vertices, v ∈ carrierVertices (Nat.log m R) 0 R) ∧
      BoundedTriangleRows (CarrierFace m (Nat.log m R) 0 R)
        ((m+1)*(Nat.log m R+1)+2*m+5) p.vertices q.vertices := by
  have h := compressedWord_interval_safe_carry m hm R n hn
  obtain ⟨p,hp⟩ := h.shapes.1.exists_carrier_path (show n+1 ≤ R by omega)
  obtain ⟨q,hq⟩ := h.shapes.2.exists_carrier_path (show n+1 ≤ R by omega)
  refine ⟨p,q,hp,hq,?_⟩
  have hrows := h.triangle_carrier_rows hm (show n+1 ≤ R by omega) p q hp hq
  have heq : (m+1)*(Nat.log m R+1)+m+3+m+2 =
      (m+1)*(Nat.log m R+1)+2*m+5 := by omega
  simpa only [heq] using hrows

theorem BoundedTriangleRows.head_eq {V : Type*} [DecidableEq V]
    {Face : Finset V → Prop} {B : ℕ} {w u : List V}
    (h : BoundedTriangleRows Face B w u) : w.head? = u.head? := by
  induction h with
  | refl w hl => rfl
  | triangle a b c hf p s hw hu => cases p <;> rfl
  | pause a p s hw hu => cases p <;> rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem BoundedTriangleRows.last_eq {V : Type*} [DecidableEq V]
    {Face : Finset V → Prop} {B : ℕ} {w u : List V}
    (h : BoundedTriangleRows Face B w u) : w.getLast? = u.getLast? := by
  induction h with
  | refl w hl => rfl
  | triangle a b c hf p s hw hu =>
      cases s <;> simp [List.getLast?_append_cons]
  | pause a p s hw hu =>
      cases s <;> simp [List.getLast?_append_cons]
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

end AbelianTargets
