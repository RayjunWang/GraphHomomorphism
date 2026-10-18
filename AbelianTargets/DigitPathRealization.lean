import AbelianTargets.SafeDigitalCarries

/-! # Literal directed realization of every bounded digital carry row -/

namespace AbelianTargets.IntervalCarriers

open SimpleGraph

def LetterStep (m : ℕ) : BSLetter → Vertex → Vertex → Prop
  | .a, x, y => HorizontalStep m x y
  | .t, x, y => VerticalStep x y
  | .tInv, x, y => VerticalStep y x

theorem LetterStep.adj {m : ℕ} (hm : 1 ≤ m) {s : BSLetter} {x y : Vertex}
    (h : LetterStep m s x y) : (graph m).Adj x y := by
  cases s with
  | a => exact horizontal_adj hm h
  | t => exact vertical_adj h
  | tInv => exact (vertical_adj h).symm

inductive WordPath (m : ℕ) : Vertex → List BSLetter → Vertex → Type
  | nil (x) : WordPath m x [] x
  | cons {s x y z w} (h : LetterStep m s x y) (p : WordPath m y w z) :
      WordPath m x (s::w) z

def WordPath.vertices {m : ℕ} {x z : Vertex} {w : List BSLetter} :
    WordPath m x w z → List Vertex
  | .nil x => [x]
  | @WordPath.cons _ _ x _ _ _ _ p => x :: p.vertices

def WordPath.toWalk {m : ℕ} (hm : 1 ≤ m) {x z : Vertex} {w : List BSLetter} :
    WordPath m x w z → (graph m).Walk x z
  | .nil _ => .nil
  | .cons h p => .cons (h.adj hm) (p.toWalk hm)

@[simp] theorem WordPath.toWalk_length {m : ℕ} (hm : 1 ≤ m)
    {x z : Vertex} {w : List BSLetter} (p : WordPath m x w z) :
    (p.toWalk hm).length = w.length := by
  induction p with
  | nil x => rfl
  | cons h p ih => simpa only [WordPath.toWalk,Walk.length_cons,List.length_cons] using congrArg Nat.succ ih

@[simp] theorem WordPath.toWalk_support {m : ℕ} (hm : 1 ≤ m)
    {x z : Vertex} {w : List BSLetter} (p : WordPath m x w z) :
    (p.toWalk hm).support = p.vertices := by
  induction p with
  | nil x => rfl
  | cons h p ih => simp only [WordPath.toWalk,WordPath.vertices,Walk.support_cons,ih]

def WordPath.append {m : ℕ} {x y z : Vertex} {w u : List BSLetter}
    (p : WordPath m x w y) (q : WordPath m y u z) : WordPath m x (w++u) z :=
  match p with
  | .nil _ => q
  | .cons h p => .cons h (p.append q)

theorem WordPath.mem_vertices_append {m : ℕ} {x y z v : Vertex}
    {w u : List BSLetter} (p : WordPath m x w y) (q : WordPath m y u z) :
    v ∈ (p.append q).vertices ↔ v ∈ p.vertices ∨ v ∈ q.vertices := by
  induction p with
  | nil x =>
      have hx : x ∈ q.vertices := by
        cases q <;> simp [WordPath.vertices]
      simp only [WordPath.append,WordPath.vertices,List.mem_singleton]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact hx
        · exact h
  | cons h p ih =>
      simp only [WordPath.append,WordPath.vertices,List.mem_cons,ih]
      tauto

def WordPath.copy {m : ℕ} {x y z t : Vertex} {w : List BSLetter}
    (p : WordPath m x w z) (hx : x = y) (hz : z = t) : WordPath m y w t := by
  subst y
  subst t
  exact p

@[simp] theorem WordPath.vertices_copy {m : ℕ} {x y z t : Vertex} {w : List BSLetter}
    (p : WordPath m x w z) (hx : x = y) (hz : z = t) :
    (p.copy hx hz).vertices = p.vertices := by cases hx; cases hz; rfl

end AbelianTargets.IntervalCarriers

namespace AbelianTargets

open SimpleGraph IntervalCarriers

/-- The shape certificate produces an actual path with exactly the
displayed edge letters. Every vertex lies between its endpoints and
below its stated maximum height. -/
theorem PositiveBSWord.exists_path {m K n : ℕ} {w : List BSLetter}
    (h : PositiveBSWord m K n w) (r : ℤ) (j : ℕ) :
    ∃ p : WordPath m (r,j) w (r+(n:ℤ)*(m:ℤ)^j,j),
      ∀ v ∈ p.vertices, r ≤ v.1 ∧ v.1 ≤ r+(n:ℤ)*(m:ℤ)^j ∧ j ≤ v.2 ∧ v.2 ≤ j+K := by
  induction h generalizing r j with
  | nil K =>
      refine ⟨(WordPath.nil (m := m) (r,j)).copy rfl (by simp), ?_⟩
      intro v hv
      simp only [WordPath.vertices_copy,WordPath.vertices,List.mem_singleton] at hv
      subst v
      simp
  | a K =>
      let p : WordPath m (r,j) [BSLetter.a] (r+(m:ℤ)^j,j) := .cons rfl (.nil _)
      refine ⟨p.copy rfl (by simp), ?_⟩
      intro v hv
      simp only [WordPath.vertices_copy,p,WordPath.vertices,List.mem_cons,List.mem_nil_iff,or_false] at hv
      have hs : 0 ≤ (m:ℤ)^j := pow_nonneg (by positivity) _
      obtain rfl | rfl := hv
      · exact ⟨le_rfl,by simpa using le_add_of_nonneg_right hs,le_rfl,by omega⟩
      · exact ⟨by omega,by simp,le_rfl,by omega⟩
  | @append K n q w z hw hz ihw ihz =>
      let Q := r+(n:ℤ)*(m:ℤ)^j
      obtain ⟨p,hp⟩ := ihw r j
      obtain ⟨u,hu⟩ := ihz Q j
      have hend : (Q+(q:ℤ)*(m:ℤ)^j,j) = (r+((n+q:ℕ):ℤ)*(m:ℤ)^j,j) := by
        dsimp [Q]
        congr 1
        push_cast
        ring
      refine ⟨(p.append u).copy rfl hend, ?_⟩
      intro v hv
      simp only [WordPath.vertices_copy,WordPath.mem_vertices_append] at hv
      have hpow : 0 ≤ (m:ℤ)^j := pow_nonneg (by positivity) _
      have hQ : r ≤ Q := le_add_of_nonneg_right (mul_nonneg (by positivity) hpow)
      have hend' := congrArg Prod.fst hend
      change Q+(q:ℤ)*(m:ℤ)^j = r+((n+q:ℕ):ℤ)*(m:ℤ)^j at hend'
      have hqnonneg : 0 ≤ (q:ℤ)*(m:ℤ)^j := mul_nonneg (by positivity) hpow
      obtain hv | hv := hv
      · obtain ⟨hlo,hhi,hjlo,hjhi⟩ := hp v hv
        exact ⟨hlo,by change v.1 ≤ _; dsimp [Q] at *; omega,hjlo,hjhi⟩
      · obtain ⟨hlo,hhi,hjlo,hjhi⟩ := hu v hv
        exact ⟨hQ.trans hlo,by omega,hjlo,hjhi⟩
  | @conjugate K n w hw ih =>
      let Q := r+(n:ℤ)*(m:ℤ)^(j+1)
      obtain ⟨p,hp⟩ := ih r (j+1)
      let d : WordPath m (Q,j+1) [BSLetter.tInv] (Q,j) := .cons (y := (Q,j)) rfl (.nil _)
      let u : WordPath m (r,j) (conjugateWord w) (Q,j) :=
        .cons (s := BSLetter.t) rfl (p.append d)
      have hend : (Q,j) = (r+((m*n:ℕ):ℤ)*(m:ℤ)^j,j) := by
        dsimp [Q]
        congr 1
        push_cast
        rw [pow_succ]
        ring
      refine ⟨u.copy rfl hend, ?_⟩
      intro v hv
      rw [WordPath.vertices_copy] at hv
      change v ∈ ((r,j) :: (p.append d).vertices) at hv
      rw [List.mem_cons,WordPath.mem_vertices_append] at hv
      simp only [d,WordPath.vertices,List.mem_cons,List.mem_nil_iff,or_false] at hv
      have hQ : r ≤ Q := le_add_of_nonneg_right
        (mul_nonneg (by positivity) (pow_nonneg (by positivity) _))
      have he := congrArg Prod.fst hend
      change Q = r+((m*n:ℕ):ℤ)*(m:ℤ)^j at he
      obtain rfl | hv | rfl | rfl := hv
      · exact ⟨le_rfl,by omega,le_rfl,by omega⟩
      · obtain ⟨hlo,hhi,hjlo,hjhi⟩ := hp v hv
        exact ⟨hlo,by omega,by omega,by omega⟩
      · exact ⟨hQ,by omega,by omega,by omega⟩
      · exact ⟨hQ,by omega,le_rfl,by omega⟩
  | @mono K L n w hw hKL ih =>
      obtain ⟨p,hp⟩ := ih r j
      refine ⟨p,?_⟩
      intro v hv
      obtain ⟨hlo,hhi,hjlo,hjhi⟩ := hp v hv
      exact ⟨hlo,hhi,hjlo,by omega⟩

theorem PositiveBSWord.exists_finite_carrier_walk {m K n R : ℕ} {w : List BSLetter}
    (hm : 1 ≤ m) (h : PositiveBSWord m K n w) (hn : n ≤ R) :
    ∃ p : (carrierGraph m K 0 R).Walk (bottomVertex K R 0 (by omega)) (bottomVertex K R n hn),
      p.length = w.length := by
  obtain ⟨p,hp⟩ := h.exists_path 0 0
  let q := p.toWalk hm
  have hsupport : ∀ v ∈ q.support, v ∈ ({v : Vertex | v ∈ carrierVertices K 0 R} : Set Vertex) := by
    intro v hv
    rw [WordPath.toWalk_support] at hv
    obtain ⟨hlo,hhi,_,hj⟩ := hp v hv
    apply mem_carrierVertices.mpr
    have hnR : (n:ℤ) ≤ R := by exact_mod_cast hn
    simp only [pow_zero,mul_one,zero_add] at hhi hj
    exact ⟨hlo,by omega,hj⟩
  let z := q.induce {v : Vertex | v ∈ carrierVertices K 0 R} hsupport
  have hlength : z.length = q.length := by
    have h' := congrArg Walk.length (q.map_induce hsupport)
    simpa only [Walk.length_map] using h'
  have hu : (⟨(0,0),hsupport _ q.start_mem_support⟩ : {v : Vertex // v ∈ carrierVertices K 0 R}) =
      bottomVertex K R 0 (by omega) := by apply Subtype.ext; rfl
  have hv : (⟨(0+(n:ℤ)*(m:ℤ)^0,0),hsupport _ q.end_mem_support⟩ :
      {v : Vertex // v ∈ carrierVertices K 0 R}) = bottomVertex K R n hn := by
    apply Subtype.ext
    simp [bottomVertex]
  refine ⟨z.copy hu hv,?_⟩
  exact (Walk.length_copy z hu hv).trans (hlength.trans (p.toWalk_length hm))

end AbelianTargets
