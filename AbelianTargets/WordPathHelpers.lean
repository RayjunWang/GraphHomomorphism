import AbelianTargets.DigitPathRealization

/-!
# Determinism and exact vertex rows of directed carrier word paths

The elementary directed steps determine their endpoint. Consequently an
edge word has a unique literal vertex row from a specified start, and
concatenation removes exactly one copy of the shared endpoint.
-/

namespace AbelianTargets.IntervalCarriers

theorem LetterStep.unique {m : ℕ} {s : BSLetter} {x y z : Vertex}
    (h : LetterStep m s x y) (h' : LetterStep m s x z) : y = z := by
  cases s with
  | a => exact h.trans h'.symm
  | t => exact h.trans h'.symm
  | tInv =>
      have hy₁ := congrArg Prod.fst h
      have hy₂ := congrArg Prod.snd h
      have hz₁ := congrArg Prod.fst h'
      have hz₂ := congrArg Prod.snd h'
      apply Prod.ext <;> dsimp [LetterStep,VerticalStep] at * <;> omega

theorem WordPath.endpoint_eq {m : ℕ} {x y z : Vertex} {w : List BSLetter}
    (p : WordPath m x w y) (q : WordPath m x w z) : y = z := by
  induction p generalizing z with
  | nil x => cases q; rfl
  | @cons s x u y w h p ih =>
      cases q with
      | @cons _ _ v _ _ h' q =>
          have huv := h.unique h'
          subst v
          exact ih q

theorem WordPath.vertices_eq {m : ℕ} {x y z : Vertex} {w : List BSLetter}
    (p : WordPath m x w y) (q : WordPath m x w z) : p.vertices = q.vertices := by
  induction p generalizing z with
  | nil x => cases q; rfl
  | @cons s x u y w h p ih =>
      cases q with
      | @cons _ _ v _ _ h' q =>
          have huv := h.unique h'
          subst v
          simp only [WordPath.vertices]
          exact congrArg (List.cons x) (ih q)

@[simp] theorem WordPath.vertices_length {m : ℕ} {x y : Vertex} {w : List BSLetter}
    (p : WordPath m x w y) : p.vertices.length = w.length+1 := by
  induction p with
  | nil x => rfl
  | cons h p ih => simp only [WordPath.vertices,List.length_cons,ih]

theorem WordPath.vertices_ne_nil {m : ℕ} {x y : Vertex} {w : List BSLetter}
    (p : WordPath m x w y) : p.vertices ≠ [] := by
  intro h
  have hh := p.vertices_length
  rw [h] at hh
  simp only [List.length_nil] at hh
  omega

@[simp] theorem WordPath.vertices_append {m : ℕ} {x y z : Vertex} {w u : List BSLetter}
    (p : WordPath m x w y) (q : WordPath m y u z) :
    (p.append q).vertices = p.vertices.dropLast ++ q.vertices := by
  induction p with
  | nil x => rfl
  | @cons s x v y w h p ih =>
      simp only [WordPath.append,WordPath.vertices,ih]
      rw [List.dropLast_cons_of_ne_nil p.vertices_ne_nil,List.cons_append]

end AbelianTargets.IntervalCarriers
