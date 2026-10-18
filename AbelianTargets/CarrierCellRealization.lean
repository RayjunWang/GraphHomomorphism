import AbelianTargets.DigitPathRealization

/-! # Every digital relation move uses a cell of the literal finite carrier -/

namespace AbelianTargets.IntervalCarriers

theorem WordPath.start_mem_vertices {m : ℕ} {x z : Vertex} {w : List BSLetter}
    (p : WordPath m x w z) : x ∈ p.vertices := by
  cases p <;> simp [WordPath.vertices]

theorem WordPath.end_mem_vertices {m : ℕ} {x z : Vertex} {w : List BSLetter}
    (p : WordPath m x w z) : z ∈ p.vertices := by
  induction p with
  | nil x => simp [WordPath.vertices]
  | cons h p ih => simp only [WordPath.vertices,List.mem_cons]; exact Or.inr ih

def WordPath.castWord {m : ℕ} {x z : Vertex} {w u : List BSLetter}
    (p : WordPath m x w z) (hw : w = u) : WordPath m x u z := hw ▸ p

@[simp] theorem WordPath.vertices_castWord {m : ℕ} {x z : Vertex} {w u : List BSLetter}
    (p : WordPath m x w z) (hw : w = u) : (p.castWord hw).vertices = p.vertices := by
  cases hw
  rfl

theorem WordPath.split {m : ℕ} {x z : Vertex} (a b : List BSLetter)
    (p : WordPath m x (a++b) z) :
    ∃ (y : Vertex) (u : WordPath m x a y) (v : WordPath m y b z),
      p.vertices = (u.append v).vertices := by
  induction a generalizing x with
  | nil => exact ⟨x,.nil x,p,rfl⟩
  | cons s a ih =>
      cases p with
      | cons h p =>
          obtain ⟨y,u,v,heq⟩ := ih p
          exact ⟨y,.cons h u,v,by simp only [WordPath.vertices,WordPath.append,heq]⟩

theorem WordPath.exists_subpath {m : ℕ} {x z : Vertex} (a w b : List BSLetter)
    (p : WordPath m x (a++w++b) z) :
    ∃ (u v : Vertex) (q : WordPath m u w v), ∀ t ∈ q.vertices, t ∈ p.vertices := by
  let p' : WordPath m x (a++(w++b)) z := p.castWord (List.append_assoc a w b)
  obtain ⟨y,u,v,heq⟩ := p'.split a (w++b)
  obtain ⟨t,q,s,heq'⟩ := v.split w b
  refine ⟨y,t,q,?_⟩
  intro c hc
  have hcv : c ∈ v.vertices := by
    rw [heq',WordPath.mem_vertices_append]
    exact Or.inl hc
  have hcp : c ∈ p'.vertices := by
    rw [heq,WordPath.mem_vertices_append]
    exact Or.inr hcv
  simpa only [p',WordPath.vertices_castWord] using hcp

/-- A contextual presentation relation in a path staying in the
carrier is located at one of its actual finite relation cells. The
height and horizontal endpoint constraints follow from vertices of
the three-edge side itself. -/
theorem relation_cell_of_carrier_path {m K : ℕ} {A B : ℤ} {x z : Vertex}
    (a b : List BSLetter)
    (p : WordPath m x (a++[BSLetter.t,BSLetter.a,BSLetter.tInv]++b) z)
    (hvertices : ∀ v ∈ p.vertices, v ∈ carrierVertices K A B) :
    ∃ c : Vertex, c ∈ carrierCells m K A B := by
  obtain ⟨u,v,q,hq⟩ := p.exists_subpath a [BSLetter.t,BSLetter.a,BSLetter.tInv] b
  have hall : ∀ c ∈ q.vertices, c ∈ carrierVertices K A B := fun c hc => hvertices c (hq c hc)
  cases q with
  | @cons s u u₁ v w ht q =>
    cases q with
    | @cons s' u₁ u₂ v w' ha q =>
      have hu : u ∈ carrierVertices K A B := hall u (by simp [WordPath.vertices])
      have hu₁ : u₁ ∈ carrierVertices K A B := hall u₁ (by simp [WordPath.vertices])
      have hu₂ : u₂ ∈ carrierVertices K A B := hall u₂ (by
        simp only [WordPath.vertices,List.mem_cons]
        exact Or.inr (Or.inr q.start_mem_vertices))
      have hstep₁ : u₁ = (u.1,u.2+1) := ht
      have hstep₂ : u₂ = (u₁.1+(m:ℤ)^u₁.2,u₁.2) := ha
      obtain ⟨_,_,hj⟩ := mem_carrierVertices.mp hu₁
      obtain ⟨_,hr,_⟩ := mem_carrierVertices.mp hu₂
      have hj' : u.2 < K := by rw [hstep₁] at hj; simp only at hj; omega
      have hr' : u.1+(m:ℤ)^(u.2+1) ≤ B := by
        simpa only [hstep₂,hstep₁] using hr
      exact ⟨u,Finset.mem_filter.mpr ⟨hu,hj',hr'⟩⟩

end AbelianTargets.IntervalCarriers
