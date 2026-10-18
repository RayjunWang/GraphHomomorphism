import AbelianTargets.AnisotropicMarkers
import AbelianTargets.ParityFields
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith

/-!
# Covering and overlap bounds for the actual marker boxes

Integer cuts in the prescribed ranges give a covering of the ambient
real orbit coordinates. Their sides lie between four and six times
the scale, and intersecting boxes have centers within six scales.
The subsequent retained-box subdivision and regular CW construction
are not supplied by these covering estimates.
-/

namespace AbelianTargets

noncomputable section

structure RectangularCuts {d : ℕ} (L : Fin d → ℕ) (A : Set (Lattice d)) where
  lower : A → Lattice d
  upper : A → Lattice d
  lower_bound : ∀ a i,a.val i-3*(L i : ℤ) ≤ lower a i ∧ lower a i ≤ a.val i-2*(L i : ℤ)
  upper_bound : ∀ a i,a.val i+2*(L i : ℤ) ≤ upper a i ∧ upper a i ≤ a.val i+3*(L i : ℤ)

def RectangularCuts.box {d : ℕ} {L : Fin d → ℕ} {A : Set (Lattice d)}
    (cuts : RectangularCuts L A) (a : A) : Set (RealCoordinates d) :=
  {z | ∀ i,(cuts.lower a i : ℝ) ≤ z i ∧ z i ≤ (cuts.upper a i : ℝ)}

theorem RectangularCuts.side_bounds {d : ℕ} {L : Fin d → ℕ} {A : Set (Lattice d)}
    (cuts : RectangularCuts L A) (a : A) (i : Fin d) :
    4*(L i : ℤ) ≤ cuts.upper a i-cuts.lower a i ∧
      cuts.upper a i-cuts.lower a i ≤ 6*(L i : ℤ) := by
  obtain ⟨hl₀,hl₁⟩ := cuts.lower_bound a i
  obtain ⟨hu₀,hu₁⟩ := cuts.upper_bound a i
  omega

theorem RectangularCuts.cover {d : ℕ} {L : Fin d → ℕ} {A : Set (Lattice d)}
    (cuts : RectangularCuts L A) (hL : ∀ i,1 ≤ L i)
    (hcover : ∀ u : Lattice d,∃ a ∈ A,∀ i,|u i-a i| ≤ (L i : ℤ)) :
    ∀ z : RealCoordinates d,∃ a : A,z ∈ cuts.box a := by
  intro z
  let u : Lattice d := fun i => Int.floor (z i)
  obtain ⟨a,ha,hclose⟩ := hcover u
  refine ⟨⟨a,ha⟩,?_⟩
  intro i
  have hu₀ : (u i : ℝ) ≤ z i := Int.floor_le (z i)
  have hu₁ : z i < (u i : ℝ)+1 := Int.lt_floor_add_one (z i)
  have hclose' : -(L i : ℤ) ≤ u i-a i ∧ u i-a i ≤ (L i : ℤ) := abs_le.mp (hclose i)
  have hl : cuts.lower ⟨a,ha⟩ i ≤ a i-2*(L i : ℤ) := (cuts.lower_bound ⟨a,ha⟩ i).2
  have hh : a i+2*(L i : ℤ) ≤ cuts.upper ⟨a,ha⟩ i := (cuts.upper_bound ⟨a,ha⟩ i).1
  have hLi : (1 : ℤ) ≤ L i := by exact_mod_cast hL i
  have hlow : cuts.lower ⟨a,ha⟩ i ≤ u i := by omega
  have hhigh : u i+1 ≤ cuts.upper ⟨a,ha⟩ i := by omega
  have hlow' : (cuts.lower ⟨a,ha⟩ i : ℝ) ≤ (u i : ℝ) := by exact_mod_cast hlow
  have hhigh' : (u i : ℝ)+1 ≤ (cuts.upper ⟨a,ha⟩ i : ℝ) := by exact_mod_cast hhigh
  exact ⟨hlow'.trans hu₀,hu₁.le.trans hhigh'⟩

theorem RectangularCuts.overlap_centers {d : ℕ} {L : Fin d → ℕ} {A : Set (Lattice d)}
    (cuts : RectangularCuts L A) {a b : A} (hoverlap : (cuts.box a ∩ cuts.box b).Nonempty) :
    ∀ i,|a.val i-b.val i| ≤ 6*(L i : ℤ) := by
  obtain ⟨z,hza,hzb⟩ := hoverlap
  intro i
  have hab' : (cuts.lower a i : ℝ) ≤ (cuts.upper b i : ℝ) := (hza i).1.trans (hzb i).2
  have hba' : (cuts.lower b i : ℝ) ≤ (cuts.upper a i : ℝ) := (hzb i).1.trans (hza i).2
  have hab : cuts.lower a i ≤ cuts.upper b i := by exact_mod_cast hab'
  have hba : cuts.lower b i ≤ cuts.upper a i := by exact_mod_cast hba'
  obtain ⟨hla,_⟩ := cuts.lower_bound a i
  obtain ⟨hlb,_⟩ := cuts.lower_bound b i
  obtain ⟨_,hua⟩ := cuts.upper_bound a i
  obtain ⟨_,hub⟩ := cuts.upper_bound b i
  rw [abs_le]
  omega

/-- The box-cover conclusion specialized to the orbit markers constructed
on an actual action. -/
theorem anisotropic_marker_boxes_cover {d : ℕ} {L : Fin d → ℕ} {X : Type*}
    [TopologicalSpace X] [AddAction (Lattice d) X]
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (x : X)
    (cuts : RectangularCuts L {a : Lattice d | a +ᵥ x ∈ M.markers}) :
    ∀ z : RealCoordinates d,∃ a,z ∈ cuts.box a :=
  cuts.cover hL (M.covering x)

end

end AbelianTargets
