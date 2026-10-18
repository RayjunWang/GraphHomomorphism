import AbelianTargets.Torus
import AbelianTargets.Dimension

namespace AbelianTargets

theorem SignedDirection.same_axis_vectors {m : ℕ} (u v : SignedDirection m)
    (haxis : u.axis = v.axis) : v.vector = u.vector ∨ v.vector = -u.vector := by
  rcases u with ⟨i, b⟩
  rcases v with ⟨j, c⟩
  change i = j at haxis
  subst j
  cases b <;> cases c <;> simp [SignedDirection.vector]

/-- The exact distinct-axis contradiction used in Lemma 7.4. The map is
on the literal finite torus, and every positive coordinate edge is
required to carry its supplied signed direction. -/
theorem coprime_torus_directions_distinct_axes {p q m : ℕ} {V : Type*}
    {H : SimpleGraph V} (hp : 0 < p) (hq : 0 < q) (hcop : p.Coprime q)
    (laws : DirectionLaws H m) (f : ZMod p × ZMod q → V)
    (u v : SignedDirection m)
    (hh : ∀ i j, H.Adj (f (i,j)) (f (i+1,j)))
    (hv : ∀ i j, H.Adj (f (i,j)) (f (i,j+1)))
    (hhu : ∀ i j, (laws.direction (hh i j)).vector = u.vector)
    (hvv : ∀ i j, (laws.direction (hv i j)).vector = v.vector) : u.axis ≠ v.axis := by
  intro haxis
  rcases u.same_axis_vectors v haxis with heq | heq
  · have hdiag : ∀ i j, f (i+1,j) = f (i,j+1) := by
      intro i j
      apply laws.straight_middle_unique_of_vectors (hh i j) (hv (i+1) j)
        (hv i j) (hh i (j+1))
      · rw [hhu, hvv, heq]
      · rw [hhu, hvv, heq]
      · rw [hhu, hhu]
    exact coprime_torus_no_collapsed_horizontal_edge hp hq hcop H f 1 (Or.inl rfl)
      hdiag ⟨0,0,hh 0 0⟩
  · have hneg : ∀ i j, (laws.direction (hv i (j-1)).symm).vector = u.vector := by
      intro i j
      rw [laws.reverse (hv i (j-1)), hvv, heq, neg_neg]
    have hdiag : ∀ i j, f (i+1,j) = f (i,j-1) := by
      intro i j
      have h₁ : H.Adj (f (i+1,j)) (f (i+1,j-1)) := by
        simpa using (hv (i+1) (j-1)).symm
      have h₂ : H.Adj (f (i,j)) (f (i,j-1)) := by
        simpa using (hv i (j-1)).symm
      have h₁v : (laws.direction h₁).vector = u.vector := by
        simpa only [sub_add_cancel] using hneg (i+1) j
      have h₂v : (laws.direction h₂).vector = u.vector := by
        simpa only [sub_add_cancel] using hneg i j
      apply laws.straight_middle_unique_of_vectors (hh i j) h₁ h₂ (hh i (j-1))
      · rw [hhu, h₁v]
      · rw [hhu, h₂v]
      · rw [hhu, hhu]
    exact coprime_torus_no_collapsed_horizontal_edge hp hq hcop H f (-1) (Or.inr rfl)
      (by simpa only [sub_eq_add_neg] using hdiag) ⟨0,0,hh 0 0⟩

end AbelianTargets
