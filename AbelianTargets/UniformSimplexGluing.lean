import AbelianTargets.SimplexDimensionBounds

/-!
# A uniform modulus on families of bounded-dimensional simplex unions

The vertex sets and number of simplices may grow. A common simplex size bound
and a common modulus on individual faces suffice for a common global modulus.
-/

namespace AbelianTargets

noncomputable section

theorem uniform_simplex_face_modulus {I : Type*} {V : I → Type*}
    [∀ i, Fintype (V i)] {Z : Type*} [PseudoMetricSpace Z]
    (F : ∀ i, Finset (Finset (V i))) (f : ∀ i, SimplicialCarrier (F i) → Z)
    (N : ℕ) (hN : ∀ i s, s ∈ F i → s.card ≤ N)
    (hface : ∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧
      ∀ i s, s ∈ F i → ∀ p q : SimplicialCarrier (F i),
        p.1.SupportedOn (s : Set (V i)) → q.1.SupportedOn (s : Set (V i)) →
        dist p q < δ → dist (f i p) (f i q) < ε) :
    ∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧ ∀ i (p q : SimplicialCarrier (F i)),
      dist p q < δ → dist (f i p) (f i q) < ε := by
  classical
  intro ε hε
  obtain ⟨η,hη,hlocal⟩ := hface (ε/2) (by linarith)
  let c : ℝ := (N : ℝ)+1
  have hc : 0<c := by dsimp [c]; positivity
  let δ : ℝ := min (1/c) (η/c)
  have hδ : 0<δ := lt_min (one_div_pos.mpr hc) (div_pos hη hc)
  refine ⟨δ,hδ,?_⟩
  intro i p q hpq
  obtain ⟨s,hs,hps⟩ := p.2
  obtain ⟨t,ht,hqt⟩ := q.2
  have hsmall : c*dist p q < 1 := by
    have hh : dist p q < 1/c := hpq.trans_le (min_le_left _ _)
    simpa only [mul_comm] using (lt_div_iff₀ hc).mp hh
  have hsmall' : (N : ℝ)*dist p.1 q.1 < 1 := by
    have hh : (N : ℝ)*dist p q ≤ c*dist p q :=
      mul_le_mul_of_nonneg_right (by dsimp [c]; linarith) dist_nonneg
    exact hh.trans_lt hsmall
  obtain ⟨r,hrs,hrt,hpr,hqr⟩ :=
    Probability.exists_commonPoint_close_of_face_bound p.1 q.1 s t hps hqt N
      (hN i s hs) (hN i t ht) hsmall'
  let r' : SimplicialCarrier (F i) := ⟨r,s,hs,hrs⟩
  have hnear : c*dist p q < η := by
    have hh : dist p q < η/c := hpq.trans_le (min_le_right _ _)
    simpa only [mul_comm] using (lt_div_iff₀ hc).mp hh
  have hpr' : dist p r' < η := hpr.trans_lt hnear
  have hqr' : dist q r' < η := hqr.trans_lt hnear
  have hx := hlocal i s hs p r' hps hrs hpr'
  have hy := hlocal i t ht q r' hqt hrt hqr'
  have hh := dist_triangle (f i p) (f i r') (f i q)
  rw [dist_comm (f i r') (f i q)] at hh
  linarith

end

end AbelianTargets
