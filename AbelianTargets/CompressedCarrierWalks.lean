import AbelianTargets.CompressedWords
import AbelianTargets.IntervalCarriers
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Actual logarithmically short walks in finite interval carriers

The recursive digit path is constructed in the literal skeleton graph.
All of its vertices stay in the horizontal interval between its endpoints
and below the digit height. Consequently it gives an actual walk in the
finite induced carrier, with the explicit logarithmic length bound.
-/

namespace AbelianTargets.IntervalCarriers

open SimpleGraph

theorem exists_horizontal_walk (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (r : ℤ) (j : ℕ) :
    ∃ p : (graph m).Walk (r,j) (r + (n : ℤ) * (m : ℤ)^j,j),
      p.length = n ∧ ∀ v ∈ p.support,
        r ≤ v.1 ∧ v.1 ≤ r + (n : ℤ) * (m : ℤ)^j ∧ v.2 = j := by
  induction n generalizing r with
  | zero =>
      refine ⟨Walk.nil.copy rfl (by simp), by simp, ?_⟩
      intro v hv
      simp only [Walk.support_copy, Walk.support_nil, List.mem_singleton] at hv
      subst v
      simp
  | succ n ih =>
      let s := (m : ℤ)^j
      have hs : 0 ≤ s := pow_nonneg (by exact_mod_cast (show 0 ≤ m by omega)) _
      obtain ⟨p,hp,hv⟩ := ih (r+s)
      have hadj : (graph m).Adj (r,j) (r+s,j) := horizontal_adj hm rfl
      let w := Walk.cons hadj p
      have hend : (r+s+(n : ℤ)*(m : ℤ)^j,j) = (r+((n+1 : ℕ) : ℤ)*(m : ℤ)^j,j) := by
        dsimp [s]
        congr 1
        ring
      refine ⟨w.copy rfl hend, ?_, ?_⟩
      · simp only [Walk.length_copy, w, Walk.length_cons, hp]
      · intro v hv'
        simp only [Walk.support_copy, w, Walk.support_cons, List.mem_cons] at hv'
        obtain rfl | hv' := hv'
        · refine ⟨le_rfl, ?_, rfl⟩
          have : 0 ≤ ((n+1 : ℕ) : ℤ) * (m : ℤ)^j := mul_nonneg (by positivity) hs
          omega
        · obtain ⟨hlo,hhi,hj⟩ := hv v hv'
          refine ⟨?_,?_,hj⟩
          · omega
          · have he := congrArg Prod.fst hend
            change r+s+(n : ℤ)*(m : ℤ)^j = _ at he
            omega

theorem exists_compressed_skeleton_walk (m : ℕ) (hm : 2 ≤ m) (n : ℕ) (r : ℤ) (j : ℕ) :
    ∃ p : (graph m).Walk (r,j) (r + (n : ℤ) * (m : ℤ)^j,j),
      p.length = (compressedWord m hm n).length ∧ ∀ v ∈ p.support,
        r ≤ v.1 ∧ v.1 ≤ r + (n : ℤ) * (m : ℤ)^j ∧
        j ≤ v.2 ∧ v.2 ≤ j + Nat.log m n := by
  induction n using Nat.strong_induction_on generalizing r j with
  | h n ih =>
      by_cases hn : n < m
      · obtain ⟨p,hp,hv⟩ := exists_horizontal_walk m (by omega) n r j
        refine ⟨p, ?_, ?_⟩
        · rw [compressedWord_of_lt m hm hn, List.length_replicate]
          exact hp
        · intro v hv'
          obtain ⟨hlo,hhi,hj⟩ := hv v hv'
          exact ⟨hlo,hhi,by omega,by omega⟩
      · have hdiv : n/m < n := Nat.div_lt_self (by omega) (by omega)
        have hlog : 1 ≤ Nat.log m n := by
          apply Nat.le_log_of_pow_le (by omega)
          simpa only [Nat.pow_one] using (show m ≤ n by omega)
        have hlogq : Nat.log m (n/m) + 1 = Nat.log m n := by
          rw [Nat.log_div_base]
          omega
        let Q : ℤ := r + (n/m : ℕ) * (m : ℤ)^(j+1)
        obtain ⟨p,hp,hpSupport⟩ := ih (n/m) hdiv r (j+1)
        obtain ⟨z,hz,hzSupport⟩ := exists_horizontal_walk m (by omega) (n%m) Q j
        have hup : (graph m).Adj (r,j) (r,j+1) := vertical_adj rfl
        have hdown : (graph m).Adj (Q,j+1) (Q,j) :=
          (vertical_adj (m := m) (x := (Q,j)) (y := (Q,j+1)) rfl).symm
        let w := Walk.cons hup (p.append (Walk.cons hdown z))
        have hdecomp : (n : ℤ) = (n/m : ℕ) * (m : ℤ) + (n%m : ℕ) := by
          exact_mod_cast (show n = n/m*m+n%m from by
            simpa only [Nat.mul_comm] using (Nat.div_add_mod n m).symm)
        have hend : (Q + (n%m : ℕ)*(m : ℤ)^j,j) = (r+(n : ℤ)*(m : ℤ)^j,j) := by
          congr 1
          calc
            Q + (n%m : ℕ)*(m : ℤ)^j = r+((n/m : ℕ)*(m : ℤ)+(n%m : ℕ))*(m : ℤ)^j := by
              dsimp [Q]
              rw [pow_succ]
              ring
            _ = r+(n : ℤ)*(m : ℤ)^j :=
              congrArg (fun z : ℤ => r+z*(m : ℤ)^j) hdecomp.symm
        have hpow : 0 ≤ (m : ℤ)^j := pow_nonneg (by positivity) _
        have hQlo : r ≤ Q := by
          exact le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg (n/m))
            (pow_nonneg (by positivity) (j+1)))
        have hQhi : Q ≤ r+(n : ℤ)*(m : ℤ)^j := by
          have : 0 ≤ (n%m : ℕ)*(m : ℤ)^j := mul_nonneg (by positivity) hpow
          have he := congrArg Prod.fst hend
          change Q + (n%m : ℕ)*(m : ℤ)^j = _ at he
          omega
        refine ⟨w.copy rfl hend, ?_, ?_⟩
        · rw [Walk.length_copy]
          simp only [w, Walk.length_cons, Walk.length_append, hp, hz,
            compressedWord_of_ge m hm (show m ≤ n by omega), List.length_cons,
            List.length_append, List.length_replicate]
        · intro v hv
          simp only [Walk.support_copy, w, Walk.support_cons, List.mem_cons,
            Walk.mem_support_append_iff] at hv
          obtain rfl | hv | rfl | hv := hv
          · exact ⟨le_rfl,hQlo.trans hQhi,le_rfl,by omega⟩
          · obtain ⟨hlo,hhi,hjlo,hjhi⟩ := hpSupport v hv
            exact ⟨hlo,hhi.trans hQhi,by omega,by omega⟩
          · exact ⟨hQlo,hQhi,by omega,by omega⟩
          · obtain ⟨hlo,hhi,hj⟩ := hzSupport v hv
            have he := congrArg Prod.fst hend
            change Q + (n%m : ℕ)*(m : ℤ)^j = _ at he
            exact ⟨hQlo.trans hlo,by omega,by omega,by omega⟩

def bottomVertex (K R n : ℕ) (hn : n ≤ R) :
    {v : Vertex // v ∈ carrierVertices K 0 R} :=
  ⟨((n : ℤ),0), mem_carrierVertices.mpr ⟨by positivity, by change (n : ℤ) ≤ R; exact_mod_cast hn, by omega⟩⟩

/-- A uniform explicit logarithmic bound for actual walks in the finite
carrier, for every integer endpoint of the interval simultaneously. -/
theorem exists_short_finite_carrier_walk (m : ℕ) (hm : 2 ≤ m)
    (K R : ℕ) (hK : Nat.log m R ≤ K) (n : ℕ) (hn : n ≤ R) :
    ∃ p : (carrierGraph m K 0 R).Walk (bottomVertex K R 0 (by omega)) (bottomVertex K R n hn),
      p.length ≤ (m+1)*(Nat.log m R+1) := by
  obtain ⟨p,hp,hv⟩ := exists_compressed_skeleton_walk m hm n 0 0
  have hsupport : ∀ v ∈ p.support, v ∈ ({v : Vertex | v ∈ carrierVertices K 0 R} : Set Vertex) := by
    intro v h
    obtain ⟨hlo,hhi,_,hj⟩ := hv v h
    have hnR : (n : ℤ) ≤ R := by exact_mod_cast hn
    have hlog := Nat.log_mono_right (b := m) hn
    apply mem_carrierVertices.mpr
    simp only [pow_zero, mul_one, zero_add] at hhi hj
    exact ⟨hlo,by omega,by omega⟩
  let q := p.induce {v : Vertex | v ∈ carrierVertices K 0 R} hsupport
  have hlength : q.length = p.length := by
    have h := congrArg Walk.length (p.map_induce hsupport)
    simpa only [Walk.length_map] using h
  have hu : (⟨(0,0), hsupport _ p.start_mem_support⟩ : {v : Vertex // v ∈ carrierVertices K 0 R}) =
      bottomVertex K R 0 (by omega) := by apply Subtype.ext; rfl
  have hv' : (⟨(0 + (n : ℤ)*(m : ℤ)^0,0), hsupport _ p.end_mem_support⟩ :
      {v : Vertex // v ∈ carrierVertices K 0 R}) = bottomVertex K R n hn := by
    apply Subtype.ext
    simp [bottomVertex]
  refine ⟨q.copy hu hv', ?_⟩
  calc
    (q.copy hu hv').length = q.length := SimpleGraph.Walk.length_copy q hu hv'
    _ = (compressedWord m hm n).length := hlength.trans hp
    _ ≤ (m+1)*(Nat.log m R+1) := compressedWord_interval_uniform_length m hm R n hn

end AbelianTargets.IntervalCarriers
