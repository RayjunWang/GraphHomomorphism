import AbelianTargets.UpperCarrierCollapse

/-! The successive free diagonals of a presentation-polygon fan. -/

namespace AbelianTargets.IntervalCarriers

theorem lowerVertex_injective {m : ℕ} (hm : 1 ≤ m) (r : ℤ) (j : ℕ) :
    Function.Injective (lowerVertex m r j) := by
  intro n k h
  have he := congrArg Prod.fst h
  dsimp [lowerVertex] at he
  have hp : 0 < (m : ℤ)^j := pow_pos (by exact_mod_cast (show 0 < m by omega)) _
  have he' : (n : ℤ)*(m : ℤ)^j = (k : ℤ)*(m : ℤ)^j := by linarith
  have hn := mul_right_cancel₀ (ne_of_gt hp) he'
  exact_mod_cast hn

theorem subset_drop_third {V : Type*} [DecidableEq V] {s : Finset V} {a b c : V}
    (hs : s ⊆ {a,b,c}) (ha : a ∈ s) (hforbid : ¬(a ∈ s ∧ c ∈ s)) : s ⊆ {a,b} := by
  intro v hv
  have hv' := hs hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv' ⊢
  rcases hv' with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hforbid ⟨ha,by simpa only [h] using hv⟩).elim

theorem lower_edge_free {m K n : ℕ} {A B r : ℤ} (hm : 1 ≤ m) (hn : n < m)
    {s : Finset Vertex} (hs : CarrierFace m (K+1) A B s)
    (ha : upperLeft r K ∈ s) (hb : lowerVertex m r K (n+1) ∈ s)
    (hupper : ∀ c : TopCell m K A B,
      ¬(upperLeft c.1.1 c.1.2 ∈ s ∧ upperRight m c.1.1 c.1.2 ∈ s))
    (hnext : n+1 < m → ∀ c : TopCell m K A B,
      ¬(upperLeft c.1.1 c.1.2 ∈ s ∧ lowerVertex m c.1.1 c.1.2 (n+2) ∈ s)) :
    s ⊆ lowerTriangle m (r,K) n := by
  have hab : upperLeft r K ≠ lowerVertex m r K (n+1) := by
    intro h; have he := congrArg Prod.snd h; dsimp [upperLeft,lowerVertex] at he; omega
  rcases hs with ⟨v,hv,hs⟩ | ⟨u,hu,v,hv,he,hs⟩ | ⟨t,ht,hs⟩
  · have ha' := Finset.mem_singleton.mp (hs ha)
    have hb' := Finset.mem_singleton.mp (hs hb)
    exact (hab (ha'.trans hb'.symm)).elim
  · have ha' := hs ha
    have hb' := hs hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha' hb'
    rcases ha' with hau | hav <;> rcases hb' with hbu | hbv
    · exact (hab (hau.trans hbu.symm)).elim
    · rw [←hau,←hbv] at hs
      apply hs.trans
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [lowerTriangle]
    · rw [←hav,←hbu] at hs
      apply hs.trans
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [lowerTriangle]
    · exact (hab (hav.trans hbv.symm)).elim
  · obtain ⟨c,hc,ht⟩ := Finset.mem_biUnion.mp ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · subst t
      have ha' := top_mem_upperTriangle hc (hs ha) (by rfl)
      have hb' : lowerVertex m r K (n+1) = lowerVertex m c.1 c.2 m := by
        have hmem := hs hb
        simp only [upperTriangle,Finset.mem_insert,Finset.mem_singleton] at hmem
        rcases hmem with h | h | h
        · have he := congrArg Prod.snd h; dsimp [lowerVertex,upperLeft] at he
          have he' := congrArg Prod.snd (ha'.resolve_right (by
            intro h'; have hh := congrArg Prod.snd h'; dsimp [upperLeft,upperRight] at hh; omega))
          dsimp [upperLeft] at he'; omega
        · exact h
        · have hh := congrArg Prod.snd h; dsimp [lowerVertex,upperRight] at hh
          rcases ha' with he | he <;> have he' := congrArg Prod.snd he <;>
            dsimp [upperLeft,upperRight] at he' <;> omega
      rcases ha' with hau | hav
      · have hr : r = c.1 := congrArg Prod.fst hau
        have hj : K = c.2 := by have hh := congrArg Prod.snd hau; dsimp [upperLeft] at hh; omega
        have hc' : c = (r,K) := Prod.ext hr.symm hj.symm
        have hcTop : c ∈ topCells m K A B := Finset.mem_filter.mpr ⟨hc,hj.symm⟩
        have hforbid := hupper ⟨c,hcTop⟩
        change ¬(upperLeft c.1 c.2 ∈ s ∧ upperRight m c.1 c.2 ∈ s) at hforbid
        rw [hc'] at hs hb' hforbid
        have hnm : n+1 = m := lowerVertex_injective hm r K hb'
        have hsmall := subset_drop_third hs ha hforbid
        apply hsmall.trans
        intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        rcases hv with rfl | h
        · simp [lowerTriangle]
        · change v = lowerVertex m r K m at h
          have hv' : v = lowerVertex m r K (n+1) := h.trans (congrArg (lowerVertex m r K) hnm.symm)
          simp [lowerTriangle,hv']
      · have hj : K = c.2 := by have hh := congrArg Prod.snd hav; dsimp [upperLeft,upperRight] at hh; omega
        have h1 := congrArg Prod.fst hav
        have h2 := congrArg Prod.fst hb'
        dsimp [upperLeft,upperRight,lowerVertex] at h1 h2
        rw [←hj,pow_succ,mul_comm] at h1
        rw [←hj] at h2
        have hp : 0 < (m : ℤ)^K := pow_pos (by exact_mod_cast (show 0 < m by omega)) _
        have hnpos : 0 < ((n+1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos n
        have hp' := mul_pos hnpos hp
        push_cast at hp'
        linarith
    · obtain ⟨k,hk,ht⟩ := Finset.mem_image.mp ht
      subst t
      have hau := top_mem_lowerTriangle hc (hs ha) (by rfl)
      have hr : r = c.1 := congrArg Prod.fst hau
      have hj : K = c.2 := by have hh := congrArg Prod.snd hau; dsimp [upperLeft] at hh; omega
      have hc' : c = (r,K) := Prod.ext hr.symm hj.symm
      have hcTop : c ∈ topCells m K A B := Finset.mem_filter.mpr ⟨hc,hj.symm⟩
      rw [hc'] at hs
      have hb' := hs hb
      simp only [lowerTriangle,Finset.mem_insert,Finset.mem_singleton] at hb'
      rcases hb' with h | h | h
      · exact (hab h.symm).elim
      · have hnk : n+1 = k := lowerVertex_injective hm r K h
        subst k
        have hforbid := hnext (Finset.mem_range.mp hk) ⟨c,hcTop⟩
        change ¬(upperLeft c.1 c.2 ∈ s ∧ lowerVertex m c.1 c.2 (n+2) ∈ s) at hforbid
        rw [hc'] at hforbid
        have hsmall := subset_drop_third hs ha hforbid
        apply hsmall.trans
        intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> simp [lowerTriangle]
      · have hnk : n+1 = k+1 := lowerVertex_injective hm r K h
        have hnk' : n = k := by omega
        subst k
        exact hs

end AbelianTargets.IntervalCarriers
