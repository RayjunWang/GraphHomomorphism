import AbelianTargets.FixedOrbitPriorityCuts

/-!
# Repointing covariance of actual orbit cuts

Changing the orbit origin by `t` changes every lattice coordinate by
`-t`. The neighborhood, priorities, and actual cut iteration respect
this change exactly.
-/

namespace AbelianTargets
noncomputable section

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]

theorem mem_inactiveOrbitNeighbors_repoint
    (M : AnisotropicClopenMarkers d L X) (S : ℕ) (x : X) (t a b : Lattice d) :
    b ∈ inactiveOrbitNeighbors M S (t +ᵥ x) a ↔
      b+t ∈ inactiveOrbitNeighbors M S x (a+t) := by
  classical
  by_cases ha : (a+t) +ᵥ x ∈ M.markers
  · have ha' : a +ᵥ (t +ᵥ x) ∈ M.markers := by simpa only [add_vadd] using ha
    rw [mem_inactiveOrbitNeighbors_of_mem M S _ _ _ ha',
      mem_inactiveOrbitNeighbors_of_mem M S _ _ _ ha]
    simp only [add_vadd,Pi.add_apply,add_sub_add_right_eq_sub]
  · have ha' : a +ᵥ (t +ᵥ x) ∉ M.markers := by simpa only [add_vadd] using ha
    simp only [inactiveOrbitNeighbors,if_neg ha,if_neg ha',Finset.mem_singleton,
      add_left_inj]

theorem fixedOrbitPriority_repoint
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X))
    (c : M.markers → Fin ((2*S+1)^d))
    (hproper : ∀ u v,(markerProximityGraph M S free).Adj u v → c u ≠ c v)
    (x : X) (t a : Lattice d) :
    (fixedOrbitPriorityNeighborhood M hL S free c hproper (t +ᵥ x)).priority a =
      (fixedOrbitPriorityNeighborhood M hL S free c hproper x).priority (a+t) := by
  change markerPriorityExtension _ _ _ (a +ᵥ (t +ᵥ x)) =
    markerPriorityExtension _ _ _ ((a+t) +ᵥ x)
  rw [add_vadd]

theorem earlierPriorityCuts_repoint
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X))
    (c : M.markers → Fin ((2*S+1)^d))
    (hproper : ∀ u v,(markerProximityGraph M S free).Adj u v → c u ≠ c v)
    (x : X) (t a : Lattice d) (n : ℕ) (i : Fin d)
    (old new : Lattice d → ℤ × ℤ)
    (hold : ∀ b,new b = ((old (b+t)).1-t i,(old (b+t)).2-t i)) :
    earlierPriorityCuts (fixedOrbitPriorityNeighborhood M hL S free c hproper (t +ᵥ x)) new n a =
      translatedCuts (-t i)
        (earlierPriorityCuts (fixedOrbitPriorityNeighborhood M hL S free c hproper x) old n (a+t)) := by
  classical
  ext z
  simp only [earlierPriorityCuts,translatedCuts,Finset.mem_biUnion,Finset.mem_filter,
    Finset.mem_insert,Finset.mem_singleton,Finset.mem_image]
  constructor
  · rintro ⟨b,⟨hb,hp⟩,hz | hz⟩
    · refine ⟨(old (b+t)).1,⟨b+t,⟨?_,?_⟩,Or.inl rfl⟩,?_⟩
      · exact (mem_inactiveOrbitNeighbors_repoint M S x t a b).mp hb
      · simpa only [fixedOrbitPriority_repoint M hL S free c hproper x t b] using hp
      · rw [hold] at hz; dsimp at hz; omega
    · refine ⟨(old (b+t)).2,⟨b+t,⟨?_,?_⟩,Or.inr rfl⟩,?_⟩
      · exact (mem_inactiveOrbitNeighbors_repoint M S x t a b).mp hb
      · simpa only [fixedOrbitPriority_repoint M hL S free c hproper x t b] using hp
      · rw [hold] at hz; dsimp at hz; omega
  · rintro ⟨w,⟨b,⟨hb,hp⟩,hw | hw⟩,hz⟩
    · refine ⟨b-t,⟨?_,?_⟩,Or.inl ?_⟩
      · apply (mem_inactiveOrbitNeighbors_repoint M S x t a (b-t)).mpr
        simpa only [sub_add_cancel] using hb
      · rw [fixedOrbitPriority_repoint M hL S free c hproper x t (b-t),sub_add_cancel]
        exact hp
      · rw [hold,sub_add_cancel]; dsimp; omega
    · refine ⟨b-t,⟨?_,?_⟩,Or.inr ?_⟩
      · apply (mem_inactiveOrbitNeighbors_repoint M S x t a (b-t)).mpr
        simpa only [sub_add_cancel] using hb
      · rw [fixedOrbitPriority_repoint M hL S free c hproper x t (b-t),sub_add_cancel]
        exact hp
      · rw [hold,sub_add_cancel]; dsimp; omega

theorem fixedOrbitCutIteration_repoint
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X))
    (c : M.markers → Fin ((2*S+1)^d))
    (hproper : ∀ u v,(markerProximityGraph M S free).Adj u v → c u ≠ c v)
    (hscale : ∀ i,32*((2*S+1)^d) ≤ L i) (x : X) (t : Lattice d) (i : Fin d) :
    ∀ n a,
      priorityCutIteration (fixedOrbitPriorityNeighborhood M hL S free c hproper (t +ᵥ x))
        (Nat.one_le_pow _ _ (by omega)) (hscale i) (fun g => g i) n a =
      ((priorityCutIteration (fixedOrbitPriorityNeighborhood M hL S free c hproper x)
        (Nat.one_le_pow _ _ (by omega)) (hscale i) (fun g => g i) n (a+t)).1-t i,
       (priorityCutIteration (fixedOrbitPriorityNeighborhood M hL S free c hproper x)
        (Nat.one_le_pow _ _ (by omega)) (hscale i) (fun g => g i) n (a+t)).2-t i) := by
  intro n
  induction n with
  | zero => intro a; simp only [priorityCutIteration,Pi.add_apply]; congr 1 <;> ring
  | succ n ih =>
      intro a
      have he := earlierPriorityCuts_repoint M hL S free c hproper x t a n i _ _ ih
      rw [priorityCutIteration,priorityCutIteration,
        fixedOrbitPriority_repoint M hL S free c hproper x t a]
      split_ifs
      · simp only [he]
        have hlo : a i-3*(L i : ℤ) = ((a+t) i-3*(L i : ℤ))+(-t i) := by simp; ring
        have hhi : a i+2*(L i : ℤ) = ((a+t) i+2*(L i : ℤ))+(-t i) := by simp; ring
        rw [hlo,hhi,selectedCut_translated,selectedCut_translated]
        rfl
      · exact ih a

end
end AbelianTargets
