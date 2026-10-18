import AbelianTargets.ActualMarkerAtlas

/-! Every nondegenerate side of an actual atlas cell is uniformly long.
Endpoint owners lie within twelve scales of one incident parent, so the
checked priority-cut separation applies at radius twenty-four. -/

namespace AbelianTargets
noncomputable section
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}

theorem ContinuousMarkerBoxes.GridCell.endpoint_owner
    {B : ContinuousMarkerBoxes M S} {x : X} {a : Lattice d} {R : RectangularCell d}
    (ha : a +ᵥ x ∈ M.markers) (hR : B.GridCell x a R) (i : Fin d) (s : Bool) :
    ∃ b : Lattice d,b +ᵥ x ∈ M.markers ∧
      (∀ j,|b j-a j| ≤ (6*L j : ℕ)) ∧
      ∃ t : Bool,cutSide (R.lower i,R.upper i) s = cutSide (B.cuts x b i) t := by
  have hm : cutSide (R.lower i,R.upper i) s ∈ B.localCutLevels x a i := by
    have hp := (mem_consecutivePairs _ _ _).mp (hR i).1
    cases s <;> simp only [cutSide,Bool.false_eq_true,if_false,if_true]
    · exact hp.1
    · exact hp.2.1
  obtain ⟨b,hb,he⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨hbmark,hclose⟩ := (mem_inactiveOrbitNeighbors_of_mem M 6 x a b ha).mp hb
  refine ⟨b,hbmark,hclose,?_⟩
  simp only [Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with he | he
  · exact ⟨false,by simpa only [cutSide,Bool.false_eq_true,if_false] using he⟩
  · exact ⟨true,by simpa only [cutSide,if_true] using he⟩

theorem ContinuousMarkerBoxes.GridCell.face_endpoint_owner
    {B : ContinuousMarkerBoxes M S} {x : X} {a : Lattice d} {R : RectangularCell d}
    (ha : a +ᵥ x ∈ M.markers) (hR : B.GridCell x a R)
    (z : RealCoordinates d) (i : Fin d) (s : Bool) :
    ∃ b : Lattice d,b +ᵥ x ∈ M.markers ∧
      (∀ j,|b j-a j| ≤ (6*L j : ℕ)) ∧
      ∃ t : Bool,cutSide ((R.faceAt z).lower i,(R.faceAt z).upper i) s =
        cutSide (B.cuts x b i) t := by
  cases s
  · by_cases he : z i = (R.upper i : ℝ)
    · simpa [cutSide,RectangularCell.faceAt,he] using hR.endpoint_owner ha i true
    · simpa [cutSide,RectangularCell.faceAt,he] using hR.endpoint_owner ha i false
  · by_cases he : z i = (R.lower i : ℝ)
    · simpa [cutSide,RectangularCell.faceAt,he] using hR.endpoint_owner ha i false
    · simpa [cutSide,RectangularCell.faceAt,he] using hR.endpoint_owner ha i true

theorem ContinuousMarkerBoxes.pointCell_endpoint_owner
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (hS : 6 ≤ S) (x : X)
    (z : RealCoordinates d) {a : Lattice d}
    (ha : a +ᵥ x ∈ M.markers) (hza : z ∈ (B.markerBox x a).closedBox)
    (i : Fin d) (s : Bool) :
    ∃ b : Lattice d,b +ᵥ x ∈ M.markers ∧
      (∀ j,|b j-a j| ≤ (12*L j : ℕ)) ∧
      ∃ t : Bool,cutSide (((B.tiling hL hS x).pointCell z).lower i,
        ((B.tiling hL hS x).pointCell z).upper i) s = cutSide (B.cuts x b i) t := by
  let T := B.tiling hL hS x
  have hex : ∃ R ∈ T.incidentFinset z,
      cutSide ((T.pointCell z).lower i,(T.pointCell z).upper i) s =
        cutSide ((R.faceAt z).lower i,(R.faceAt z).upper i) s := by
    cases s
    · obtain ⟨R,hR,he⟩ := (T.incidentFinset z).exists_mem_eq_sup'
        (T.incidentFinset_nonempty z) (fun R => (R.faceAt z).lower i)
      exact ⟨R,hR,he⟩
    · obtain ⟨R,hR,he⟩ := (T.incidentFinset z).exists_mem_eq_inf'
        (T.incidentFinset_nonempty z) (fun R => (R.faceAt z).upper i)
      exact ⟨R,hR,he⟩
  obtain ⟨R,hR,he⟩ := hex
  obtain ⟨⟨c,hc,hgrid,hkeep⟩,hzR⟩ := (T.mem_incidentFinset z R).mp hR
  have hzc := hgrid.subset_parent hzR
  have hcnear := B.parents_near_of_overlap x ha hc ⟨z,hza,hzc⟩
  have hcclose := ((mem_inactiveOrbitNeighbors_of_mem M 6 x a c ha).mp hcnear).2
  obtain ⟨b,hb,hbc,t,het⟩ := hgrid.face_endpoint_owner hc z i s
  refine ⟨b,hb,?_,t,he.trans het⟩
  intro j
  have hbabs := abs_add_le (b j-c j) (c j-a j)
  have hb := hbc j
  have hc := hcclose j
  have hid : b j-c j+(c j-a j) = b j-a j := by ring
  rw [hid] at hbabs
  push_cast at hb hc ⊢
  omega

theorem ContinuousMarkerBoxes.cutSide_same_owner_separated
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (x : X) (a : Lattice d)
    (i : Fin d) (s t : Bool)
    (hne : cutSide (B.cuts x a i) s ≠ cutSide (B.cuts x a i) t) :
    ((L i/(16*((2*S+1)^d)) : ℕ) : ℤ) <
      |cutSide (B.cuts x a i) s-cutSide (B.cuts x a i) t| := by
  have hdiv : ((L i/(16*((2*S+1)^d)) : ℕ) : ℤ) ≤ (L i : ℤ) :=
    by exact_mod_cast Nat.div_le_self (L i) (16*((2*S+1)^d))
  have hb := B.cuts_bounds x a i
  have hli : (1 : ℤ) ≤ L i := by exact_mod_cast hL i
  cases s <;> cases t <;> simp only [cutSide,Bool.false_eq_true,if_false,if_true] at hne ⊢
  · exact (hne rfl).elim
  · rw [abs_of_nonpos (by omega)]
    omega
  · rw [abs_of_nonneg (by omega)]
    omega
  · exact (hne rfl).elim

theorem ContinuousMarkerBoxes.atlas_side_bounds
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (hS : 24 ≤ S) (x : X)
    {R : RectangularCell d} (hR : R ∈ B.atlasCells hL (by omega) x)
    (i : Fin d) (hi : R.lower i < R.upper i) :
    ((L i/(16*((2*S+1)^d)) : ℕ) : ℤ) < R.upper i-R.lower i ∧
      R.upper i-R.lower i ≤ (6*L i : ℕ) := by
  obtain ⟨z,rfl⟩ := hR
  obtain ⟨a,hza⟩ := B.boxes_cover hL x z
  obtain ⟨b,hb,hba,s,he₁⟩ := B.pointCell_endpoint_owner hL (by omega) x z a.property hza i false
  obtain ⟨c,hc,hca,t,he₂⟩ := B.pointCell_endpoint_owner hL (by omega) x z a.property hza i true
  have hsep : ((L i/(16*((2*S+1)^d)) : ℕ) : ℤ) <
      |cutSide (B.cuts x b i) s-cutSide (B.cuts x c i) t| := by
    by_cases he : b = c
    · subst c
      apply B.cutSide_same_owner_separated hL x b i s t
      intro he
      simp only [cutSide,Bool.false_eq_true,if_false,if_true] at he₁ he₂
      unfold cutSide at he
      rw [← he₁,← he₂] at he
      exact (ne_of_lt hi) he
    · apply B.cuts_separated x b c hb hc he
      intro j
      have hh := abs_sub_le (c j) (a.val j) (b j)
      have hb := hba j
      have hc := hca j
      rw [abs_sub_comm (a.val j) (b j)] at hh
      have hs : (24*L j : ℕ) ≤ S*L j := Nat.mul_le_mul_right _ hS
      push_cast at hb hc hs ⊢
      omega
  simp only [cutSide,Bool.false_eq_true,if_false,if_true] at he₁ he₂
  unfold cutSide at hsep
  rw [← he₁,← he₂,abs_sub_comm,abs_of_nonneg (by omega)] at hsep
  exact ⟨hsep,(B.tiling hL (by omega) x).cells_bounded ⟨z,rfl⟩ i⟩

end
end AbelianTargets
