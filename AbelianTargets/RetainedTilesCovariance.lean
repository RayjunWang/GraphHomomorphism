import AbelianTargets.ActualMarkerAtlas
import AbelianTargets.RectangularTranslation

namespace AbelianTargets
noncomputable section
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}

theorem ContinuousMarkerBoxes.cutSide_repoint (B : ContinuousMarkerBoxes M S)
    (x : X) (t a : Lattice d) (i : Fin d) (s : Bool) :
    cutSide (B.cuts (t +ᵥ x) a i) s = cutSide (B.cuts x (a+t) i) s-t i := by
  rw [B.cuts_repoint]
  cases s <;> rfl

theorem ContinuousMarkerBoxes.mem_localCutLevels_iff (B : ContinuousMarkerBoxes M S)
    (x : X) (a : Lattice d) (i : Fin d) (v : ℤ) :
    v ∈ B.localCutLevels x a i ↔
      ∃ b ∈ inactiveOrbitNeighbors M 6 x a,∃ s : Bool,v = cutSide (B.cuts x b i) s := by
  constructor
  · intro hv
    obtain ⟨b,hb,hv⟩ := Finset.mem_biUnion.mp hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · exact ⟨b,hb,false,hv⟩
    · exact ⟨b,hb,true,hv⟩
  · rintro ⟨b,hb,s,rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨b,hb,?_⟩
    cases s <;> simp [cutSide]

theorem ContinuousMarkerBoxes.mem_localCutLevels_repoint (B : ContinuousMarkerBoxes M S)
    (x : X) (t a : Lattice d) (i : Fin d) (v : ℤ) :
    v ∈ B.localCutLevels (t +ᵥ x) a i ↔ v+t i ∈ B.localCutLevels x (a+t) i := by
  rw [B.mem_localCutLevels_iff,B.mem_localCutLevels_iff]
  constructor
  · rintro ⟨b,hb,s,hv⟩
    refine ⟨b+t,(mem_inactiveOrbitNeighbors_repoint M 6 x t a b).mp hb,s,?_⟩
    rw [hv,B.cutSide_repoint]
    omega
  · rintro ⟨b,hb,s,hv⟩
    have hb' : b-t ∈ inactiveOrbitNeighbors M 6 (t +ᵥ x) a := by
      apply (mem_inactiveOrbitNeighbors_repoint M 6 x t a (b-t)).mpr
      simpa using hb
    refine ⟨b-t,hb',s,?_⟩
    rw [B.cutSide_repoint]
    simpa using (eq_sub_iff_add_eq.mpr hv)

theorem consecutivePairs_of_shift {D E : Finset ℤ} (t a b : ℤ)
    (hD : ∀ v,v ∈ D ↔ v+t ∈ E) :
    (a,b) ∈ consecutivePairs D ↔ (a+t,b+t) ∈ consecutivePairs E := by
  rw [mem_consecutivePairs,mem_consecutivePairs]
  constructor
  · rintro ⟨ha,hb,hab,hgap⟩
    refine ⟨(hD a).mp ha,(hD b).mp hb,by omega,?_⟩
    intro z hz hzz
    have hzD : z-t ∈ D := (hD (z-t)).mpr (by simpa using hz)
    exact hgap (z-t) hzD ⟨by omega,by omega⟩
  · rintro ⟨ha,hb,hab,hgap⟩
    refine ⟨(hD a).mpr ha,(hD b).mpr hb,by omega,?_⟩
    intro z hz hzz
    exact hgap (z+t) ((hD z).mp hz) ⟨by omega,by omega⟩

theorem ContinuousMarkerBoxes.GridCell_repoint (B : ContinuousMarkerBoxes M S)
    (x : X) (t a : Lattice d) (R : RectangularCell d) :
    B.GridCell (t +ᵥ x) a R ↔ B.GridCell x (a+t) (R.translate t) := by
  constructor <;> intro h i
  · have hi := h i
    refine ⟨(consecutivePairs_of_shift (t i) (R.lower i) (R.upper i)
      (B.mem_localCutLevels_repoint x t a i)).mp hi.1,?_⟩
    have hb := B.cuts_repoint x t a i
    rw [hb] at hi
    change (B.cuts x (a+t) i).1 ≤ R.lower i+t i ∧
      R.upper i+t i ≤ (B.cuts x (a+t) i).2
    exact ⟨by have hh:=hi.2.1; dsimp only at hh; omega,
      by have hh:=hi.2.2; dsimp only at hh; omega⟩
  · have hi := h i
    refine ⟨(consecutivePairs_of_shift (t i) (R.lower i) (R.upper i)
      (B.mem_localCutLevels_repoint x t a i)).mpr hi.1,?_⟩
    rw [B.cuts_repoint]
    change (B.cuts x (a+t) i).1-t i ≤ R.lower i ∧
      R.upper i ≤ (B.cuts x (a+t) i).2-t i
    have hlo := hi.2.1
    have hhi := hi.2.2
    change (B.cuts x (a+t) i).1 ≤ R.lower i+t i at hlo
    change R.upper i+t i ≤ (B.cuts x (a+t) i).2 at hhi
    omega

theorem ContinuousMarkerBoxes.markerBox_repoint (B : ContinuousMarkerBoxes M S)
    (x : X) (t a : Lattice d) :
    (B.markerBox (t +ᵥ x) a).translate t = B.markerBox x (a+t) := by
  apply RectangularCell.endpoint_pair_injective
  apply Prod.ext <;> funext i <;>
    simp [markerBox,RectangularCell.translate,B.cuts_repoint]

theorem disjoint_translated_rectangles (R Q : RectangularCell d) (t : Lattice d) :
    Disjoint (R.translate t).relativeInterior (Q.translate t).closedBox ↔
      Disjoint R.relativeInterior Q.closedBox := by
  constructor
  · intro h
    apply Set.disjoint_left.mpr
    intro z hzR hzQ
    exact Set.disjoint_left.mp h
      ((R.mem_relativeInterior_translate t z).mpr hzR)
      ((Q.mem_closedBox_translateCoordinates t z).mpr hzQ)
  · intro h
    apply Set.disjoint_left.mpr
    intro z hzR hzQ
    have hr : translateCoordinates (-t) z ∈ R.relativeInterior := by
      apply (R.mem_relativeInterior_translate t _).mp
      simpa only [translateCoordinates_cancel_neg] using hzR
    have hq : translateCoordinates (-t) z ∈ Q.closedBox := by
      apply (Q.mem_closedBox_translateCoordinates t _).mp
      simpa only [translateCoordinates_cancel_neg] using hzQ
    exact Set.disjoint_left.mp h hr hq

theorem ContinuousMarkerBoxes.Retained_repoint (B : ContinuousMarkerBoxes M S)
    (x : X) (t a : Lattice d) (R : RectangularCell d) :
    B.Retained (t +ᵥ x) a R ↔ B.Retained x (a+t) (R.translate t) := by
  constructor
  · rintro ⟨ha,hgrid,hkeep⟩
    refine ⟨by simpa only [add_vadd] using ha,(B.GridCell_repoint x t a R).mp hgrid,?_⟩
    intro b hb hp
    have hb' : (b-t) +ᵥ (t +ᵥ x) ∈ M.markers := by
      rw [← add_vadd,sub_add_cancel]
      exact hb
    have hp' : (B.priority (t +ᵥ x) (b-t)).val < (B.priority (t +ᵥ x) a).val := by
      simpa only [B.priority_repoint,sub_add_cancel] using hp
    have hd := (disjoint_translated_rectangles R (B.markerBox (t +ᵥ x) (b-t)) t).mpr
      (hkeep (b-t) hb' hp')
    simpa only [B.markerBox_repoint,sub_add_cancel] using hd
  · rintro ⟨ha,hgrid,hkeep⟩
    refine ⟨by simpa only [add_vadd] using ha,(B.GridCell_repoint x t a R).mpr hgrid,?_⟩
    intro b hb hp
    have hb' : (b+t) +ᵥ x ∈ M.markers := by simpa only [add_vadd] using hb
    have hp' : (B.priority x (b+t)).val < (B.priority x (a+t)).val := by
      simpa only [B.priority_repoint] using hp
    apply (disjoint_translated_rectangles R (B.markerBox (t +ᵥ x) b) t).mp
    simpa only [B.markerBox_repoint] using hkeep (b+t) hb' hp'

theorem ContinuousMarkerBoxes.retainedTiles_repoint (B : ContinuousMarkerBoxes M S)
    (x : X) (t : Lattice d) :
    (fun R : RectangularCell d => R.translate t) '' B.retainedTiles (t +ᵥ x) =
      B.retainedTiles x := by
  ext R
  constructor
  · rintro ⟨Q,⟨a,ha⟩,rfl⟩
    exact ⟨a+t,(B.Retained_repoint x t a Q).mp ha⟩
  · rintro ⟨a,ha⟩
    refine ⟨R.translate (-t),⟨a-t,?_⟩,R.translate_cancel_neg t⟩
    apply (B.Retained_repoint x t (a-t) (R.translate (-t))).mpr
    simpa only [sub_add_cancel,RectangularCell.translate_cancel_neg] using ha

end
end AbelianTargets
