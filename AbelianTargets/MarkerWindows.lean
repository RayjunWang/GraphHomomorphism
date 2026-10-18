import AbelianTargets.Actions
import AbelianTargets.Dimension
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Finite separated marker windows

The finite target in Lemma 7.3 of arXiv:2609.39824v1. Its adjacency is
exactly the overlap relation (9), and looplessness is proved from marker
separation and coverage, rather than imposed in the definition.
-/

namespace AbelianTargets

noncomputable section

def markerBox (d L : ℕ) : Finset (Lattice d) :=
  Fintype.piFinset fun _ => Finset.Icc (-(2 * (L : ℤ))) (2 * (L : ℤ))

theorem mem_markerBox {d L : ℕ} (u : Lattice d) :
    u ∈ markerBox d L ↔ ∀ i, |u i| ≤ 2 * (L : ℤ) := by
  simp only [markerBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

def MarkerSeparated {d : ℕ} (L : ℕ) (D : Finset (Lattice d)) : Prop :=
  ∀ a ∈ D, ∀ b ∈ D, a ≠ b → ∃ i, (L : ℤ) < |a i - b i|

def MarkerCovering {d : ℕ} (L : ℕ) (D : Finset (Lattice d)) : Prop :=
  ∀ u : Lattice d, (∀ i, |u i| ≤ (L : ℤ)) →
    ∃ a ∈ D, ∀ i, |u i - a i| ≤ (L : ℤ)

/-- The exact finite vertex set in Lemma 7.3. -/
def MarkerPattern (d L : ℕ) :=
  {D : Finset (Lattice d) //
    D ⊆ markerBox d L ∧ MarkerSeparated L D ∧ MarkerCovering L D}

namespace MarkerPattern

variable {d L : ℕ}

instance : Finite (MarkerPattern d L) := by
  classical
  apply Finite.of_injective
    (fun D : MarkerPattern d L =>
      (⟨D.val, Finset.mem_powerset.mpr D.property.1⟩ :
        {s : Finset (Lattice d) // s ∈ (markerBox d L).powerset}))
  intro D E h
  apply Subtype.ext
  exact congrArg
    (fun t : {s : Finset (Lattice d) // s ∈ (markerBox d L).powerset} => t.val) h

noncomputable instance : Fintype (MarkerPattern d L) := Fintype.ofFinite _

instance : TopologicalSpace (MarkerPattern d L) := ⊥
instance : DiscreteTopology (MarkerPattern d L) := ⟨rfl⟩

theorem mem_box (D : MarkerPattern d L) {a : Lattice d} (ha : a ∈ D.val) :
    a ∈ markerBox d L := D.property.1 ha

theorem separated (D : MarkerPattern d L) : MarkerSeparated L D.val :=
  D.property.2.1

theorem covering (D : MarkerPattern d L) : MarkerCovering L D.val :=
  D.property.2.2

theorem central_marker (D : MarkerPattern d L) :
    ∃ a ∈ D.val, ∀ i, |a i| ≤ (L : ℤ) := by
  obtain ⟨a, ha, hclose⟩ := D.covering 0 (by intro i; simp)
  refine ⟨a, ha, ?_⟩
  simpa only [Pi.zero_apply, zero_sub, abs_neg] using hclose

theorem eq_of_close (D : MarkerPattern d L) {a b : Lattice d}
    (ha : a ∈ D.val) (hb : b ∈ D.val)
    (hclose : ∀ i, |a i - b i| ≤ (L : ℤ)) : a = b := by
  by_contra hne
  obtain ⟨i, hi⟩ := D.separated a ha b hb hne
  exact (not_lt_of_ge (hclose i)) hi

end MarkerPattern

def SignedUnit {d : ℕ} (g : Lattice d) : Prop :=
  ∃ i : Fin d, g = unitVector i ∨ g = -unitVector i

namespace SignedUnit

variable {d : ℕ} {g : Lattice d}

theorem neg (hg : SignedUnit g) : SignedUnit (-g) := by
  obtain ⟨i, rfl | rfl⟩ := hg
  · exact ⟨i, Or.inr rfl⟩
  · exact ⟨i, Or.inl (neg_neg _)⟩

theorem abs_coord_le_one (hg : SignedUnit g) (j : Fin d) : |g j| ≤ 1 := by
  obtain ⟨i, rfl | rfl⟩ := hg
  · simp only [unitVector]
    split <;> norm_num
  · simp only [Pi.neg_apply, abs_neg, unitVector]
    split <;> norm_num

theorem ne_zero (hg : SignedUnit g) : g ≠ 0 := by
  obtain ⟨i, rfl | rfl⟩ := hg
  · intro h
    have hi := congrFun h i
    simp [unitVector] at hi
  · intro h
    have hi := congrFun h i
    simp [unitVector] at hi

end SignedUnit

/-- Pointwise form of (9): on the intersection of the two windows,
membership agrees after translating by the edge displacement. -/
def WindowOverlap {d L : ℕ} (g : Lattice d)
    (D E : MarkerPattern d L) : Prop :=
  ∀ z, z ∈ markerBox d L → z - g ∈ markerBox d L →
    (z ∈ D.val ↔ z - g ∈ E.val)

theorem WindowOverlap.symm {d L : ℕ} {g : Lattice d}
    {D E : MarkerPattern d L} (h : WindowOverlap g D E) :
    WindowOverlap (-g) E D := by
  intro z hz hzg
  have hp : z + g ∈ markerBox d L := by simpa using hzg
  have hm : (z + g) - g ∈ markerBox d L := by simpa using hz
  simpa only [sub_neg_eq_add, add_sub_cancel_right] using (h (z + g) hp hm).symm

theorem central_sub_mem_box {d L : ℕ} (hL : 4 ≤ L)
    {a g : Lattice d} (ha : ∀ i, |a i| ≤ (L : ℤ))
    (hg : SignedUnit g) : a - g ∈ markerBox d L := by
  apply (mem_markerBox _).2
  intro i
  have hLi : (4 : ℤ) ≤ L := by exact_mod_cast hL
  have hai := abs_le.mp (ha i)
  have hgi := abs_le.mp (hg.abs_coord_le_one i)
  apply abs_le.mpr
  constructor <;> simp only [Pi.sub_apply] <;> omega

theorem WindowOverlap.marker_step {d L : ℕ} {g a : Lattice d}
    {D E : MarkerPattern d L} (h : WindowOverlap g D E)
    (ha : a ∈ D.val) (hbox : a - g ∈ markerBox d L) : a - g ∈ E.val :=
  (h a (D.mem_box ha) hbox).1 ha

/-- Different signed directions cannot witness the same oriented edge. -/
theorem WindowOverlap.unique_direction {d L : ℕ} (hL : 4 ≤ L)
    {g h : Lattice d} {D E : MarkerPattern d L}
    (hg : SignedUnit g) (hh : SignedUnit h)
    (hDE : WindowOverlap g D E) (hDE' : WindowOverlap h D E) : g = h := by
  obtain ⟨a, ha, hac⟩ := D.central_marker
  have hag := hDE.marker_step ha (central_sub_mem_box hL hac hg)
  have hah := hDE'.marker_step ha (central_sub_mem_box hL hac hh)
  have heq : a - g = a - h := E.eq_of_close hag hah (by
    intro i
    have hLi : (4 : ℤ) ≤ L := by exact_mod_cast hL
    have hgi := abs_le.mp (hg.abs_coord_le_one i)
    have hhi := abs_le.mp (hh.abs_coord_le_one i)
    apply abs_le.mpr
    constructor <;> simp only [Pi.sub_apply] <;> omega)
  funext i
  have hi := congrFun heq i
  simp only [Pi.sub_apply] at hi
  omega

theorem WindowOverlap.no_loop {d L : ℕ} (hL : 4 ≤ L)
    {g : Lattice d} {D : MarkerPattern d L} (hg : SignedUnit g) :
    ¬ WindowOverlap g D D := by
  intro h
  obtain ⟨a, ha, hac⟩ := D.central_marker
  have hag := h.marker_step ha (central_sub_mem_box hL hac hg)
  have heq : a = a - g := D.eq_of_close ha hag (by
    intro i
    have hLi : (4 : ℤ) ≤ L := by exact_mod_cast hL
    have hgi := abs_le.mp (hg.abs_coord_le_one i)
    apply abs_le.mpr
    constructor <;> simp only [Pi.sub_apply] <;> omega)
  apply hg.ne_zero
  funext i
  have hi := congrFun heq i
  simp only [Pi.sub_apply, Pi.zero_apply] at hi ⊢
  omega

theorem SignedUnit.sub_coord_bound {d : ℕ} {g a : Lattice d} {r : ℤ}
    (hg : SignedUnit g) (ha : ∀ i, |a i| ≤ r) :
    ∀ i, |(a - g) i| ≤ r + 1 := by
  intro i
  have hai := abs_le.mp (ha i)
  have hgi := abs_le.mp (hg.abs_coord_le_one i)
  apply abs_le.mpr
  constructor <;> simp only [Pi.sub_apply] <;> omega

/-- The sum of displacements on every closed four-walk is zero. -/
theorem WindowOverlap.four_walk {d L : ℕ} (hL : 4 ≤ L)
    {g₁ g₂ g₃ g₄ : Lattice d} {D E F G : MarkerPattern d L}
    (hg₁ : SignedUnit g₁) (hg₂ : SignedUnit g₂)
    (hg₃ : SignedUnit g₃) (hg₄ : SignedUnit g₄)
    (hDE : WindowOverlap g₁ D E) (hEF : WindowOverlap g₂ E F)
    (hFG : WindowOverlap g₃ F G) (hGD : WindowOverlap g₄ G D) :
    g₁ + g₂ + g₃ + g₄ = 0 := by
  obtain ⟨a, ha, hac⟩ := D.central_marker
  have hLi : (4 : ℤ) ≤ L := by exact_mod_cast hL
  have hb₁ := hg₁.sub_coord_bound hac
  have hb₂ := hg₂.sub_coord_bound hb₁
  have hb₃ := hg₃.sub_coord_bound hb₂
  have hb₄ := hg₄.sub_coord_bound hb₃
  have hbox₁ : a - g₁ ∈ markerBox d L :=
    (mem_markerBox _).2 (fun i => le_trans (hb₁ i) (by omega))
  have hbox₂ : a - g₁ - g₂ ∈ markerBox d L :=
    (mem_markerBox _).2 (fun i => le_trans (hb₂ i) (by omega))
  have hbox₃ : a - g₁ - g₂ - g₃ ∈ markerBox d L :=
    (mem_markerBox _).2 (fun i => le_trans (hb₃ i) (by omega))
  have hbox₄ : a - g₁ - g₂ - g₃ - g₄ ∈ markerBox d L :=
    (mem_markerBox _).2 (fun i => le_trans (hb₄ i) (by omega))
  have ha₁ := hDE.marker_step ha hbox₁
  have ha₂ := hEF.marker_step ha₁ hbox₂
  have ha₃ := hFG.marker_step ha₂ hbox₃
  have ha₄ := hGD.marker_step ha₃ hbox₄
  have heq : a = a - g₁ - g₂ - g₃ - g₄ := D.eq_of_close ha ha₄ (by
    intro i
    have h₁ := abs_le.mp (hg₁.abs_coord_le_one i)
    have h₂ := abs_le.mp (hg₂.abs_coord_le_one i)
    have h₃ := abs_le.mp (hg₃.abs_coord_le_one i)
    have h₄ := abs_le.mp (hg₄.abs_coord_le_one i)
    apply abs_le.mpr
    constructor <;> simp only [Pi.sub_apply] <;> omega)
  funext i
  have hi := congrFun heq i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at hi ⊢
  omega

private theorem unit_window_cover {d L : ℕ} (hL : 4 ≤ L)
    (i : Fin d) {z : Lattice d} (hz : z ∈ markerBox d L) :
    z + unitVector i ∈ markerBox d L ∨ z - unitVector i ∈ markerBox d L := by
  have hzi := abs_le.mp ((mem_markerBox _).1 hz i)
  have hLi : (4 : ℤ) ≤ L := by exact_mod_cast hL
  have hstep : |z i + 1| ≤ 2 * (L : ℤ) ∨ |z i - 1| ≤ 2 * (L : ℤ) := by
    simp only [abs_le]
    omega
  rcases hstep with hp | hm
  · left
    apply (mem_markerBox _).2
    intro j
    by_cases hji : j = i
    · subst j
      simpa [unitVector] using hp
    · simpa [unitVector, hji] using (mem_markerBox _).1 hz j
  · right
    apply (mem_markerBox _).2
    intro j
    by_cases hji : j = i
    · subst j
      simpa [unitVector] using hm
    · simpa [unitVector, hji] using (mem_markerBox _).1 hz j

/-- The middle window is covered by the two endpoint windows for a straight
two-step displacement. This is the inclusion used at the end of Lemma 7.3. -/
theorem SignedUnit.window_cover {d L : ℕ} (hL : 4 ≤ L)
    {g z : Lattice d} (hg : SignedUnit g) (hz : z ∈ markerBox d L) :
    z + g ∈ markerBox d L ∨ z - g ∈ markerBox d L := by
  obtain ⟨i, rfl | rfl⟩ := hg
  · exact unit_window_cover hL i hz
  · have h := unit_window_cover hL i hz
    simpa only [sub_neg_eq_add, ← sub_eq_add_neg] using h.symm

/-- The endpoints and displacement determine a straight walk's middle vertex. -/
theorem WindowOverlap.straight_middle_unique {d L : ℕ} (hL : 4 ≤ L)
    {g : Lattice d} {D E E' F : MarkerPattern d L} (hg : SignedUnit g)
    (hDE : WindowOverlap g D E) (hEF : WindowOverlap g E F)
    (hDE' : WindowOverlap g D E') (hE'F : WindowOverlap g E' F) : E = E' := by
  apply Subtype.ext
  apply Finset.ext
  intro z
  by_cases hz : z ∈ markerBox d L
  · obtain hp | hm := hg.window_cover hL hz
    · have hzm : z + g - g ∈ markerBox d L := by simpa using hz
      have h₁ := hDE (z + g) hp hzm
      have h₂ := hDE' (z + g) hp hzm
      simpa only [add_sub_cancel_right] using h₁.symm.trans h₂
    · exact (hEF z hz hm).trans (hE'F z hz hm).symm
  · have hnE : z ∉ E.val := fun h => hz (E.mem_box h)
    have hnE' : z ∉ E'.val := fun h => hz (E'.mem_box h)
    simp only [hnE, hnE']

/-- The graph `M_{d,L}` of Lemma 7.3, with exactly overlap adjacency. -/
def MarkerGraph (d L : ℕ) (hL : 4 ≤ L) : SimpleGraph (MarkerPattern d L) where
  Adj D E := ∃ g : Lattice d, SignedUnit g ∧ WindowOverlap g D E
  symm := by
    rintro D E ⟨g, hg, h⟩
    exact ⟨-g, hg.neg, h.symm⟩
  loopless := by
    constructor
    rintro D ⟨g, hg, h⟩
    exact WindowOverlap.no_loop hL hg h

theorem SignedDirection.isSignedUnit {d : ℕ} (s : SignedDirection d) :
    SignedUnit s.vector := by
  refine ⟨s.axis, ?_⟩
  cases hs : s.positive
  · right
    simp [SignedDirection.vector, hs]
  · left
    simp [SignedDirection.vector, hs]

theorem SignedUnit.exists_signedDirection {d : ℕ} {g : Lattice d}
    (hg : SignedUnit g) : ∃ s : SignedDirection d, s.vector = g := by
  obtain ⟨i, rfl | rfl⟩ := hg
  · exact ⟨⟨i, true⟩, rfl⟩
  · exact ⟨⟨i, false⟩, rfl⟩

theorem exists_markerDirection {d L : ℕ} {hL : 4 ≤ L}
    {D E : MarkerPattern d L} (h : (MarkerGraph d L hL).Adj D E) :
    ∃ s : SignedDirection d, WindowOverlap s.vector D E := by
  obtain ⟨g, hg, hDE⟩ := h
  obtain ⟨s, hs⟩ := hg.exists_signedDirection
  exact ⟨s, hs.symm ▸ hDE⟩

/-- The unique signed displacement of an actual oriented marker-graph edge. -/
def markerDirection {d L : ℕ} (hL : 4 ≤ L)
    {D E : MarkerPattern d L} (h : (MarkerGraph d L hL).Adj D E) :
    SignedDirection d := Classical.choose (exists_markerDirection h)

theorem markerDirection_overlap {d L : ℕ} (hL : 4 ≤ L)
    {D E : MarkerPattern d L} (h : (MarkerGraph d L hL).Adj D E) :
    WindowOverlap (markerDirection hL h).vector D E :=
  Classical.choose_spec (exists_markerDirection h)

theorem markerDirection_reverse {d L : ℕ} (hL : 4 ≤ L)
    {D E : MarkerPattern d L} (h : (MarkerGraph d L hL).Adj D E) :
    (markerDirection hL h.symm).vector = -(markerDirection hL h).vector :=
  WindowOverlap.unique_direction hL
    (markerDirection hL h.symm).isSignedUnit
    (markerDirection hL h).isSignedUnit.neg
    (markerDirection_overlap hL h.symm) (markerDirection_overlap hL h).symm

/-- Both structural direction laws in Lemma 7.3 hold for the actual finite
marker graph. The clopen-marker existence theorem is not used here. -/
def markerDirectionLaws (d L : ℕ) (hL : 4 ≤ L) :
    DirectionLaws (MarkerGraph d L hL) d where
  direction := markerDirection hL
  reverse := markerDirection_reverse hL
  four_walk := by
    intro D E F G hDE hEF hFG hGD
    exact WindowOverlap.four_walk hL
      (markerDirection hL hDE).isSignedUnit (markerDirection hL hEF).isSignedUnit
      (markerDirection hL hFG).isSignedUnit (markerDirection hL hGD).isSignedUnit
      (markerDirection_overlap hL hDE) (markerDirection_overlap hL hEF)
      (markerDirection_overlap hL hFG) (markerDirection_overlap hL hGD)
  straight_middle_unique := by
    intro D E E' F hDE hEF hDE' hE'F h₁ h₂ h₃
    apply WindowOverlap.straight_middle_unique hL (markerDirection hL hDE).isSignedUnit
    · exact markerDirection_overlap hL hDE
    · rw [h₁]
      exact markerDirection_overlap hL hEF
    · rw [h₂]
      exact markerDirection_overlap hL hDE'
    · rw [h₃]
      exact markerDirection_overlap hL hE'F

end

end AbelianTargets
