import AbelianTargets.UpperCarrierFaces
import AbelianTargets.ParallelCollapse

set_option backward.isDefEq.respectTransparency false

/-! A simultaneous, continuous, speed-one collapse of all top horizontal
edges in the literal finite interval carrier. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section
attribute [local instance] Classical.propDecidable

def topCells (m K : ℕ) (A B : ℤ) : Finset Vertex :=
  (carrierCells m (K+1) A B).filter (fun c => c.2 = K)
abbrev TopCell (m K : ℕ) (A B : ℤ) := {c : Vertex // c ∈ topCells m K A B}
instance (m K : ℕ) (A B : ℤ) : Fintype (TopCell m K A B) :=
  Fintype.ofFinset (topCells m K A B) (by simp)

theorem topCell_cell {m K : ℕ} {A B : ℤ} (c : TopCell m K A B) :
    c.1 ∈ carrierCells m (K+1) A B := (Finset.mem_filter.mp c.2).1
theorem topCell_height {m K : ℕ} {A B : ℤ} (c : TopCell m K A B) : c.1.2 = K :=
  (Finset.mem_filter.mp c.2).2

def topTriangle {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (c : TopCell m K A B) :
    CollapseTriangle (CarrierVertex (K+1) A B) where
  a := ⟨upperLeft c.1.1 c.1.2,upperLeft_mem_of_cell (topCell_cell c)⟩
  b := ⟨upperRight m c.1.1 c.1.2,upperRight_mem_of_cell (topCell_cell c)⟩
  c := ⟨lowerVertex m c.1.1 c.1.2 m,lowerVertex_mem_of_cell (topCell_cell c) le_rfl⟩
  ab := fun h => upperLeft_ne_upperRight hm c.1.1 c.1.2 (congrArg Subtype.val h)
  ac := by intro h; have hh := congrArg (fun x => x.1.2) h; dsimp [upperLeft,lowerVertex] at hh; omega
  bc := by intro h; have hh := congrArg (fun x => x.1.2) h; dsimp [upperRight,lowerVertex] at hh; omega

theorem topTriangle_image {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (c : TopCell m K A B) :
    (topTriangle hm c).vertices.image Subtype.val = upperTriangle m c.1 := by
  ext v
  simp [CollapseTriangle.vertices,topTriangle,upperTriangle]
  tauto

theorem mem_topTriangle_iff {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (c : TopCell m K A B)
    (v : CarrierVertex (K+1) A B) :
    v ∈ (topTriangle hm c).vertices ↔ v.1 ∈ upperTriangle m c.1 := by
  rw [←topTriangle_image hm c]
  constructor
  · intro h; exact Finset.mem_image.mpr ⟨v,h,rfl⟩
  · rintro h
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
    have hwv : w = v := Subtype.ext he
    simpa only [hwv] using hw

def topCollapseFamily {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) :
    FreeCollapseFamily (simplexFaces m (K+1) A B) (TopCell m K A B) where
  triangle := topTriangle hm
  mem_face c := by
    apply (mem_simplexFaces _).mpr
    rw [topTriangle_image]
    exact Or.inr (Or.inr ⟨_,mem_carrierTriangles_upper (topCell_cell c),Finset.Subset.refl _⟩)
  free_edge c s hs ha hb := by
    have hs' := (mem_simplexFaces s).mp hs
    have ha' : upperLeft c.1.1 K ∈ s.image Subtype.val := by
      simpa only [topTriangle,topCell_height c] using
        (Finset.mem_image.mpr ⟨(topTriangle hm c).a,ha,rfl⟩ : (topTriangle hm c).a.1 ∈ s.image Subtype.val)
    have hb' : upperRight m c.1.1 K ∈ s.image Subtype.val := by
      simpa only [topTriangle,topCell_height c] using
        (Finset.mem_image.mpr ⟨(topTriangle hm c).b,hb,rfl⟩ : (topTriangle hm c).b.1 ∈ s.image Subtype.val)
    have hsub := upper_edge_free hm hs' ha' hb'
    intro v hv
    apply (mem_topTriangle_iff hm c v).mpr
    have hc : c.1 = (c.1.1,K) := Prod.ext rfl (topCell_height c)
    rw [hc]
    exact hsub (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  no_other_edge c d hcd := by
    by_contra h
    push Not at h
    have ha := (mem_topTriangle_iff hm c (topTriangle hm d).a).mp h.1
    have hb := (mem_topTriangle_iff hm c (topTriangle hm d).b).mp h.2
    have hc : c.1 = (c.1.1,K) := Prod.ext rfl (topCell_height c)
    have hd : d.1 = (d.1.1,K) := Prod.ext rfl (topCell_height d)
    change upperLeft d.1.1 d.1.2 ∈ upperTriangle m c.1 at ha
    change upperRight m d.1.1 d.1.2 ∈ upperTriangle m c.1 at hb
    rw [hc,topCell_height d] at ha hb
    have hr := upper_edge_origin_eq hm ha hb
    apply hcd
    apply Subtype.ext
    exact Prod.ext hr.symm ((topCell_height c).trans (topCell_height d).symm)

def collapseTop {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m (K+1) A B) (t : unitInterval) : Realization m (K+1) A B :=
  (topCollapseFamily hm).map (Finset.univ.toList) (Finset.nodup_toList _) p t

theorem continuous_collapseTop {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) :
    Continuous (fun z : Realization m (K+1) A B × unitInterval => collapseTop hm z.1 z.2) :=
  (topCollapseFamily hm).continuous_map _ (Finset.nodup_toList _)

theorem collapseTop_track {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B) :
    LipschitzWith 1 (collapseTop hm p) := (topCollapseFamily hm).map_track _ (Finset.nodup_toList _) p

theorem collapseTop_joint {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) :
    ∃ J : ℝ≥0, LipschitzWith J
      (fun z : Realization m (K+1) A B × unitInterval => collapseTop hm z.1 z.2) :=
  (topCollapseFamily hm).map_joint _ (Finset.nodup_toList _)

@[simp] theorem collapseTop_zero {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B) :
    collapseTop hm p 0 = p := (topCollapseFamily hm).map_zero _ (Finset.nodup_toList _) p

theorem collapseTop_removes {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B)
    (c : TopCell m K A B) :
    (collapseTop hm p 1).1.mass (topTriangle hm c).a = 0 ∨
      (collapseTop hm p 1).1.mass (topTriangle hm c).b = 0 :=
  (topCollapseFamily hm).map_one_removes _ (Finset.nodup_toList _) p c (by simp)

end
end AbelianTargets.IntervalCarriers
