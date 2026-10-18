import AbelianTargets.LowerCarrierCollapse

set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets.IntervalCarriers
noncomputable section
attribute [local instance] Classical.propDecidable

theorem FanAdmissible.downward {m K t : ℕ} {A B : ℤ} {s u : Finset Vertex}
    (hs : FanAdmissible m K A B t s) (hu : u ⊆ s) : FanAdmissible m K A B t u := by
  constructor
  · intro c h; exact hs.1 c ⟨hu h.1,hu h.2⟩
  · intro c k hk hkm h; exact hs.2 c k hk hkm ⟨hu h.1,hu h.2⟩

theorem fanFaces_downward {m K t : ℕ} {A B : ℤ} {s u : Finset (CarrierVertex (K+1) A B)}
    (hs : s ∈ fanFaces m K A B t) (hu : u ⊆ s) : u ∈ fanFaces m K A B t := by
  obtain ⟨hs,ha⟩ := (mem_fanFaces s).mp hs
  exact (mem_fanFaces u).mpr ⟨simplexFaces_downward hs hu,ha.downward (Finset.image_subset_image hu)⟩

theorem positiveSupport_mem_fan {m K t : ℕ} {A B : ℤ}
    (p : SimplicialCarrier (fanFaces m K A B t)) : p.1.positiveSupport ∈ fanFaces m K A B t := by
  obtain ⟨s,hs,hp⟩ := p.2
  exact fanFaces_downward hs (p.1.positiveSupport_subset hp)

theorem mem_positiveSupport_image {K : ℕ} {A B : ℤ} (p : Probability (CarrierVertex K A B))
    (v : CarrierVertex K A B) : v.1 ∈ p.positiveSupport.image Subtype.val ↔ 0 < p.mass v := by
  constructor
  · intro h
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
    have hv : w = v := Subtype.ext he
    simpa only [hv] using (Probability.mem_positiveSupport p w).mp hw
  · intro h
    exact Finset.mem_image.mpr ⟨v,(Probability.mem_positiveSupport p v).mpr h,rfl⟩

theorem collapseTop_terminal {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B) :
    (collapseTop hm p 1).1.positiveSupport ∈ fanFaces m K A B m := by
  apply (mem_fanFaces _).mpr
  refine ⟨positiveSupport_mem _,?_,?_⟩
  · intro c h
    have ha : 0 < (collapseTop hm p 1).1.mass (topTriangle hm c).a :=
      (mem_positiveSupport_image _ (topTriangle hm c).a).mp h.1
    have hb : 0 < (collapseTop hm p 1).1.mass (topTriangle hm c).b :=
      (mem_positiveSupport_image _ (topTriangle hm c).b).mp h.2
    rcases collapseTop_removes hm p c with hz | hz
    · rw [hz] at ha; exact lt_irrefl _ ha
    · rw [hz] at hb; exact lt_irrefl _ hb
  · intro c k hk hkm
    omega

def initialFan {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B) :
    SimplicialCarrier (fanFaces m K A B m) :=
  ⟨(collapseTop hm p 1).1,_,collapseTop_terminal hm p,
    Probability.supportedOn_positiveSupport _⟩

theorem continuous_initialFan {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) : Continuous (initialFan (K := K) (A := A) (B := B) hm) :=
  (continuous_subtype_val.comp ((continuous_collapseTop hm).comp
    (continuous_id.prodMk continuous_const))).subtype_mk _

theorem collapseFan_terminal {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hn : n < m)
    (p : SimplicialCarrier (fanFaces m K A B (n+1))) :
    (collapseFan hm hn p 1).1.positiveSupport ∈ fanFaces m K A B n := by
  obtain ⟨hs,hallowed⟩ := (mem_fanFaces _).mp (positiveSupport_mem_fan (collapseFan hm hn p 1))
  apply (mem_fanFaces _).mpr
  refine ⟨hs,hallowed.1,?_⟩
  intro c k hk hkm h
  by_cases hkn : k = n
  · subst k
    have ha : 0 < (collapseFan hm hn p 1).1.mass (fanTriangle hm hn c).a :=
      (mem_positiveSupport_image _ (fanTriangle hm hn c).a).mp h.1
    have hb : 0 < (collapseFan hm hn p 1).1.mass (fanTriangle hm hn c).b :=
      (mem_positiveSupport_image _ (fanTriangle hm hn c).b).mp h.2
    rcases collapseFan_removes hm hn p c with hz | hz
    · rw [hz] at ha; exact lt_irrefl _ ha
    · rw [hz] at hb; exact lt_irrefl _ hb
  · exact hallowed.2 c k (by omega) hkm h

def fanRetraction {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hn : n < m)
    (p : SimplicialCarrier (fanFaces m K A B (n+1))) : SimplicialCarrier (fanFaces m K A B n) :=
  ⟨(collapseFan hm hn p 1).1,_,collapseFan_terminal hm hn p,
    Probability.supportedOn_positiveSupport _⟩

theorem continuous_fanRetraction {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hn : n < m) :
    Continuous (fanRetraction (K := K) (A := A) (B := B) hm hn) :=
  (continuous_subtype_val.comp ((continuous_collapseFan hm hn).comp
    (continuous_id.prodMk continuous_const))).subtype_mk _

end
end AbelianTargets.IntervalCarriers
