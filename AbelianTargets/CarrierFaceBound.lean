import AbelianTargets.CarrierGeometry

/-! Uniform simplex dimension, independent of the size of the carrier. -/

namespace AbelianTargets.IntervalCarriers

theorem carrierTriangle_card_le {m K : ℕ} {A B : ℤ} {s : Finset Vertex}
    (hs : s ∈ carrierTriangles m K A B) : s.card ≤ 3 := by
  obtain ⟨c,hc,hs⟩ := Finset.mem_biUnion.mp hs
  obtain rfl | hs := Finset.mem_insert.mp hs
  · exact Finset.card_le_three
  · obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.card_le_three

theorem CarrierFace.card_le_three {m K : ℕ} {A B : ℤ} {s : Finset Vertex}
    (hs : CarrierFace m K A B s) : s.card ≤ 3 := by
  rcases hs with ⟨v,hv,hsv⟩ | ⟨u,hu,v,hv,he,hsv⟩ | ⟨t,ht,hst⟩
  · exact (Finset.card_le_card hsv).trans (by simp)
  · exact (Finset.card_le_card hsv).trans (Finset.card_le_two.trans (by omega))
  · exact (Finset.card_le_card hst).trans (carrierTriangle_card_le ht)

theorem simplexFaces_card_le_three {m K : ℕ} {A B : ℤ}
    {s : Finset (CarrierVertex K A B)} (hs : s ∈ simplexFaces m K A B) : s.card ≤ 3 := by
  classical
  have hcard : (s.image Subtype.val).card=s.card :=
    Finset.card_image_of_injective s Subtype.val_injective
  rw [←hcard]
  exact ((mem_simplexFaces s).mp hs).card_le_three

end AbelianTargets.IntervalCarriers
