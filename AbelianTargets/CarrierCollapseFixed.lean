import AbelianTargets.VerticalCarrierCollapse

set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets.IntervalCarriers
noncomputable section

theorem mass_zero_at_top {K : ℕ} {A B : ℤ} (p : Probability (CarrierVertex (K+1) A B))
    (hp : ∀ v, 0 < p.mass v → v.1.2 ≤ K) (v : CarrierVertex (K+1) A B) (hv : v.1.2 = K+1) :
    p.mass v = 0 := by
  apply le_antisymm _ (p.nonneg v)
  apply le_of_not_gt
  intro h
  have hh := hp v h
  omega

theorem top_mapList_fixes_lower {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Probability (CarrierVertex (K+1) A B)) (hp : ∀ v, 0 < p.mass v → v.1.2 ≤ K)
    (l : List (TopCell m K A B)) (t : unitInterval) : (topCollapseFamily hm).mapList l p t = p := by
  apply FreeCollapseFamily.mapList_fixes
  intro c hc
  exact Or.inl (mass_zero_at_top p hp (topTriangle hm c).a (by
    simp only [topTriangle,upperLeft,topCell_height c]))

theorem fan_mapList_fixes_lower {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hn : n < m)
    (p : Probability (CarrierVertex (K+1) A B)) (hp : ∀ v, 0 < p.mass v → v.1.2 ≤ K)
    (l : List (TopCell m K A B)) (t : unitInterval) : (fanCollapseFamily hm hn).mapList l p t = p := by
  apply FreeCollapseFamily.mapList_fixes
  intro c hc
  exact Or.inl (mass_zero_at_top p hp (fanTriangle hm hn c).a (by
    simp only [fanTriangle,upperLeft,topCell_height c]))

theorem verticalMap_fixes_lower {K : ℕ} {A B : ℤ}
    (p : Probability (CarrierVertex (K+1) A B)) (hp : ∀ v, 0 < p.mass v → v.1.2 ≤ K)
    (t : unitInterval) : verticalMap p t = p := by
  unfold verticalMap
  rw [Probability.push_eq_self floorVertex p (fun v hv => floorVertex_eq_self v (hp v hv))]
  exact Probability.mix_self _ _

end
end AbelianTargets.IntervalCarriers
