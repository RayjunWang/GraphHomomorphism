import AbelianTargets.CarrierGeometry
import Mathlib.Topology.MetricSpace.Lipschitz

set_option backward.isDefEq.respectTransparency false

/-!
# An explicit simplicial free-edge collapse

The two coordinates on a free edge lose their common minimum, and the
opposite vertex receives twice that amount. This is the literal PL
deformation onto the two retained sides of a triangle.
-/

namespace AbelianTargets.Probability

open scoped BigOperators NNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

def triangleCollapse (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) : Probability V := by
  classical
  let k := min (p.mass a) (p.mass b)
  refine ⟨fun v => p.mass v + (if v = c then 2*k else 0) -
    (if v = a then k else 0) - (if v = b then k else 0), ?_, ?_⟩
  · intro v
    have hk : 0 ≤ k := le_min (p.nonneg a) (p.nonneg b)
    have hka : k ≤ p.mass a := min_le_left _ _
    have hkb : k ≤ p.mass b := min_le_right _ _
    by_cases ha : v = a
    · subst v; simp only [hac, hab, if_false, if_true]; linarith
    by_cases hb : v = b
    · subst v; simp only [hbc, Ne.symm hab, if_false, if_true]; linarith
    by_cases hc : v = c
    · subst v; simp only [Ne.symm hac, Ne.symm hbc, if_false, if_true]; linarith [p.nonneg c]
    · simp only [ha,hb,hc,if_false,add_zero,sub_zero]; exact p.nonneg v
  · rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    simp only [p.sum_one,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    ring

theorem triangleCollapse_mass (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) (v : V) :
    (triangleCollapse a b c hab hac hbc p).mass v =
      p.mass v + (if v = c then 2*min (p.mass a) (p.mass b) else 0) -
        (if v = a then min (p.mass a) (p.mass b) else 0) -
          (if v = b then min (p.mass a) (p.mass b) else 0) := rfl

theorem triangleCollapse_fixes (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) (h : p.mass a = 0 ∨ p.mass b = 0) :
    triangleCollapse a b c hab hac hbc p = p := by
  have hk : min (p.mass a) (p.mass b) = 0 := by
    rcases h with h | h
    · rw [h,min_eq_left (p.nonneg b)]
    · rw [h,min_eq_right (p.nonneg a)]
  ext v
  rw [triangleCollapse_mass,hk]
  simp

theorem triangleCollapse_supported (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) (hp : p.SupportedOn ({a,b,c} : Set V)) :
    (triangleCollapse a b c hab hac hbc p).SupportedOn ({a,b,c} : Set V) := by
  apply supportedOn_iff_zero.mpr
  intro v hv
  have ha : v ≠ a := fun h => hv (by simp [h])
  have hb : v ≠ b := fun h => hv (by simp [h])
  have hc : v ≠ c := fun h => hv (by simp [h])
  rw [triangleCollapse_mass]
  simp only [ha,hb,hc,if_false,add_zero,sub_zero]
  exact supportedOn_iff_zero.mp hp v hv

theorem triangleCollapse_edge_removed (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) :
    (triangleCollapse a b c hab hac hbc p).mass a = 0 ∨
      (triangleCollapse a b c hab hac hbc p).mass b = 0 := by
  by_cases h : p.mass a ≤ p.mass b
  · left
    simp [triangleCollapse_mass,hac,hab,min_eq_left h]
  · right
    simp [triangleCollapse_mass,hbc,Ne.symm hab,min_eq_right (le_of_not_ge h)]

theorem continuous_triangleCollapse (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Continuous (triangleCollapse a b c hab hac hbc) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro v
  change Continuous (fun p : Probability V => p.mass v +
    (if v = c then 2*min (p.mass a) (p.mass b) else 0) -
      (if v = a then min (p.mass a) (p.mass b) else 0) -
        (if v = b then min (p.mass a) (p.mass b) else 0))
  have hk := (continuous_mass_apply a).min (continuous_mass_apply b)
  have hc : Continuous (fun p : Probability V => if v = c then 2*min (p.mass a) (p.mass b) else 0) := by
    split_ifs
    · exact continuous_const.mul hk
    · exact continuous_const
  have ha : Continuous (fun p : Probability V => if v = a then min (p.mass a) (p.mass b) else 0) := by
    split_ifs
    · exact hk
    · exact continuous_const
  have hb : Continuous (fun p : Probability V => if v = b then min (p.mass a) (p.mass b) else 0) := by
    split_ifs
    · exact hk
    · exact continuous_const
  exact (((continuous_mass_apply v).add hc).sub ha).sub hb

def triangleHomotopy (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) (t : unitInterval) : Probability V :=
  mix p (triangleCollapse a b c hab hac hbc p) t

@[simp] theorem triangleHomotopy_zero (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) : triangleHomotopy a b c hab hac hbc p 0 = p := mix_zero _ _

@[simp] theorem triangleHomotopy_one (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) : triangleHomotopy a b c hab hac hbc p 1 =
      triangleCollapse a b c hab hac hbc p := mix_one _ _

theorem continuous_triangleHomotopy (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Continuous (fun z : Probability V × unitInterval => triangleHomotopy a b c hab hac hbc z.1 z.2) :=
  continuous_mix_of_continuous continuous_fst
    ((continuous_triangleCollapse a b c hab hac hbc).comp continuous_fst) continuous_snd

theorem triangleHomotopy_fixes (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) (h : p.mass a = 0 ∨ p.mass b = 0) (t : unitInterval) :
    triangleHomotopy a b c hab hac hbc p t = p := by
  unfold triangleHomotopy
  rw [triangleCollapse_fixes a b c hab hac hbc p h,mix_self]

theorem triangleHomotopy_supported (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) (hp : p.SupportedOn ({a,b,c} : Set V)) (t : unitInterval) :
    (triangleHomotopy a b c hab hac hbc p t).SupportedOn ({a,b,c} : Set V) :=
  supportedOn_mix hp (triangleCollapse_supported a b c hab hac hbc p hp) t

theorem triangleHomotopy_track (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Probability V) : LipschitzWith 1 (triangleHomotopy a b c hab hac hbc p) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  change dist (FixedSlots.mix p.mass (triangleCollapse a b c hab hac hbc p).mass r)
    (FixedSlots.mix p.mass (triangleCollapse a b c hab hac hbc p).mass s) ≤ _
  exact (FixedSlots.mix_lipschitz _ _ 1 (dist_le_one _ _)).dist_le_mul r s

theorem triangleCollapse_lipschitz (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LipschitzWith 3 (triangleCollapse a b c hab hac hbc) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change dist (triangleCollapse a b c hab hac hbc p).mass
    (triangleCollapse a b c hab hac hbc q).mass ≤ 3*dist p q
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ 3*dist p q)).mpr
  intro v
  rw [Real.dist_eq,triangleCollapse_mass,triangleCollapse_mass]
  have hv : |p.mass v-q.mass v| ≤ dist p q := dist_le_pi_dist p.mass q.mass v
  have hk : |min (p.mass a) (p.mass b)-min (q.mass a) (q.mass b)| ≤ dist p q :=
    (abs_min_sub_min_le_max _ _ _ _).trans
      (max_le (dist_le_pi_dist p.mass q.mass a) (dist_le_pi_dist p.mass q.mass b))
  rw [abs_le] at hv hk
  have hd : (0 : ℝ) ≤ dist p q := dist_nonneg
  split_ifs <;> (try simp only [add_zero,sub_zero]) <;> rw [abs_le] <;> constructor <;> linarith

theorem triangleHomotopy_joint (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LipschitzWith 4 (fun z : Probability V × unitInterval => triangleHomotopy a b c hab hac hbc z.1 z.2) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨p,t⟩ ⟨q,s⟩
  have hspace : dist (triangleHomotopy a b c hab hac hbc p t)
      (triangleHomotopy a b c hab hac hbc q t) ≤ 3*dist p q := by
    have hd : (0 : ℝ) ≤ dist p q := dist_nonneg
    exact FixedSlots.mix_dist_le_of_le (a := p.mass) (b := q.mass)
      (c := (triangleCollapse a b c hab hac hbc p).mass)
      (d := (triangleCollapse a b c hab hac hbc q).mass) (Δ := 3*dist p q)
      (by change dist p q ≤ 3*dist p q; linarith)
      ((triangleCollapse_lipschitz a b c hab hac hbc).dist_le_mul p q) t
  have htime := (triangleHomotopy_track a b c hab hac hbc q).dist_le_mul t s
  have hpq : dist p q ≤ dist (p,t) (q,s) := by simp only [Prod.dist_eq]; exact le_max_left _ _
  have hts : dist t s ≤ dist (p,t) (q,s) := by simp only [Prod.dist_eq]; exact le_max_right _ _
  have htri := dist_triangle (triangleHomotopy a b c hab hac hbc p t)
    (triangleHomotopy a b c hab hac hbc q t) (triangleHomotopy a b c hab hac hbc q s)
  norm_num at htime ⊢
  linarith

end
end AbelianTargets.Probability
