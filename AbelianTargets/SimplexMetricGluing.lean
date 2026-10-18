import AbelianTargets.SupportGeometry
import Mathlib.Tactic.FieldSimp

/-!
# A common-face estimate for finite probability simplices

Two nearby probability points have a normalized coordinatewise minimum
supported in both of their support sets. This quantitative fact permits
Lipschitz estimates on simplex charts to be glued without an intrinsic-metric
assumption. The image diameter handles pairs with disjoint supports.
-/

namespace AbelianTargets

open scoped BigOperators NNReal

noncomputable section

namespace Probability

variable {V : Type*} [Fintype V]

def overlapMass (p q : Probability V) : ℝ := ∑ v, min (p.mass v) (q.mass v)

theorem overlapMass_nonneg (p q : Probability V) : 0 ≤ overlapMass p q :=
  Finset.sum_nonneg fun v _ => le_min (p.nonneg v) (q.nonneg v)

theorem overlapMass_le_one (p q : Probability V) : overlapMass p q ≤ 1 := by
  calc
    overlapMass p q ≤ ∑ v, p.mass v := Finset.sum_le_sum fun v _ => min_le_left _ _
    _ = 1 := p.sum_one

theorem mass_dist_le (p q : Probability V) (v : V) :
    |p.mass v - q.mass v| ≤ dist p q := by
  exact (dist_le_pi_dist p.mass q.mass v)

theorem one_sub_overlapMass_le (p q : Probability V) :
    1 - overlapMass p q ≤ (Fintype.card V : ℝ) * dist p q := by
  have he : 1 - overlapMass p q = ∑ v, (p.mass v - min (p.mass v) (q.mass v)) := by
    rw [Finset.sum_sub_distrib, p.sum_one]
    rfl
  rw [he]
  calc
    _ ≤ ∑ _v : V, dist p q := Finset.sum_le_sum fun v _ => by
      have hd := mass_dist_le p q v
      rw [abs_le] at hd
      by_cases h : p.mass v ≤ q.mass v
      · rw [min_eq_left h, sub_self]; exact dist_nonneg
      · rw [min_eq_right (le_of_not_ge h)]
        exact hd.2
    _ = (Fintype.card V : ℝ) * dist p q := by simp

def commonPoint (p q : Probability V) (h : 0 < overlapMass p q) : Probability V where
  mass v := min (p.mass v) (q.mass v) / overlapMass p q
  nonneg v := div_nonneg (le_min (p.nonneg v) (q.nonneg v)) h.le
  sum_one := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    exact mul_inv_cancel₀ (ne_of_gt h)

theorem commonPoint_supportedOn_left (p q : Probability V) (h : 0 < overlapMass p q)
    {A : Set V} (hp : p.SupportedOn A) : (commonPoint p q h).SupportedOn A := by
  intro v hv
  have hv' : 0 < min (p.mass v) (q.mass v) :=
    (div_pos_iff_of_pos_right h).mp hv
  exact hp v (hv'.trans_le (min_le_left _ _))

theorem commonPoint_supportedOn_right (p q : Probability V) (h : 0 < overlapMass p q)
    {A : Set V} (hq : q.SupportedOn A) : (commonPoint p q h).SupportedOn A := by
  intro v hv
  have hv' : 0 < min (p.mass v) (q.mass v) :=
    (div_pos_iff_of_pos_right h).mp hv
  exact hq v (hv'.trans_le (min_le_right _ _))

theorem dist_commonPoint_left (p q : Probability V) (h : 0 < overlapMass p q) :
    dist p (commonPoint p q h) ≤ ((Fintype.card V : ℝ) + 1) * dist p q := by
  change dist p.mass (commonPoint p q h).mass ≤ _
  apply (dist_pi_le_iff (by positivity :
    0 ≤ ((Fintype.card V : ℝ) + 1) * dist p q)).2
  intro v
  rw [Real.dist_eq, abs_le]
  have hm : 0 ≤ min (p.mass v) (q.mass v) := le_min (p.nonneg v) (q.nonneg v)
  have hs : overlapMass p q ≤ 1 := overlapMass_le_one p q
  have hms : min (p.mass v) (q.mass v) ≤ overlapMass p q :=
    Finset.single_le_sum (fun w _ => le_min (p.nonneg w) (q.nonneg w)) (Finset.mem_univ v)
  have hmass : min (p.mass v) (q.mass v) / overlapMass p q ≤ 1 :=
    (div_le_one h).2 hms
  have hmin : min (p.mass v) (q.mass v) ≤
      min (p.mass v) (q.mass v) / overlapMass p q := by
    apply (le_div_iff₀ h).2
    exact mul_le_of_le_one_right hm hs
  have hd := mass_dist_le p q v
  have hdelta : p.mass v - min (p.mass v) (q.mass v) ≤ dist p q := by
    by_cases hv : p.mass v ≤ q.mass v
    · rw [min_eq_left hv, sub_self]; exact dist_nonneg
    · rw [min_eq_right (le_of_not_ge hv)]
      exact (abs_le.mp hd).2
  have hnorm : min (p.mass v) (q.mass v) / overlapMass p q -
      min (p.mass v) (q.mass v) ≤ 1 - overlapMass p q := by
    have hid : min (p.mass v) (q.mass v) / overlapMass p q -
        min (p.mass v) (q.mass v) =
        (min (p.mass v) (q.mass v) / overlapMass p q) * (1 - overlapMass p q) := by
      field_simp
    rw [hid]
    exact mul_le_of_le_one_left (sub_nonneg.mpr hs) hmass
  have hloss := one_sub_overlapMass_le p q
  change -(((Fintype.card V : ℝ) + 1) * dist p q) ≤
      p.mass v - min (p.mass v) (q.mass v) / overlapMass p q ∧
      p.mass v - min (p.mass v) (q.mass v) / overlapMass p q ≤ _
  constructor <;> nlinarith [min_le_left (p.mass v) (q.mass v), dist_nonneg (x := p) (y := q)]

theorem dist_commonPoint_right (p q : Probability V) (h : 0 < overlapMass p q) :
    dist q (commonPoint p q h) ≤ ((Fintype.card V : ℝ) + 1) * dist p q := by
  have hs : overlapMass q p = overlapMass p q := by
    unfold overlapMass; simp only [min_comm]
  have he : commonPoint q p (hs.symm ▸ h) = commonPoint p q h := by
    ext v; simp [commonPoint, hs, min_comm]
  simpa only [he, dist_comm q p] using dist_commonPoint_left q p (hs.symm ▸ h)

end Probability

/-- The literal union of a finite collection of probability-simplex faces. -/
abbrev SimplicialCarrier {V : Type*} [Fintype V] (F : Finset (Finset V)) :=
  {p : Probability V // ∃ s ∈ F, p.SupportedOn (s : Set V)}

/-- Uniform simplex-chart estimates and a bounded image give a global ambient
Lipschitz estimate. Agreement on overlaps is automatic because `f` is a single
function on the literal face union. No connectedness assumption is needed. -/
theorem lipschitz_simplicialCarrier {V Z : Type*} [Fintype V] [MetricSpace Z]
    (F : Finset (Finset V)) (f : SimplicialCarrier F → Z) (L C : ℝ≥0)
    (hdiam : ∀ p q, dist (f p) (f q) ≤ C)
    (hface : ∀ s ∈ F, ∀ p q : SimplicialCarrier F,
      p.1.SupportedOn (s : Set V) → q.1.SupportedOn (s : Set V) →
      dist (f p) (f q) ≤ L * dist p q) :
    LipschitzWith (2 * (Fintype.card V + 1) * L + Fintype.card V * C) f := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro p q
  let n : ℝ := Fintype.card V
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hδ : 0 ≤ dist p q := dist_nonneg
  by_cases hs : 0 < Probability.overlapMass p.1 q.1
  · obtain ⟨s, hsF, hps⟩ := p.2
    obtain ⟨t, htF, hqt⟩ := q.2
    let r : SimplicialCarrier F :=
      ⟨Probability.commonPoint p.1 q.1 hs, s, hsF,
        Probability.commonPoint_supportedOn_left p.1 q.1 hs hps⟩
    have hrs : r.1.SupportedOn (s : Set V) :=
      Probability.commonPoint_supportedOn_left p.1 q.1 hs hps
    have hrt : r.1.SupportedOn (t : Set V) :=
      Probability.commonPoint_supportedOn_right p.1 q.1 hs hqt
    have hpr : dist p r ≤ (n + 1) * dist p q :=
      Probability.dist_commonPoint_left p.1 q.1 hs
    have hqr : dist q r ≤ (n + 1) * dist p q :=
      Probability.dist_commonPoint_right p.1 q.1 hs
    have hfpr := hface s hsF p r hps hrs
    have hfqr := hface t htF q r hqt hrt
    have hb : dist (f p) (f q) ≤ 2 * (n + 1) * L * dist p q := by
      calc
        _ ≤ dist (f p) (f r) + dist (f r) (f q) := dist_triangle _ _ _
        _ = dist (f p) (f r) + dist (f q) (f r) := by rw [dist_comm (f r) (f q)]
        _ ≤ L * dist p r + L * dist q r := add_le_add hfpr hfqr
        _ ≤ L * ((n+1) * dist p q) + L * ((n+1) * dist p q) :=
          add_le_add (mul_le_mul_of_nonneg_left hpr L.2)
            (mul_le_mul_of_nonneg_left hqr L.2)
        _ = _ := by ring
    have hnc : 0 ≤ n * C * dist p q := by positivity
    change dist (f p) (f q) ≤
      (2 * ((Fintype.card V : ℝ) + 1) * L + (Fintype.card V : ℝ) * C) * dist p q
    dsimp [n] at hb hnc
    nlinarith
  · have hzero : Probability.overlapMass p.1 q.1 = 0 :=
      le_antisymm (le_of_not_gt hs) (Probability.overlapMass_nonneg p.1 q.1)
    have hlarge : 1 ≤ n * dist p q := by
      simpa only [hzero, sub_zero] using Probability.one_sub_overlapMass_le p.1 q.1
    have hb := hdiam p q
    have hlarge' := mul_le_mul_of_nonneg_left hlarge C.2
    have hnonneg : 0 ≤ 2 * (n + 1) * L * dist p q := by positivity
    change dist (f p) (f q) ≤
      (2 * ((Fintype.card V : ℝ) + 1) * L + (Fintype.card V : ℝ) * C) * dist p q
    dsimp [n] at hlarge' hnonneg
    nlinarith

end

end AbelianTargets
