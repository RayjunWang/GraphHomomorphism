import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Finite consecutive integer cut levels and their closed-interval cover. -/

namespace AbelianTargets
noncomputable section

def consecutivePairs (D : Finset ℤ) : Finset (ℤ × ℤ) :=
  (D.product D).filter (fun p => p.1 < p.2 ∧ ∀ c ∈ D,¬(p.1 < c ∧ c < p.2))

@[simp] theorem mem_consecutivePairs (D : Finset ℤ) (a b : ℤ) :
    (a,b) ∈ consecutivePairs D ↔ a ∈ D ∧ b ∈ D ∧ a < b ∧
      ∀ c ∈ D,¬(a < c ∧ c < b) := by
  simp only [consecutivePairs,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product]
  tauto

theorem consecutivePair_bounds_of_point {D : Finset ℤ} {a b l u : ℤ} {z : ℝ}
    (hab : (a,b) ∈ consecutivePairs D) (hl : l ∈ D) (hu : u ∈ D)
    (haz : (a : ℝ) < z) (hzb : z < (b : ℝ))
    (hlz : (l : ℝ) ≤ z) (hzu : z ≤ (u : ℝ)) : l ≤ a ∧ b ≤ u := by
  obtain ⟨ha,hb,hab,hgap⟩ := (mem_consecutivePairs D a b).mp hab
  constructor
  · by_contra hn
    have hal : a < l := by omega
    have hlb : l < b := by exact_mod_cast hlz.trans_lt hzb
    exact hgap l hl ⟨hal,hlb⟩
  · by_contra hn
    have hub : u < b := by omega
    have hau : a < u := by exact_mod_cast haz.trans_le hzu
    exact hgap u hu ⟨hau,hub⟩

theorem consecutivePairs_disjoint_interiors {D : Finset ℤ} {a b c e : ℤ}
    (hab : (a,b) ∈ consecutivePairs D) (hce : (c,e) ∈ consecutivePairs D)
    {z : ℝ} (haz : (a : ℝ) < z) (hzb : z < (b : ℝ))
    (hcz : (c : ℝ) < z) (hze : z < (e : ℝ)) : a = c ∧ b = e := by
  have hc := (mem_consecutivePairs D c e).mp hce
  have ha := (mem_consecutivePairs D a b).mp hab
  have h₁ := consecutivePair_bounds_of_point hab hc.1 hc.2.1 haz hzb hcz.le hze.le
  have h₂ := consecutivePair_bounds_of_point hce ha.1 ha.2.1 hcz hze haz.le hzb.le
  omega

/-- Every point of an interval whose endpoints occur among the cut levels
lies in one of the consecutive closed intervals. Endpoint points are
included, without taking a closure of a punctured set. -/
theorem exists_consecutivePair_cover (D : Finset ℤ) (A B : ℤ)
    (hA : A ∈ D) (hB : B ∈ D) (hAB : A < B) (z : ℝ)
    (hAz : (A : ℝ) ≤ z) (hzB : z ≤ (B : ℝ)) :
    ∃ a b,(a,b) ∈ consecutivePairs D ∧ A ≤ a ∧ b ≤ B ∧
      (a : ℝ) ≤ z ∧ z ≤ (b : ℝ) := by
  classical
  by_cases hz : z = (B : ℝ)
  · subst z
    let F := D.filter (fun c => c < B)
    have hF : F.Nonempty := ⟨A,Finset.mem_filter.mpr ⟨hA,hAB⟩⟩
    let a := F.max' hF
    have haF : a ∈ F := F.max'_mem hF
    obtain ⟨haD,haB⟩ := Finset.mem_filter.mp haF
    have hAa : A ≤ a := F.le_max' A (Finset.mem_filter.mpr ⟨hA,hAB⟩)
    refine ⟨a,B,(mem_consecutivePairs D a B).mpr ⟨haD,hB,haB,?_⟩,
      hAa,le_rfl,?_,le_rfl⟩
    · intro c hc ⟨hac,hcB⟩
      have hca : c ≤ a := F.le_max' c (Finset.mem_filter.mpr ⟨hc,hcB⟩)
      omega
    · exact_mod_cast haB.le
  · have hzB' : z < (B : ℝ) := lt_of_le_of_ne hzB hz
    let F := D.filter (fun c : ℤ => (c : ℝ) ≤ z)
    let G := D.filter (fun c : ℤ => z < (c : ℝ))
    have hF : F.Nonempty := ⟨A,Finset.mem_filter.mpr ⟨hA,hAz⟩⟩
    have hG : G.Nonempty := ⟨B,Finset.mem_filter.mpr ⟨hB,hzB'⟩⟩
    let a := F.max' hF
    let b := G.min' hG
    obtain ⟨haD,haz⟩ := Finset.mem_filter.mp (F.max'_mem hF)
    obtain ⟨hbD,hzb⟩ := Finset.mem_filter.mp (G.min'_mem hG)
    have hab : a < b := by exact_mod_cast haz.trans_lt hzb
    have hAa : A ≤ a := F.le_max' A (Finset.mem_filter.mpr ⟨hA,hAz⟩)
    have hbB : b ≤ B := G.min'_le B (Finset.mem_filter.mpr ⟨hB,hzB'⟩)
    refine ⟨a,b,(mem_consecutivePairs D a b).mpr ⟨haD,hbD,hab,?_⟩,
      hAa,hbB,haz,hzb.le⟩
    intro c hc ⟨hac,hcb⟩
    by_cases hcz : (c : ℝ) ≤ z
    · have hca : c ≤ a := F.le_max' c (Finset.mem_filter.mpr ⟨hc,hcz⟩)
      omega
    · have hbc : b ≤ c := G.min'_le c (Finset.mem_filter.mpr ⟨hc,lt_of_not_ge hcz⟩)
      omega

end
end AbelianTargets
