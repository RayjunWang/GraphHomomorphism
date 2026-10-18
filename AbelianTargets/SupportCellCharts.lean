import AbelianTargets.SupportRelationCharts
import AbelianTargets.TriangleChartIntersections

/-! A single continuous chart on each complete literal relation polygon. -/

namespace AbelianTargets
noncomputable section
open scoped unitInterval
attribute [local instance] Classical.propDecidable

namespace IntervalCarriers
def cellHeight (c v : Vertex) : I := if v.2=c.2+1 then 1 else 0
def cellTheta (k m : ℕ) (c v : Vertex) : I :=
  if v.2=c.2 then oddBreak k (((v.1-c.1)/(m : ℤ)^c.2).toNat)
  else if v.1=c.1 then 0 else 1

theorem cellHeight_lower (c : Vertex) (m n : ℕ) :
    cellHeight c (lowerVertex m c.1 c.2 n)=0 := by simp [cellHeight,lowerVertex]
theorem cellHeight_upperLeft (c : Vertex) : cellHeight c (upperLeft c.1 c.2)=1 := by
  simp [cellHeight,upperLeft]
theorem cellHeight_upperRight (c : Vertex) (m : ℕ) : cellHeight c (upperRight m c.1 c.2)=1 := by
  simp [cellHeight,upperRight]

theorem cellTheta_lower (k m : ℕ) (hm : 1≤m) (c : Vertex) (n : ℕ) :
    cellTheta k m c (lowerVertex m c.1 c.2 n)=oddBreak k n := by
  have hp : (m : ℤ)^c.2≠0 := pow_ne_zero _ (by exact_mod_cast (show m≠0 by omega))
  simp [cellTheta,lowerVertex,Int.mul_ediv_cancel _ hp]

theorem cellTheta_upperLeft (k m : ℕ) (c : Vertex) :
    cellTheta k m c (upperLeft c.1 c.2)=0 := by simp [cellTheta,upperLeft]
theorem cellTheta_upperRight (k m : ℕ) (hm : 1≤m) (c : Vertex) :
    cellTheta k m c (upperRight m c.1 c.2)=1 := by
  have hp : 0<(m : ℤ)^(c.2+1) := pow_pos (by exact_mod_cast (show 0<m by omega)) _
  simp [cellTheta,upperRight,show c.1+(m : ℤ)^(c.2+1)≠c.1 by omega]

theorem cellHeight_translate (a : ℤ) (c v : Vertex) :
    cellHeight (translate a c) (translate a v)=cellHeight c v := rfl
theorem cellTheta_translate (a : ℤ) (k m : ℕ) (c v : Vertex) :
    cellTheta k m (translate a c) (translate a v)=cellTheta k m c v := by
  simp [cellTheta,translate,add_sub_add_right_eq_sub]
end IntervalCarriers

namespace SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
variable {V : Type*} [Fintype V]

def rawCellChart (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex) :
    Probability V → SupportPair H :=
  D.affineChart (IntervalCarriers.cellHeight c ∘ f)
    (IntervalCarriers.cellTheta D.power (2*D.power+1) c ∘ f)

theorem continuous_rawCellChart (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex) :
    Continuous (D.rawCellChart f c) := D.continuous_affineChart _ _

theorem rawCellChart_lower_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (n : ℕ) (hn : n<2*D.power+1) (l r : V)
    (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 n)
    (hr : f r=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 (n+1)) (t : I) :
    D.rawCellChart f c (Probability.mix (Probability.dirac l) (Probability.dirac r) t)=
      if n%2=0 then D.a t else D.b t := by
  unfold rawCellChart affineChart
  rw [Probability.parameter_mix,Probability.parameter_mix]
  simp only [Probability.parameter_dirac,Function.comp_apply,hl,hr,
    IntervalCarriers.cellHeight_lower,
    IntervalCarriers.cellTheta_lower D.power (2*D.power+1) (by omega)]
  have hz : intervalMix 0 0 t=0 := by apply Subtype.ext; simp [intervalMix]
  rw [hz,D.relationHomotopy.apply_zero]
  exact alternatingOddPath_on_slot D.a D.b D.power n hn t

theorem rawCellChart_upper_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (u v : V) (hu : f u=IntervalCarriers.upperLeft c.1 c.2)
    (hv : f v=IntervalCarriers.upperRight (2*D.power+1) c.1 c.2) (t : I) :
    D.rawCellChart f c (Probability.mix (Probability.dirac u) (Probability.dirac v) t)=D.a t := by
  unfold rawCellChart affineChart
  rw [Probability.parameter_mix,Probability.parameter_mix]
  simp only [Probability.parameter_dirac,Function.comp_apply,hu,hv,
    IntervalCarriers.cellHeight_upperLeft,IntervalCarriers.cellHeight_upperRight,
    IntervalCarriers.cellTheta_upperLeft,
    IntervalCarriers.cellTheta_upperRight D.power (2*D.power+1) (by omega),intervalMix_zero_one]
  have ho : intervalMix 1 1 t=1 := by apply Subtype.ext; simp [intervalMix]
  rw [ho,D.relationHomotopy.apply_one]
  rfl

theorem rawCellChart_left_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (l u : V) (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 0)
    (hu : f u=IntervalCarriers.upperLeft c.1 c.2) (t : I) :
    D.rawCellChart f c (Probability.mix (Probability.dirac l) (Probability.dirac u) t)=D.base := by
  unfold rawCellChart affineChart
  rw [Probability.parameter_mix,Probability.parameter_mix]
  simp only [Probability.parameter_dirac,Function.comp_apply,hl,hu,
    IntervalCarriers.cellTheta_lower D.power (2*D.power+1) (by omega),
    IntervalCarriers.cellTheta_upperLeft,oddBreak_zero]
  have hz : intervalMix 0 0 t=0 := by apply Subtype.ext; simp [intervalMix]
  rw [hz,D.relationHomotopy.source]

theorem rawCellChart_right_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (l v : V) (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 (2*D.power+1))
    (hv : f v=IntervalCarriers.upperRight (2*D.power+1) c.1 c.2) (t : I) :
    D.rawCellChart f c (Probability.mix (Probability.dirac l) (Probability.dirac v) t)=
      SupportPair.swap H D.base := by
  unfold rawCellChart affineChart
  rw [Probability.parameter_mix,Probability.parameter_mix]
  simp only [Probability.parameter_dirac,Function.comp_apply,hl,hv,
    IntervalCarriers.cellTheta_lower D.power (2*D.power+1) (by omega),
    IntervalCarriers.cellTheta_upperRight D.power (2*D.power+1) (by omega),oddBreak_last]
  have ho : intervalMix 1 1 t=1 := by apply Subtype.ext; simp [intervalMix]
  rw [ho,D.relationHomotopy.target]

end SupportTorsionData
end
end AbelianTargets
