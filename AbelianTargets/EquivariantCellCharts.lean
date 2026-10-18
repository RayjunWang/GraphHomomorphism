import AbelianTargets.ParitySwapGeometry

/-! Actual relation-polygon charts with the literal horizontal parity action. -/
namespace AbelianTargets.SupportTorsionData
noncomputable section
open scoped unitInterval
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
variable {V : Type*} [Fintype V]

def cellChart (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (p : Probability V) : SupportPair H :=
  SupportPair.paritySwap H c.1 (D.rawCellChart f c p)

theorem continuous_cellChart (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex) :
    Continuous (D.cellChart f c) :=
  (SupportPair.continuous_paritySwap H c.1).comp (D.continuous_rawCellChart f c)

theorem cellChart_lower_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (n : ℕ) (hn : n<2*D.power+1) (l r : V)
    (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 n)
    (hr : f r=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 (n+1)) (t : I) :
    D.cellChart f c (Probability.mix (Probability.dirac l) (Probability.dirac r) t)=
      SupportPair.paritySwap H (f l).1 (D.a t) := by
  unfold cellChart
  rw [D.rawCellChart_lower_edge f c n hn l r hl hr]
  rw [hl]
  change _=SupportPair.paritySwap H (c.1+(n:ℤ)*((2*D.power+1:ℕ):ℤ)^c.2) (D.a t)
  rw [SupportPair.paritySwap_lower_coordinate]
  by_cases hn : n%2=0
  · simp [hn]
  · simp [hn,D.b_swap]

theorem cellChart_upper_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (u v : V) (hu : f u=IntervalCarriers.upperLeft c.1 c.2)
    (hv : f v=IntervalCarriers.upperRight (2*D.power+1) c.1 c.2) (t : I) :
    D.cellChart f c (Probability.mix (Probability.dirac u) (Probability.dirac v) t)=
      SupportPair.paritySwap H (f u).1 (D.a t) := by
  unfold cellChart
  rw [D.rawCellChart_upper_edge f c u v hu hv,hu]
  rfl

theorem cellChart_left_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (l u : V) (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 0)
    (hu : f u=IntervalCarriers.upperLeft c.1 c.2) (t : I) :
    D.cellChart f c (Probability.mix (Probability.dirac l) (Probability.dirac u) t)=
      SupportPair.paritySwap H (f l).1 D.base := by
  unfold cellChart
  rw [D.rawCellChart_left_edge f c l u hl hu,hl]
  simp [IntervalCarriers.lowerVertex]

theorem cellChart_right_edge (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (l v : V) (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 (2*D.power+1))
    (hv : f v=IntervalCarriers.upperRight (2*D.power+1) c.1 c.2) (t : I) :
    D.cellChart f c (Probability.mix (Probability.dirac l) (Probability.dirac v) t)=
      SupportPair.paritySwap H (f l).1 D.base := by
  unfold cellChart
  rw [D.rawCellChart_right_edge f c l v hl hv,hl]
  change SupportPair.paritySwap H c.1 (SupportPair.swap H D.base)=
    SupportPair.paritySwap H (c.1+((2*D.power+1:ℕ):ℤ)*((2*D.power+1:ℕ):ℤ)^c.2) D.base
  rw [mul_comm,←pow_succ,SupportPair.paritySwap_odd_pow]
  by_cases hr : c.1%2=0 <;> simp [SupportPair.paritySwap,hr,SupportPair.swap_swap]

theorem cellChart_lower_vertex (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (n : ℕ) (hn : n≤2*D.power+1) (l : V)
    (hl : f l=IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 n) :
    D.cellChart f c (Probability.dirac l)=SupportPair.paritySwap H (f l).1 D.base := by
  unfold cellChart rawCellChart affineChart
  simp only [Probability.parameter_dirac,Function.comp_apply,hl,
    IntervalCarriers.cellHeight_lower,
    IntervalCarriers.cellTheta_lower D.power (2*D.power+1) (by omega)]
  rw [D.relationHomotopy.apply_zero]
  change SupportPair.paritySwap H c.1 ((alternatingOddPath D.a D.b D.power) (oddBreak D.power n))=
    SupportPair.paritySwap H (IntervalCarriers.lowerVertex (2*D.power+1) c.1 c.2 n).1 D.base
  by_cases hn' : n<2*D.power+1
  · have he := alternatingOddPath_on_slot D.a D.b D.power n hn' (0 : I)
    have hm : intervalMix (oddBreak D.power n) (oddBreak D.power (n+1)) 0=oddBreak D.power n := by
      apply Subtype.ext; simp [intervalMix]
    rw [hm] at he
    rw [he]
    simp only [Path.source]
    change _=SupportPair.paritySwap H (c.1+(n:ℤ)*((2*D.power+1:ℕ):ℤ)^c.2) D.base
    rw [SupportPair.paritySwap_lower_coordinate]
  · have he : n=2*D.power+1 := by omega
    subst n
    rw [oddBreak_last,(alternatingOddPath D.a D.b D.power).target]
    change SupportPair.paritySwap H c.1 (SupportPair.swap H D.base)=
      SupportPair.paritySwap H (c.1+((2*D.power+1:ℕ):ℤ)*((2*D.power+1:ℕ):ℤ)^c.2) D.base
    rw [mul_comm,←pow_succ,SupportPair.paritySwap_odd_pow]
    by_cases hr : c.1%2=0 <;> simp [SupportPair.paritySwap,hr,SupportPair.swap_swap]

theorem cellChart_upperLeft_vertex (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (u : V) (hu : f u=IntervalCarriers.upperLeft c.1 c.2) :
    D.cellChart f c (Probability.dirac u)=SupportPair.paritySwap H (f u).1 D.base := by
  unfold cellChart rawCellChart affineChart
  simp only [Probability.parameter_dirac,Function.comp_apply,hu,
    IntervalCarriers.cellHeight_upperLeft,IntervalCarriers.cellTheta_upperLeft,
    Path.Homotopy.source]
  rfl

theorem cellChart_upperRight_vertex (f : V → IntervalCarriers.Vertex) (c : IntervalCarriers.Vertex)
    (v : V) (hv : f v=IntervalCarriers.upperRight (2*D.power+1) c.1 c.2) :
    D.cellChart f c (Probability.dirac v)=SupportPair.paritySwap H (f v).1 D.base := by
  unfold cellChart rawCellChart affineChart
  simp only [Probability.parameter_dirac,Function.comp_apply,hv,
    IntervalCarriers.cellHeight_upperRight,
    IntervalCarriers.cellTheta_upperRight D.power (2*D.power+1) (by omega),
    Path.Homotopy.target]
  change SupportPair.paritySwap H c.1 (SupportPair.swap H D.base)=
    SupportPair.paritySwap H (c.1+((2*D.power+1:ℕ):ℤ)^(c.2+1)) D.base
  rw [SupportPair.paritySwap_odd_pow]
  by_cases hr : c.1%2=0 <;> simp [SupportPair.paritySwap,hr,SupportPair.swap_swap]

end
end AbelianTargets.SupportTorsionData
