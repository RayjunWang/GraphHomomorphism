import AbelianTargets.ProbabilityParameters

/-! Explicit barycentric charts filling the odd Baumslag--Solitar relation. -/

namespace AbelianTargets
noncomputable section
open scoped unitInterval
attribute [local instance] Classical.propDecidable

namespace SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)

def relationHomotopy : (alternatingOddPath D.a D.b D.power).Homotopy D.a :=
  Classical.choice D.alternating_odd_null

variable {V : Type*} [Fintype V]

def affineChart (height theta : V → I) (p : Probability V) : SupportPair H :=
  D.relationHomotopy (Probability.parameter height p,Probability.parameter theta p)

theorem continuous_affineChart (height theta : V → I) :
    Continuous (D.affineChart height theta) :=
  D.relationHomotopy.continuous.comp
    ((Probability.continuous_parameter height).prodMk (Probability.continuous_parameter theta))

theorem affineChart_eq_on_support (height theta height' theta' : V → I)
    (p : Probability V) (s : Set V) (hp : p.SupportedOn s)
    (hh : ∀v∈s,height v=height' v) (ht : ∀v∈s,theta v=theta' v) :
    D.affineChart height theta p=D.affineChart height' theta' p := by
  unfold affineChart
  rw [Probability.parameter_eq_on_support p s hp hh,
    Probability.parameter_eq_on_support p s hp ht]

def lowerHeight (u : V) (v : V) : I := if v=u then 1 else 0
def lowerTheta (l r : V) (n : ℕ) (v : V) : I :=
  if v=l then oddBreak D.power n else if v=r then oddBreak D.power (n+1) else 0

def lowerChart (u l r : V) (n : ℕ) :=
  D.affineChart (lowerHeight u) (D.lowerTheta l r n)

def upperHeight (u v : V) (w : V) : I := if w=u ∨ w=v then 1 else 0
def upperTheta (l v : V) (w : V) : I := if w=l ∨ w=v then 1 else 0
def upperChart (u l v : V) := D.affineChart (upperHeight u v) (upperTheta l v)

theorem continuous_lowerChart (u l r : V) (n : ℕ) : Continuous (D.lowerChart u l r n) :=
  D.continuous_affineChart _ _
theorem continuous_upperChart (u l v : V) : Continuous (D.upperChart u l v) :=
  D.continuous_affineChart _ _

theorem lowerChart_bottom (u l r : V) (hul : u≠l) (hur : u≠r) (hlr : l≠r)
    (n : ℕ) (hn : n<2*D.power+1) (t : I) :
    D.lowerChart u l r n (Probability.mix (Probability.dirac l) (Probability.dirac r) t)=
      if n%2=0 then D.a t else D.b t := by
  classical
  unfold lowerChart affineChart
  rw [Probability.parameter_mix,Probability.parameter_mix]
  simp only [Probability.parameter_dirac]
  have hh : lowerHeight u l=0 ∧ lowerHeight u r=0 := by simp [lowerHeight,hul.symm,hur.symm]
  have ht : D.lowerTheta l r n l=oddBreak D.power n ∧
      D.lowerTheta l r n r=oddBreak D.power (n+1) := by simp [lowerTheta,hlr.symm]
  rw [hh.1,hh.2,ht.1,ht.2]
  have hz : intervalMix 0 0 t=0 := by apply Subtype.ext; simp [intervalMix]
  rw [hz,D.relationHomotopy.apply_zero]
  exact alternatingOddPath_on_slot D.a D.b D.power n hn t

theorem upperChart_top (u l v : V) (hul : u≠l) (huv : u≠v) (hlv : l≠v) (t : I) :
    D.upperChart u l v (Probability.mix (Probability.dirac u) (Probability.dirac v) t)=D.a t := by
  classical
  unfold upperChart affineChart
  rw [Probability.parameter_mix,Probability.parameter_mix]
  simp only [Probability.parameter_dirac]
  have hh : upperHeight u v u=1 ∧ upperHeight u v v=1 := by simp [upperHeight]
  have ht : upperTheta l v u=0 ∧ upperTheta l v v=1 := by simp [upperTheta,hul,huv]
  rw [hh.1,hh.2,ht.1,ht.2,intervalMix_zero_one]
  have ho : intervalMix 1 1 t=1 := by apply Subtype.ext; simp [intervalMix]
  rw [ho,D.relationHomotopy.apply_one]
  rfl

theorem lowerChart_left (u l r : V) (hul : u≠l) (hur : u≠r) (hlr : l≠r) (t : I) :
    D.lowerChart u l r 0 (Probability.mix (Probability.dirac l) (Probability.dirac u) t)=D.base := by
  classical
  unfold lowerChart affineChart
  rw [Probability.parameter_mix,Probability.parameter_mix]
  simp only [Probability.parameter_dirac]
  have ht : D.lowerTheta l r 0 l=0 ∧ D.lowerTheta l r 0 u=0 := by
    simp [lowerTheta,hul,hur]
  rw [ht.1,ht.2]
  have hz : intervalMix 0 0 t=0 := by apply Subtype.ext; simp [intervalMix]
  rw [hz,D.relationHomotopy.source]

theorem upperChart_right (u l v : V) (hul : u≠l) (huv : u≠v) (hlv : l≠v) (t : I) :
    D.upperChart u l v (Probability.mix (Probability.dirac l) (Probability.dirac v) t)=
      SupportPair.swap H D.base := by
  classical
  unfold upperChart affineChart
  rw [Probability.parameter_mix,Probability.parameter_mix]
  simp only [Probability.parameter_dirac]
  have ht : upperTheta l v l=1 ∧ upperTheta l v v=1 := by simp [upperTheta]
  rw [ht.1,ht.2]
  have ho : intervalMix 1 1 t=1 := by apply Subtype.ext; simp [intervalMix]
  rw [ho,D.relationHomotopy.target]

end SupportTorsionData
end
end AbelianTargets
