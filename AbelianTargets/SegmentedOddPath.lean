import AbelianTargets.SupportWitness
import AbelianTargets.BottomEdgeSplice

/-! A literal alternating odd path and its finite dyadic edge subdivision. -/

namespace AbelianTargets
noncomputable section

def firstHalf (r : unitInterval) : unitInterval :=
  ⟨(r : ℝ)/2,by constructor <;> linarith [r.property.1,r.property.2]⟩
def secondHalf (r : unitInterval) : unitInterval :=
  ⟨(1+(r : ℝ))/2,by constructor <;> linarith [r.property.1,r.property.2]⟩
def tailQuarter (r : unitInterval) : unitInterval := secondHalf (secondHalf r)
def intervalMix (a b r : unitInterval) : unitInterval :=
  ⟨(1-(r : ℝ))*(a : ℝ)+(r : ℝ)*(b : ℝ),by
    have h₀ := mul_nonneg (show 0 ≤ 1-(r : ℝ) by linarith [r.property.2]) a.property.1
    have h₁ := mul_nonneg r.property.1 b.property.1
    have h₂ := mul_le_mul_of_nonneg_left a.property.2 (show 0 ≤ 1-(r : ℝ) by linarith [r.property.2])
    have h₃ := mul_le_mul_of_nonneg_left b.property.2 r.property.1
    constructor <;> nlinarith⟩

theorem trans_firstHalf {X : Type*} [TopologicalSpace X] {p q z : X}
    (a : Path p q) (b : Path q z) (r : unitInterval) : (a.trans b) (firstHalf r) = a r := by
  rw [Path.trans_apply,dif_pos (by change (r : ℝ)/2 ≤ 1/2; linarith [r.property.2])]
  congr 1
  apply Subtype.ext
  change 2*((r : ℝ)/2) = (r : ℝ)
  ring

theorem trans_secondHalf {X : Type*} [TopologicalSpace X] {p q z : X}
    (a : Path p q) (b : Path q z) (r : unitInterval) : (a.trans b) (secondHalf r) = b r := by
  rw [Path.trans_apply]
  split_ifs with h
  · have hr : r = 0 := by
      apply Subtype.ext
      change (1+(r : ℝ))/2 ≤ 1/2 at h
      change (r : ℝ) = 0
      linarith [r.property.1]
    subst r
    have he : ∀ (hI : 2*(secondHalf 0 : ℝ) ∈ unitInterval),
        (⟨2*(secondHalf 0 : ℝ),hI⟩ : unitInterval) = 1 := by
      intro hI
      apply Subtype.ext
      norm_num [secondHalf]
    rw [he,a.target,b.source]
  · congr 1
    apply Subtype.ext
    change 2*((1+(r : ℝ))/2)-1 = (r : ℝ)
    ring

def alternatingOddPath {X : Type*} [TopologicalSpace X] {p q : X}
    (a : Path p q) (b : Path q p) : ℕ → Path p q
  | 0 => a
  | k+1 => a.trans (b.trans (alternatingOddPath a b k))

def oddBreak : ℕ → ℕ → unitInterval
  | 0,0 => 0
  | 0,_+1 => 1
  | k+1,0 => 0
  | k+1,1 => FixedSlots.halfPoint
  | k+1,n+2 => tailQuarter (oddBreak k n)

@[simp] theorem oddBreak_zero (k : ℕ) : oddBreak k 0 = 0 := by cases k <;> rfl
@[simp] theorem oddBreak_last (k : ℕ) : oddBreak k (2*k+1) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have he : 2*(k+1)+1 = (2*k+1)+2 := by omega
    rw [he,oddBreak,ih]
    apply Subtype.ext
    norm_num [tailQuarter,secondHalf]

theorem intervalMix_zero_one (r : unitInterval) : intervalMix 0 1 r = r := by
  apply Subtype.ext
  simp [intervalMix]

theorem intervalMix_first (r : unitInterval) :
    intervalMix 0 FixedSlots.halfPoint r = firstHalf r := by
  apply Subtype.ext
  change (1-(r : ℝ))*0+(r : ℝ)*(1/2) = (r : ℝ)/2
  ring

theorem intervalMix_second (r : unitInterval) :
    intervalMix FixedSlots.halfPoint (tailQuarter 0) r = secondHalf (firstHalf r) := by
  apply Subtype.ext
  change (1-(r : ℝ))*(1/2)+(r : ℝ)*((1+(1+0)/2)/2) = (1+(r : ℝ)/2)/2
  ring

theorem intervalMix_tail (a b r : unitInterval) :
    intervalMix (tailQuarter a) (tailQuarter b) r = tailQuarter (intervalMix a b r) := by
  apply Subtype.ext
  change (1-(r : ℝ))*((1+(1+(a : ℝ))/2)/2)+(r : ℝ)*((1+(1+(b : ℝ))/2)/2) =
    (1+(1+((1-(r : ℝ))*(a : ℝ)+(r : ℝ)*(b : ℝ)))/2)/2
  ring

theorem alternatingOddPath_on_slot {X : Type*} [TopologicalSpace X] {p q : X}
    (a : Path p q) (b : Path q p) (k n : ℕ) (hn : n < 2*k+1) (r : unitInterval) :
    alternatingOddPath a b k (intervalMix (oddBreak k n) (oddBreak k (n+1)) r) =
      if n%2=0 then a r else b r := by
  induction k generalizing n with
  | zero =>
    have he : n=0 := by omega
    subst n
    simp [alternatingOddPath,oddBreak,intervalMix_zero_one]
  | succ k ih =>
    cases n with
    | zero =>
      rw [oddBreak,oddBreak,intervalMix_first,alternatingOddPath,trans_firstHalf]
      rfl
    | succ n =>
      cases n with
      | zero =>
        rw [oddBreak,oddBreak,oddBreak_zero,intervalMix_second,alternatingOddPath,
          trans_secondHalf,trans_firstHalf]
        rfl
      | succ n =>
        have he : n+1+1=n+2 := by omega
        have he' : n+1+1+1=(n+1)+2 := by omega
        rw [he,he',oddBreak,oddBreak,intervalMix_tail,alternatingOddPath]
        change (a.trans (b.trans (alternatingOddPath a b k)))
          (secondHalf (secondHalf (intervalMix (oddBreak k n) (oddBreak k (n+1)) r))) = _
        rw [trans_secondHalf,trans_secondHalf,ih n (by omega)]
        have hp : (n+2)%2=n%2 := by omega
        rw [hp]

theorem alternatingOddPath_homotopic {X : Type*} [TopologicalSpace X] {p q : X}
    (a : Path p q) (b : Path q p) (k : ℕ) :
    (alternatingOddPath a b k).Homotopic ((pathLoopPower (a.trans b) k).trans a) := by
  induction k with
  | zero => exact (Path.Homotopic.refl_trans a).symm
  | succ k ih =>
    exact ((Path.Homotopic.refl a).hcomp ((Path.Homotopic.refl b).hcomp ih)).trans
      ((Path.Homotopic.trans_assoc a b _).symm.trans
        (Path.Homotopic.trans_assoc (a.trans b) (pathLoopPower (a.trans b) k) a).symm)

theorem SupportTorsionData.alternating_odd_null {V : Type*} [Fintype V]
    {H : SimpleGraph V} (D : SupportTorsionData H) :
    (alternatingOddPath D.a D.b D.power).Homotopic D.a :=
  (alternatingOddPath_homotopic D.a D.b D.power).trans
    ((D.null_power.hcomp (Path.Homotopic.refl D.a)).trans (Path.Homotopic.refl_trans D.a))

end
end AbelianTargets
