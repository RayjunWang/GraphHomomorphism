import AbelianTargets.SupportCellCharts

/-! Literal parity covariance of the support-space shore swap. -/
namespace AbelianTargets.SupportPair
noncomputable section
variable {V : Type*} [Fintype V] (H : SimpleGraph V)

def paritySwap (r : ℤ) (z : SupportPair H) : SupportPair H :=
  if r%2=0 then z else swap H z

theorem continuous_paritySwap (r : ℤ) : Continuous (paritySwap H r) := by
  unfold paritySwap
  split_ifs
  · exact continuous_id
  · exact continuous_swap H

theorem paritySwap_mod_eq {r s : ℤ} (h : r%2=s%2) (z : SupportPair H) :
    paritySwap H r z=paritySwap H s z := by simp [paritySwap,h]

theorem paritySwap_add (r s : ℤ) (z : SupportPair H) :
    paritySwap H (r+s) z=paritySwap H r (paritySwap H s z) := by
  have hr₀ := Int.emod_nonneg r (by norm_num : (2:ℤ)≠0)
  have hr₁ := Int.emod_lt_of_pos r (by norm_num : (0:ℤ)<2)
  have hs₀ := Int.emod_nonneg s (by norm_num : (2:ℤ)≠0)
  have hs₁ := Int.emod_lt_of_pos s (by norm_num : (0:ℤ)<2)
  have he := Int.add_emod r s 2
  by_cases hr : r%2=0 <;> by_cases hs : s%2=0
  · have ha : (r+s)%2=0 := by omega
    simp [paritySwap,ha,hr,hs]
  · have ha : (r+s)%2≠0 := by omega
    simp [paritySwap,ha,hr,hs]
  · have ha : (r+s)%2≠0 := by omega
    simp [paritySwap,ha,hr,hs]
  · have ha : (r+s)%2=0 := by omega
    simp [paritySwap,ha,hr,hs,swap_swap]

theorem paritySwap_odd_pow (k j : ℕ) (r : ℤ) (z : SupportPair H) :
    paritySwap H (r+((2*k+1:ℕ):ℤ)^j) z=swap H (paritySwap H r z) := by
  have hb : ((2*k+1:ℕ):ℤ)%2=1 := by simp [Int.add_emod,Int.mul_emod]
  have hp : (((2*k+1:ℕ):ℤ)^j)%2=1 := by
    induction j with
    | zero => norm_num
    | succ j ih => rw [pow_succ,Int.mul_emod,ih,hb]; norm_num
  rw [paritySwap_add]
  simp only [paritySwap,hp,one_ne_zero,if_false]
  by_cases hr : r%2=0 <;> simp [hr,swap_swap]

theorem paritySwap_lower_coordinate (k j n : ℕ) (r : ℤ) (z : SupportPair H) :
    paritySwap H (r+(n:ℤ)*((2*k+1:ℕ):ℤ)^j) z=
      paritySwap H r (if n%2=0 then z else swap H z) := by
  have hb : ((2*k+1:ℕ):ℤ)%2=1 := by simp [Int.add_emod,Int.mul_emod]
  have hp : (((2*k+1:ℕ):ℤ)^j)%2=1 := by
    induction j with
    | zero => norm_num
    | succ j ih => rw [pow_succ,Int.mul_emod,ih,hb]; norm_num
  rw [paritySwap_add]
  have hn : ((n:ℤ)*((2*k+1:ℕ):ℤ)^j)%2=(n%2:ℕ) := by
    rw [Int.mul_emod,hp,mul_one,Int.emod_emod]
    exact (Int.natCast_mod n 2).symm
  simp only [paritySwap,hn,Nat.cast_eq_zero]

end
end AbelianTargets.SupportPair
