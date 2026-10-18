import AbelianTargets.ActualQuantitativeAtlasRecursion

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AbelianTargets
noncomputable section
open scoped NNReal BigOperators

def anisotropicLowerRates {d : ℕ} (i : Fin d) (P L M : ℝ≥0) (j : Fin d) : ℝ≥0 :=
  (if j=i then L else M)/(32*P)

def anisotropicUpperRates {d : ℕ} (i : Fin d) (L M : ℝ≥0) (j : Fin d) : ℝ≥0 :=
  6*(if j=i then L else M)

def firstRankFactor (P : ℝ≥0) : ℕ→ℝ≥0
  | 0 => 0
  | n+1 => max (firstRankFactor P n) (96*P*max (6*firstRankFactor P n) 1)

def transverseRankFactor (P : ℝ≥0) (d : ℕ) (D J : ℝ≥0) : ℕ→ℝ≥0
  | 0 => 0
  | n+1 => max (transverseRankFactor P d D J n)
      (64*P*ControlledContraction.coneTransverseConstant (6*firstRankFactor P n*D) D J
        (6*d*d*(firstRankFactor P n*D+transverseRankFactor P d D J n)+1))

theorem anisotropic_rank_rates_bound {d : ℕ} (i : Fin d) (P L M D J : ℝ≥0)
    (hP : 0<P) (hL : 0<L) (hM : 0<M) (n : ℕ) :
    ∀ j,atlasRankRates (anisotropicLowerRates i P L M) (anisotropicUpperRates i L M) D J i n j≤
      if j=i then firstRankFactor P n*D/L else transverseRankFactor P d D J n/M := by
  induction n with
  | zero => intro j; simp [atlasRankRates,firstRankFactor,transverseRankFactor]
  | succ n ih =>
    let C := atlasRankRates (anisotropicLowerRates i P L M) (anisotropicUpperRates i L M) D J i n
    let A := firstRankFactor P n
    let B := transverseRankFactor P d D J n
    have hS : C i*anisotropicUpperRates i L M i≤6*A*D := by
      have hi := ih i
      simp at hi
      calc
        _ = C i*(6*L) := by simp [anisotropicUpperRates]
        _ ≤ (A*D/L)*(6*L) := mul_le_mul_right' hi _
        _ = _ := by field_simp <;> ring
    have hB : rankBoundaryRate (anisotropicUpperRates i L M) C≤6*d*d*(A*D+B)+1 := by
      have hterm : ∀j,C j*anisotropicUpperRates i L M j/2≤3*(A*D+B) := by
        intro j
        have hc := ih j
        by_cases hj : j=i
        · subst j
          calc
            _ ≤ 6*A*D/2 := by gcongr
            _ ≤ _ := by
              rw [show 6*A*D/2=3*(A*D) by ring]
              exact mul_le_mul_left' (le_add_of_nonneg_right (by positivity)) 3
        · simp only [if_neg hj] at hc
          calc
            _ = C j*(6*M)/2 := by simp [anisotropicUpperRates,hj]
            _ ≤ (B/M)*(6*M)/2 := by gcongr
            _ = 3*B := by field_simp <;> ring
            _ ≤ _ := mul_le_mul_left' (le_add_of_nonneg_left (by positivity : 0≤A*D)) 3
      have hs : (∑ j,C j*anisotropicUpperRates i L M j/2)≤(d : ℝ≥0)*(3*(A*D+B)) := by
        calc
          _ ≤ ∑ _j : Fin d,3*(A*D+B) := Finset.sum_le_sum (fun j _ => hterm j)
          _ = _ := by simp
      unfold rankBoundaryRate
      calc
        _ ≤ 2*d*((d : ℝ≥0)*(3*(A*D+B)))+1 := by gcongr
        _ = _ := by ring
    intro j
    change nextRankRates (anisotropicLowerRates i P L M) (anisotropicUpperRates i L M) C D J i j≤_
    unfold nextRankRates
    by_cases hj : j=i
    · subst j
      simp only [if_true]
      apply max_le
      · have hci : C i≤A*D/L := by simpa [C,A] using ih i
        exact hci.trans (by dsimp [firstRankFactor]; gcongr; exact le_max_left _ _)
      · have hmax : max (C i*anisotropicUpperRates i L M i) D≤max (6*A) 1*D := by
          apply max_le
          · exact hS.trans (by gcongr; exact le_max_left _ _)
          · simpa only [one_mul] using (mul_le_mul_right' (le_max_right (6*A) 1) D)
        calc
          _ ≤ (3*(max (6*A) 1*D))/(L/(32*P)) := by
            unfold anisotropicLowerRates
            simp only [if_true]
            exact div_le_div₀ (by positivity) (mul_le_mul_left' hmax 3) (by positivity) le_rfl
          _ = (96*P*max (6*A) 1)*D/L := by field_simp <;> ring
          _ ≤ _ := by dsimp [firstRankFactor]; gcongr; exact le_max_right _ _
    · simp only [if_neg hj]
      apply max_le
      · exact (ih j).trans (by simp only [if_neg hj]; dsimp [transverseRankFactor]; gcongr; exact le_max_left _ _)
      · have hcone : ControlledContraction.coneTransverseConstant (C i*anisotropicUpperRates i L M i) D J
            (rankBoundaryRate (anisotropicUpperRates i L M) C)≤
          ControlledContraction.coneTransverseConstant (6*A*D) D J (6*d*d*(A*D+B)+1) := by
          unfold ControlledContraction.coneTransverseConstant
          gcongr
        calc
          _ ≤ (2*ControlledContraction.coneTransverseConstant (6*A*D) D J (6*d*d*(A*D+B)+1))/(M/(32*P)) := by
            unfold anisotropicLowerRates
            simp only [if_neg hj]
            gcongr
          _ = (64*P*ControlledContraction.coneTransverseConstant (6*A*D) D J (6*d*d*(A*D+B)+1))/M := by
            field_simp <;> ring
          _ ≤ _ := by dsimp [transverseRankFactor]; gcongr; exact le_max_right _ _

end
end AbelianTargets
