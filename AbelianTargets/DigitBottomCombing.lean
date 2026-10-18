import AbelianTargets.DigitBottomData

/-! The actual digit combing of the entire finite bottom interval, with common slots. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

def digitSplice (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n < R) :=
  Classical.choose (exists_bottomSpliceData m hm R n hn)

theorem digitSplice_leftRow (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n < R) :
    (digitSplice m hm R n hn).leftRow = bottomRow m hm R n (by omega) :=
  (Classical.choose_spec (exists_bottomSpliceData m hm R n hn)).1

theorem digitSplice_targetRow (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n < R) :
    (digitSplice m hm R n hn).carryTarget.vertices = bottomRow m hm R (n+1) (by omega) :=
  (Classical.choose_spec (exists_bottomSpliceData m hm R n hn)).2

theorem digitSplice_zero (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n < R)
    (u : unitInterval) : (digitSplice m hm R n hn).family (0,u) =
    FixedSlots.asPath (bottomRow m hm R n (by omega)) (carryRowBudget m R+1) u := by
  rw [FixedSlots.BottomSpliceData.family_zero,digitSplice_leftRow]

theorem digitSplice_one (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n < R)
    (u : unitInterval) : (digitSplice m hm R n hn).family (1,u) =
    FixedSlots.asPath (bottomRow m hm R (n+1) (by omega)) (carryRowBudget m R+1) u := by
  rw [FixedSlots.BottomSpliceData.family_one,digitSplice_targetRow]
  apply FixedSlots.rowPath_congr
  intro j hj
  unfold FixedSlots.appendRowEndpoint
  split_ifs with hj'
  · rfl
  · have hl := compressedWord_interval_uniform_length m hm R (n+1) (show n+1 ≤ R by omega)
    symm
    apply bottomRow_terminal
    dsimp [carryRowBudget] at hj'
    omega

def digitEdgeFamily (m : ℕ) (hm : 2 ≤ m) (R n : ℕ)
    (z : unitInterval × unitInterval) : CarrierVertex (Nat.log m R) 0 R → ℝ :=
  if hn : n < R then (digitSplice m hm R n hn).family z else bottomMass (Nat.log m R) R 0

theorem digitEdgeFamily_eq (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n < R) :
    digitEdgeFamily m hm R n = (digitSplice m hm R n hn).family := by
  funext z
  simp only [digitEdgeFamily,dif_pos hn]

theorem digitEdgeFamily_match (m : ℕ) (hm : 2 ≤ m) (R n : ℕ) (hn : n+1 < R)
    (u : unitInterval) : digitEdgeFamily m hm R n (1,u) = digitEdgeFamily m hm R (n+1) (0,u) := by
  rw [digitEdgeFamily_eq m hm R n (by omega),digitEdgeFamily_eq m hm R (n+1) hn,
    digitSplice_one,digitSplice_zero]

def bottomCombing (m : ℕ) (hm : 2 ≤ m) (R : ℕ) :
    ℝ × unitInterval → (CarrierVertex (Nat.log m R) 0 R → ℝ) :=
  FixedSlots.intervalGlue (digitEdgeFamily m hm R) (R-1)

theorem bottomCombing_continuous (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R) :
    Continuous (bottomCombing m hm R) := by
  apply FixedSlots.intervalGlue_continuous
  · intro i hi
    rw [digitEdgeFamily_eq m hm R i (by omega)]
    exact (digitSplice m hm R i (by omega)).continuous_family
  · intro i hi u
    exact digitEdgeFamily_match m hm R i (by omega) u

theorem bottomCombing_path_time_lipschitz (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (x : ℝ) : LipschitzWith (carryRowBudget m R+2 : ℝ≥0)
      (fun u => bottomCombing m hm R (x,u)) := by
  apply FixedSlots.intervalGlue_path_time_lipschitz
  intro i hi r
  rw [digitEdgeFamily_eq m hm R i (by omega)]
  simpa only [one_mul,Nat.cast_add,Nat.cast_ofNat] using
    (digitSplice m hm R i (by omega)).family_path_time_lipschitz r

theorem bottomCombing_joint_lipschitz (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R) :
    ∃ J : ℝ≥0, LipschitzWith J (bottomCombing m hm R) := by
  apply FixedSlots.intervalGlue_joint_lipschitz
  · intro i hi
    rw [digitEdgeFamily_eq m hm R i (by omega)]
    exact (digitSplice m hm R i (by omega)).family_joint_lipschitz
  · intro i hi u
    exact digitEdgeFamily_match m hm R i (by omega) u

theorem bottomCombing_mem (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (z : ℝ × unitInterval) : bottomCombing m hm R z ∈ ambientRealization m (Nat.log m R) 0 R := by
  apply FixedSlots.intervalGlue_mem
  intro i hi z
  rw [digitEdgeFamily_eq m hm R i (by omega)]
  exact (digitSplice m hm R i (by omega)).family_mem z

@[simp] theorem bottomCombing_source (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (x : ℝ) : bottomCombing m hm R (x,0) = bottomMass (Nat.log m R) R 0 := by
  unfold bottomCombing
  have he := FixedSlots.intervalGlue_eval_eq (digitEdgeFamily m hm R)
    (fun _ _ => bottomMass (Nat.log m R) R 0) (R-1) 0 (fun i hi r => by
      rw [digitEdgeFamily_eq m hm R i (by omega)]
      exact (digitSplice m hm R i (by omega)).family_source r) x
  rw [he]
  have hc : ∀ n, FixedSlots.intervalGlue (fun _ _ => bottomMass (Nat.log m R) R 0) n (x,0) =
      bottomMass (Nat.log m R) R 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [FixedSlots.intervalGlue]; split <;> first | exact ih | rfl
  exact hc _

@[simp] theorem bottomCombing_target (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (x : ℝ) : bottomCombing m hm R (x,1) = bottomMap (Nat.log m R) R x := by
  unfold bottomCombing bottomMap
  have he := FixedSlots.intervalGlue_eval_eq (digitEdgeFamily m hm R)
    (fun i z => FixedSlots.mix (bottomMass (Nat.log m R) R i)
      (bottomMass (Nat.log m R) R (i+1)) z.1) (R-1) 1 (fun i hi r => by
      rw [digitEdgeFamily_eq m hm R i (by omega)]
      exact (digitSplice m hm R i (by omega)).family_target r) x
  rw [he]
  have hc : ∀ n, ∀ u v : unitInterval,
      FixedSlots.intervalGlue (fun i z => FixedSlots.mix (bottomMass (Nat.log m R) R i)
        (bottomMass (Nat.log m R) R (i+1)) z.1) n (x,u) =
      FixedSlots.intervalGlue (fun i z => FixedSlots.mix (bottomMass (Nat.log m R) R i)
        (bottomMass (Nat.log m R) R (i+1)) z.1) n (x,v) := by
    intro n u v
    induction n with
    | zero => rfl
    | succ n ih => simp only [FixedSlots.intervalGlue]; split <;> first | exact ih | rfl
  exact hc _ _ _

@[simp] theorem bottomCombing_base (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (u : unitInterval) : bottomCombing m hm R (0,u) = bottomMass (Nat.log m R) R 0 := by
  rw [bottomCombing,FixedSlots.intervalGlue_zero,digitEdgeFamily_eq m hm R 0 hR,digitSplice_zero]
  have hrow : bottomRow m hm R 0 (Nat.zero_le R) =
      fun _ => bottomMass (Nat.log m R) R 0 := by
    funext j
    apply bottomRow_terminal
    simp only [compressedWord_zero,List.length_nil]
    exact Nat.zero_le _
  rw [hrow]
  have hc : ∀ T k u, FixedSlots.rowPath T (fun _ => bottomMass (Nat.log m R) R 0) k u =
      bottomMass (Nat.log m R) R 0 := by
    intro T k u
    induction k with
    | zero => exact AffineMap.lineMap_same_apply _ _
    | succ k ih => simp only [FixedSlots.rowPath]; split <;> first
        | exact ih
        | exact AffineMap.lineMap_same_apply _ _
  exact hc _ _ _

end
end AbelianTargets.IntervalCarriers
