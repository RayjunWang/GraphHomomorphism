import AbelianTargets.ControlledStages
import AbelianTargets.VerticalCarrierCollapse

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Equal-slot assembly of the actual `m+2` collapses in one height layer. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal unitInterval
noncomputable section
attribute [local instance] Classical.propDecidable

def oneHeightStage {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) :
    ℕ → Probability (CarrierVertex (K+1) A B) × I → Probability (CarrierVertex (K+1) A B)
  | 0 => fun z => (topCollapseFamily hm).mapList Finset.univ.toList z.1 z.2
  | n+1 => fun z => if hn : n < m then
      (fanCollapseFamily hm (show m-n-1 < m by omega)).mapList Finset.univ.toList z.1 z.2
    else if n=m then verticalMap z.1 z.2 else z.1

@[simp] theorem oneHeightStage_zero {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (n : ℕ)
    (p : Probability (CarrierVertex (K+1) A B)) : oneHeightStage hm n (p,0)=p := by
  cases n with
  | zero => exact (topCollapseFamily hm).mapList_zero _ p
  | succ n =>
    simp only [oneHeightStage]
    split_ifs
    · exact (fanCollapseFamily hm _).mapList_zero _ p
    · exact Probability.mix_zero _ _
    · rfl

theorem oneHeightStage_joint {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (n : ℕ) :
    ∃ J : ℝ≥0, LipschitzWith J (oneHeightStage (K := K) (A := A) (B := B) hm n) := by
  cases n with
  | zero => exact (topCollapseFamily hm).mapList_joint _
  | succ n =>
    by_cases hn : n<m
    · simpa only [oneHeightStage,dif_pos hn] using
        (fanCollapseFamily (K := K) (A := A) (B := B) hm (show m-n-1<m by omega)).mapList_joint Finset.univ.toList
    · by_cases he : n=m
      · exact ⟨_,by simpa only [oneHeightStage,dif_neg hn,if_pos he] using
          (verticalMap_joint (K := K) (A := A) (B := B))⟩
      · exact ⟨1,by simpa only [oneHeightStage,dif_neg hn,if_neg he] using
          (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : Probability (CarrierVertex (K+1) A B) × I → _))⟩

def oneHeightState {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (n : ℕ)
    (p : Realization m (K+1) A B) := stageState (fun p : Realization m (K+1) A B => p.1) (oneHeightStage hm) n p

theorem oneHeightState_fan {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (n : ℕ) (hn : n≤m)
    (p : Realization m (K+1) A B) :
    ∃ s ∈ fanFaces m K A B (m-n), (oneHeightState hm (n+1) p).SupportedOn (s : Set _) := by
  induction n with
  | zero =>
    simpa only [oneHeightState,stageState,oneHeightStage,Nat.sub_zero] using (initialFan hm p).2
  | succ n ih =>
    have hnm : n<m := by omega
    obtain ⟨s,hs,hp⟩ := ih (by omega)
    have he : m-n = (m-n-1)+1 := by omega
    let q : SimplicialCarrier (fanFaces m K A B ((m-n-1)+1)) :=
      ⟨oneHeightState hm (n+1) p,s,by simpa only [←he] using hs,hp⟩
    have hq := (fanRetraction hm (show m-n-1<m by omega) q).2
    simpa only [fanRetraction,collapseFan,FreeCollapseFamily.map,q,oneHeightState,stageState,
      oneHeightStage,dif_pos hnm,show m-(n+1)=m-n-1 by omega] using hq

theorem oneHeightStage_actual {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (n : ℕ)
    (p : Realization m (K+1) A B) (t : I) :
    InRealization m (K+1) A B (oneHeightStage hm n (oneHeightState hm n p,t)) := by
  induction n generalizing t with
  | zero => exact (collapseTop hm p t).2
  | succ n ih =>
    by_cases hn : n<m
    · obtain ⟨s,hs,hp⟩ := oneHeightState_fan hm n (by omega) p
      have he : m-n=(m-n-1)+1 := by omega
      let q : SimplicialCarrier (fanFaces m K A B ((m-n-1)+1)) :=
        ⟨oneHeightState hm (n+1) p,s,by simpa only [←he] using hs,hp⟩
      simpa only [oneHeightStage,dif_pos hn,fanOriginal,collapseFan,FreeCollapseFamily.map,q] using
        (fanOriginal (collapseFan hm (show m-n-1<m by omega) q t)).2
    · by_cases he : n=m
      · subst n
        let q : SimplicialCarrier (fanFaces m K A B 0) :=
          ⟨oneHeightState hm (m+1) p,by simpa using oneHeightState_fan hm m le_rfl p⟩
        simpa only [oneHeightStage,dif_neg (lt_irrefl m),if_pos rfl] using
          terminal_fan_verticalMap_mem hm q t
      · have hprev := ih 1
        simpa only [oneHeightStage,dif_neg hn,if_neg he,oneHeightState,stageState] using hprev

theorem oneHeightStage_track {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (n : ℕ)
    (p : Realization m (K+1) A B) :
    LipschitzWith 1 (fun t : I => oneHeightStage hm n (oneHeightState hm n p,t)) := by
  cases n with
  | zero =>
    apply LipschitzWith.of_dist_le_mul
    intro t s
    exact (collapseTop_track hm p).dist_le_mul t s
  | succ n =>
    by_cases hn : n<m
    · obtain ⟨s,hs,hp⟩ := oneHeightState_fan hm n (by omega) p
      have he : m-n=(m-n-1)+1 := by omega
      let q : SimplicialCarrier (fanFaces m K A B ((m-n-1)+1)) :=
        ⟨oneHeightState hm (n+1) p,s,by simpa only [←he] using hs,hp⟩
      apply LipschitzWith.of_dist_le_mul
      intro t s
      simpa only [oneHeightStage,dif_pos hn,collapseFan,FreeCollapseFamily.map,q,Subtype.dist_eq] using
        (collapseFan_track hm (show m-n-1<m by omega) q).dist_le_mul t s
    · by_cases he : n=m
      · simpa only [oneHeightStage,dif_neg hn,if_pos he] using verticalMap_track (oneHeightState hm (n+1) p)
      · simpa only [oneHeightStage,dif_neg hn,if_neg he] using
          (LipschitzWith.const (oneHeightState hm (n+1) p)).weaken (show (0 : ℝ≥0)≤1 by norm_num)

def oneHeightHomotopy {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m (K+1) A B) (t : I) : Realization m (K+1) A B :=
  ⟨stageHomotopy (fun p : Realization m (K+1) A B => p.1) (oneHeightStage hm) (m+2) (p,t),
    stageCurve_mem_of_tracks _ _ {q | InRealization m (K+1) A B q} (fun p => p.2)
      (oneHeightStage_actual hm) _ _⟩

@[simp] theorem oneHeightHomotopy_zero {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m (K+1) A B) : oneHeightHomotopy hm p 0=p :=
  Subtype.ext (stageCurve_zero _ _ (oneHeightStage_zero hm) _ _)

theorem oneHeightHomotopy_one_height {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m (K+1) A B) (v : CarrierVertex (K+1) A B)
    (hv : 0 < (oneHeightHomotopy hm p 1).1.mass v) : v.1.2≤K := by
  let q : SimplicialCarrier (fanFaces m K A B 0) :=
    ⟨oneHeightState hm (m+1) p,by simpa using oneHeightState_fan hm m le_rfl p⟩
  have he : (oneHeightHomotopy hm p 1).1=(collapseVertical hm q 1).1 := by
    change stageCurve _ _ (m+2) (1,p)=_
    rw [stageCurve_one]
    simp only [stageState,oneHeightStage,dif_neg (lt_irrefl m),if_pos rfl,
      collapseVertical,q,oneHeightState,ite_true]
  exact collapseVertical_terminal_height hm q v (by simpa only [he] using hv)

theorem oneHeightHomotopy_track {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m (K+1) A B) : LipschitzWith ((m+2 : ℕ) : ℝ≥0) (oneHeightHomotopy hm p) := by
  have hh := stageHomotopy_track (fun p : Realization m (K+1) A B => p.1)
    (oneHeightStage hm) (oneHeightStage_zero hm) 1 (oneHeightStage_track hm) (m+2) p
  apply LipschitzWith.of_dist_le_mul
  intro t s
  simpa only [oneHeightHomotopy,Subtype.dist_eq,mul_one] using hh.dist_le_mul t s

theorem oneHeightHomotopy_joint {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) :
    ∃ J : ℝ≥0, LipschitzWith J
      (fun z : Realization m (K+1) A B × I => oneHeightHomotopy hm z.1 z.2) := by
  have hi : LipschitzWith 1 (fun p : Realization m (K+1) A B => p.1) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change dist p q ≤ (1 : ℝ)*dist p q
    simp
  obtain ⟨J,hJ⟩ := stageHomotopy_joint (fun p : Realization m (K+1) A B => p.1)
    (oneHeightStage hm) (oneHeightStage_zero hm) ⟨1,hi⟩ (oneHeightStage_joint hm) (m+2)
  refine ⟨J,?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro p q
  exact hJ.dist_le_mul p q

theorem continuous_oneHeightHomotopy {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) :
    Continuous (fun z : Realization m (K+1) A B × I => oneHeightHomotopy hm z.1 z.2) :=
  (oneHeightHomotopy_joint hm).choose_spec.continuous

end
end AbelianTargets.IntervalCarriers
