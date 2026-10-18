import AbelianTargets.DoubleCoverLifts

/-!
# Odd torsion walks and support-space paths

This file makes the endpoint transports in the path-lifting argument of
Lemma 6.2 and Proposition 7.1 explicit.
-/

namespace AbelianTargets

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- A relative path homotopy after explicit transport of the two endpoints. -/
def HeteroPathHomotopic {a b a' b' : X} (P : Path a b) (Q : Path a' b') : Prop :=
  ∃ (ha : a' = a) (hb : b' = b), (P.cast ha hb).Homotopic Q

namespace HeteroPathHomotopic

theorem refl {a b : X} (P : Path a b) : HeteroPathHomotopic P P :=
  ⟨rfl, rfl, .refl P⟩

theorem of_homotopic {a b : X} {P Q : Path a b} (h : P.Homotopic Q) :
    HeteroPathHomotopic P Q := ⟨rfl, rfl, h⟩

theorem symm {a b a' b' : X} {P : Path a b} {Q : Path a' b'}
    (h : HeteroPathHomotopic P Q) : HeteroPathHomotopic Q P := by
  rcases h with ⟨ha, hb, h⟩
  subst a'
  subst b'
  exact ⟨rfl, rfl, h.symm⟩

theorem trans {a b a' b' a'' b'' : X}
    {P : Path a b} {Q : Path a' b'} {R : Path a'' b''}
    (hPQ : HeteroPathHomotopic P Q) (hQR : HeteroPathHomotopic Q R) :
    HeteroPathHomotopic P R := by
  rcases hPQ with ⟨ha, hb, hPQ⟩
  rcases hQR with ⟨ha', hb', hQR⟩
  subst a'
  subst b'
  subst a''
  subst b''
  exact ⟨rfl, rfl, hPQ.trans hQR⟩

theorem append {a b c a' b' c' : X}
    {P : Path a b} {Q : Path a' b'} {R : Path b c} {S : Path b' c'}
    (hPQ : HeteroPathHomotopic P Q) (hRS : HeteroPathHomotopic R S) :
    HeteroPathHomotopic (P.trans R) (Q.trans S) := by
  rcases hPQ with ⟨ha, hb, hPQ⟩
  rcases hRS with ⟨_, hc, hRS⟩
  subst a'
  subst b'
  subst c'
  exact ⟨rfl, rfl, hPQ.hcomp hRS⟩

theorem of_pointwise_eq {a b a' b' : X} (P : Path a b) (Q : Path a' b')
    (h : ∀ t, P t = Q t) : HeteroPathHomotopic P Q := by
  have ha : a' = a := by simpa only [Path.source] using (h 0).symm
  have hb : b' = b := by simpa only [Path.target] using (h 1).symm
  refine ⟨ha, hb, ?_⟩
  have he : P.cast ha hb = Q := Path.ext (funext h)
  rw [he]

theorem homotopic {a b : X} {P Q : Path a b} (h : HeteroPathHomotopic P Q) : P.Homotopic Q := by
  rcases h with ⟨_, _, h⟩
  exact h

end HeteroPathHomotopic

variable {V : Type*} [Fintype V] (H : SimpleGraph V) (s : V → V) (hs : ∀ v, H.Adj v (s v))

theorem supportHeteroReducedHomotopic {a b a' b' : V ⊕ V}
    {p : H.bipartiteDoubleCover.Walk a b} {q : H.bipartiteDoubleCover.Walk a' b'}
    (hpq : HeteroReducedHomotopic H.bipartiteDoubleCover p q) :
    HeteroPathHomotopic
      (walkPath H.bipartiteDoubleCover (doublePoint H s hs) (doubleEdgePath H s hs) p)
      (walkPath H.bipartiteDoubleCover (doublePoint H s hs) (doubleEdgePath H s hs) q) := by
  rcases hpq with ⟨ha, hb, hpq⟩
  refine ⟨congrArg (doublePoint H s hs) ha.symm, congrArg (doublePoint H s hs) hb.symm, ?_⟩
  rw [← walkPath_copy H.bipartiteDoubleCover (doublePoint H s hs) (doubleEdgePath H s hs) p ha hb]
  apply Path.Homotopic.Quotient.exact
  rw [doubleWalkPath_class, doubleWalkPath_class]
  exact doubleCover_respects_reducedHomotopic H s hs hpq

theorem supportLiftPath_append {a b c : V} (p : H.Walk a b) (q : H.Walk b c) (σ : Bool) :
    HeteroPathHomotopic (supportLiftPath H s hs (p.append q) σ)
      ((supportLiftPath H s hs p σ).trans (supportLiftPath H s hs q (toggleSheet p.length σ))) :=
  (supportHeteroReducedHomotopic H s hs (liftWalk_append_hetero H p q σ)).trans
    (.of_homotopic (walkPath_append H.bipartiteDoubleCover (doublePoint H s hs)
      (doubleEdgePath H s hs) (liftWalk H p σ) (liftWalk H q (toggleSheet p.length σ))))

theorem supportLiftPath_reducedHomotopic {a b : V} {p q : H.Walk a b}
    (hpq : ReducedHomotopic H p q) (σ : Bool) :
    HeteroPathHomotopic (supportLiftPath H s hs p σ) (supportLiftPath H s hs q σ) :=
  supportHeteroReducedHomotopic H s hs (ReducedHomotopic.lift_to_doubleCover H hpq σ)

theorem toggleSheet_odd {n : ℕ} (hn : Odd n) (σ : Bool) : toggleSheet n σ = !σ := by
  rw [toggleSheet_eq_mod, Nat.odd_iff.mp hn]
  simp

/-- The path `α : p → τp` obtained from an odd closed graph walk. -/
def oddSupportPath {a : V} (γ : H.Walk a a) (hodd : Odd γ.length) :
    Path (SupportPair.vertex H (hs a)) (SupportPair.swap H (SupportPair.vertex H (hs a))) :=
  (supportLiftPath H s hs γ false).cast rfl (by
    change doublePoint H s hs (sheetVertex a true) =
      doublePoint H s hs (sheetVertex a (toggleSheet γ.length false))
    rw [toggleSheet_odd hodd]
    rfl)

/-- The return path is the shore swap of `α`. -/
def swappedReturnPath {p : SupportPair H} (α : Path p (SupportPair.swap H p)) :
    Path (SupportPair.swap H p) p :=
  (α.map (SupportPair.continuous_swap H)).cast rfl (SupportPair.swap_swap H p).symm

def alternatingSupportLoop {p : SupportPair H} (α : Path p (SupportPair.swap H p)) : Path p p :=
  α.trans (swappedReturnPath H α)

theorem supportLiftPath_double_odd {a : V} (γ : H.Walk a a) (hodd : Odd γ.length) :
    HeteroPathHomotopic (supportLiftPath H s hs (γ.append γ) false)
      (alternatingSupportLoop H (oddSupportPath H s hs γ hodd)) := by
  have hα : HeteroPathHomotopic (supportLiftPath H s hs γ false)
      (oddSupportPath H s hs γ hodd) := .of_pointwise_eq _ _ (fun _ => rfl)
  have hβ : HeteroPathHomotopic (supportLiftPath H s hs γ (toggleSheet γ.length false))
      (swappedReturnPath H (oddSupportPath H s hs γ hodd)) := by
    apply HeteroPathHomotopic.of_pointwise_eq
    intro t
    change supportLiftPath H s hs γ (toggleSheet γ.length false) t =
      SupportPair.swap H (supportLiftPath H s hs γ false t)
    exact (congrArg (fun sheet : Bool => supportLiftPath H s hs γ sheet t)
      (toggleSheet_odd hodd false)).trans (supportLiftPath_swap H s hs γ false t).symm
  exact (supportLiftPath_append H s hs γ γ false).trans (hα.append hβ)

def pathLoopPower {p : X} (P : Path p p) : ℕ → Path p p
  | 0 => Path.refl p
  | n + 1 => P.trans (pathLoopPower P n)

theorem toggleSheet_even {n : ℕ} (hn : Even n) (σ : Bool) : toggleSheet n σ = σ := by
  rw [toggleSheet_eq_mod, Nat.even_iff.mp hn]
  simp

theorem supportLiftPath_loopPower {a : V} (δ : H.Walk a a) (hδ : Even δ.length)
    (σ : Bool) (P : Path (doublePoint H s hs (sheetVertex a σ))
      (doublePoint H s hs (sheetVertex a σ)))
    (hP : HeteroPathHomotopic (supportLiftPath H s hs δ σ) P) (n : ℕ) :
    HeteroPathHomotopic (supportLiftPath H s hs (loopPower H δ n) σ) (pathLoopPower P n) := by
  induction n with
  | zero => exact .of_pointwise_eq _ _ (fun _ => rfl)
  | succ n ih =>
    have ht : HeteroPathHomotopic (supportLiftPath H s hs (loopPower H δ n) (toggleSheet δ.length σ))
        (supportLiftPath H s hs (loopPower H δ n) σ) := by
      apply HeteroPathHomotopic.of_pointwise_eq
      intro t
      rw [toggleSheet_even hδ]
    exact (supportLiftPath_append H s hs δ (loopPower H δ n) σ).trans
      (hP.append (ht.trans ih))

omit [Fintype V] in
theorem loopPower_double {a : V} (γ : H.Walk a a) (n : ℕ) :
    loopPower H (γ.append γ) n = loopPower H γ (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [loopPower_succ, ih, Nat.mul_succ]
    rw [show 2*n+2 = 2+2*n by omega, loopPower_add]
    simp [loopPower_succ]

/-- The finite-torsion hypothesis gives the genuine nullhomotopy of
`(α * τ α)^(N/2)` required in Proposition 7.1. -/
theorem oddSupportPath_torsion {a : V} (γ : H.Walk a a) (hodd : Odd γ.length)
    {N : ℕ} (hnull : ReducedHomotopic H (loopPower H γ N) .nil) :
    ∃ k : ℕ, N = 2*k ∧
      (pathLoopPower (alternatingSupportLoop H (oddSupportPath H s hs γ hodd)) k).Homotopic
        (Path.refl (SupportPair.vertex H (hs a))) := by
  obtain ⟨k, hk⟩ := even_exponent_of_odd_null_power hodd hnull
  have hN : N = 2*k := by omega
  have hδ : Even (γ.append γ).length := by
    simp only [SimpleGraph.Walk.length_append]
    exact ⟨γ.length, rfl⟩
  have hP := supportLiftPath_loopPower H s hs (γ.append γ) hδ false
    (alternatingSupportLoop H (oddSupportPath H s hs γ hodd))
    (supportLiftPath_double_odd H s hs γ hodd) k
  have hnull' : ReducedHomotopic H (loopPower H (γ.append γ) k) .nil := by
    simpa only [loopPower_double, ← hN] using hnull
  have hT := supportLiftPath_reducedHomotopic H s hs hnull' false
  exact ⟨k, hN, (hP.symm.trans hT).homotopic⟩

/-- The relation-cell boundary `α * reverse(P * α)` is nullhomotopic
whenever `P` is. This is the explicit cancellation used for the
Baumslag--Solitar relation in Lemma 6.2 and Proposition 7.1. -/
theorem presentation_boundary_nullhomotopic {p q : X} (α : Path p q)
    (P : Path p p) (hP : P.Homotopic (Path.refl p)) :
    (α.trans (P.trans α).symm).Homotopic (Path.refl p) := by
  rw [Path.trans_symm]
  exact (Path.Homotopic.trans_assoc α α.symm P.symm).symm.trans
    (((Path.Homotopic.trans_symm α).hcomp (Path.Homotopic.refl P.symm)).trans
      ((Path.Homotopic.refl_trans P.symm).trans (by simpa only [Path.refl_symm] using hP.symm₂)))

/-- The actual boundary image of the relation cell for exponent `N+1`
is filled by a genuine relative path homotopy. -/
theorem oddSupportPath_presentation_boundary {a : V} (γ : H.Walk a a)
    (hodd : Odd γ.length) {N : ℕ}
    (hnull : ReducedHomotopic H (loopPower H γ N) .nil) :
    ∃ k : ℕ, N = 2*k ∧
      ((oddSupportPath H s hs γ hodd).trans
        ((pathLoopPower (alternatingSupportLoop H (oddSupportPath H s hs γ hodd)) k).trans
          (oddSupportPath H s hs γ hodd)).symm).Homotopic
        (Path.refl (SupportPair.vertex H (hs a))) := by
  obtain ⟨k, hk, hP⟩ := oddSupportPath_torsion H s hs γ hodd hnull
  exact ⟨k, hk, presentation_boundary_nullhomotopic _ _ hP⟩

end

end AbelianTargets
