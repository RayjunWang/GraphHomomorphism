import AbelianTargets.DoubleCoverSupport

/-!
# Binary lifts of graph walks

Walks lift to the bipartite double cover with the sheet determined by their
length parity.  This is the combinatorial covering step in Lemma 6.2.
-/

namespace AbelianTargets

variable {V : Type*} (H : SimpleGraph V)

def toggleSheet : ℕ → Bool → Bool
  | 0, b => b
  | n + 1, b => toggleSheet n (!b)

@[simp] theorem toggleSheet_zero (b : Bool) : toggleSheet 0 b = b := rfl
@[simp] theorem toggleSheet_succ (n : ℕ) (b : Bool) : toggleSheet (n+1) b = toggleSheet n (!b) := rfl

theorem toggleSheet_add (m n : ℕ) (b : Bool) :
    toggleSheet (m+n) b = toggleSheet n (toggleSheet m b) := by
  induction m generalizing b with
  | zero => simp
  | succ m ih => simpa [Nat.succ_add] using ih (!b)

theorem toggleSheet_eq_mod (n : ℕ) (b : Bool) :
    toggleSheet n b = if n % 2 = 0 then b else !b := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hn with hn | hn <;> simp [toggleSheet_succ, ih, Nat.add_mod, hn]

theorem toggleSheet_eq_of_mod_eq {m n : ℕ} (h : m % 2 = n % 2) (b : Bool) :
    toggleSheet m b = toggleSheet n b := by rw [toggleSheet_eq_mod, toggleSheet_eq_mod, h]

def sheetVertex (v : V) : Bool → V ⊕ V
  | false => .inl v
  | true => .inr v

def liftedEdge {a b : V} (h : H.Adj a b) (σ : Bool) :
    H.bipartiteDoubleCover.Adj (sheetVertex a σ) (sheetVertex b (!σ)) := by
  cases σ <;> exact h

def liftWalk : {a b : V} → (p : H.Walk a b) → (σ : Bool) →
    H.bipartiteDoubleCover.Walk (sheetVertex a σ) (sheetVertex b (toggleSheet p.length σ))
  | _, _, .nil, _ => .nil
  | _, _, .cons h p, σ => .cons (liftedEdge H h σ) (liftWalk p (!σ))

@[simp] theorem liftWalk_length {a b : V} (p : H.Walk a b) (σ : Bool) :
    (liftWalk H p σ).length = p.length := by
  induction p generalizing σ with
  | nil => rfl
  | cons h p ih => simpa [liftWalk] using ih (!σ)

theorem liftWalk_append {a b c : V} (p : H.Walk a b) (q : H.Walk b c) (σ : Bool) :
    (liftWalk H p σ).append (liftWalk H q (toggleSheet p.length σ)) =
      (liftWalk H (p.append q) σ).copy rfl
        (congrArg (sheetVertex c) (by
          simpa only [SimpleGraph.Walk.length_append] using toggleSheet_add p.length q.length σ)) := by
  induction p generalizing σ with
  | nil => rfl
  | cons h p ih =>
    simpa only [SimpleGraph.Walk.cons_append, liftWalk, SimpleGraph.Walk.length_cons,
      toggleSheet_succ, SimpleGraph.Walk.copy_cons] using
      congrArg (SimpleGraph.Walk.cons (liftedEdge H h σ)) (ih q (!σ))

namespace ReducedHomotopic

variable {H}

theorem copy {a b a' b' : V} {p q : H.Walk a b}
    (hpq : ReducedHomotopic H p q) (ha : a = a') (hb : b = b') :
    ReducedHomotopic H (p.copy ha hb) (q.copy ha hb) := by
  subst a'
  subst b'
  exact hpq

end ReducedHomotopic

/-- Reduced homotopy with endpoint equalities made explicit. This wrapper
allows lifting to a covering graph without hiding endpoint transports. -/
def HeteroReducedHomotopic {a b a' b' : V} (p : H.Walk a b) (q : H.Walk a' b') : Prop :=
  ∃ (ha : a = a') (hb : b = b'), ReducedHomotopic H (p.copy ha hb) q

namespace HeteroReducedHomotopic

variable {H}

theorem refl {a b : V} (p : H.Walk a b) : HeteroReducedHomotopic H p p :=
  ⟨rfl, rfl, .refl p⟩

theorem symm {a b a' b' : V} {p : H.Walk a b} {q : H.Walk a' b'}
    (h : HeteroReducedHomotopic H p q) : HeteroReducedHomotopic H q p := by
  rcases h with ⟨ha, hb, h⟩
  subst a'
  subst b'
  exact ⟨rfl, rfl, h.symm⟩

theorem trans {a b a' b' a'' b'' : V}
    {p : H.Walk a b} {q : H.Walk a' b'} {r : H.Walk a'' b''}
    (hpq : HeteroReducedHomotopic H p q) (hqr : HeteroReducedHomotopic H q r) :
    HeteroReducedHomotopic H p r := by
  rcases hpq with ⟨ha, hb, hpq⟩
  rcases hqr with ⟨ha', hb', hqr⟩
  subst a'
  subst b'
  subst a''
  subst b''
  exact ⟨rfl, rfl, hpq.trans hqr⟩

theorem append {a b c a' b' c' : V}
    {p : H.Walk a b} {q : H.Walk a' b'} {r : H.Walk b c} {s : H.Walk b' c'}
    (hpq : HeteroReducedHomotopic H p q) (hrs : HeteroReducedHomotopic H r s) :
    HeteroReducedHomotopic H (p.append r) (q.append s) := by
  rcases hpq with ⟨ha, hb, hpq⟩
  rcases hrs with ⟨_, hc, hrs⟩
  subst a'
  subst b'
  subst c'
  exact ⟨rfl, rfl, .append hpq hrs⟩

end HeteroReducedHomotopic

theorem liftWalk_append_hetero {a b c : V}
    (p : H.Walk a b) (q : H.Walk b c) (σ : Bool) :
    HeteroReducedHomotopic H.bipartiteDoubleCover (liftWalk H (p.append q) σ)
      ((liftWalk H p σ).append (liftWalk H q (toggleSheet p.length σ))) := by
  refine ⟨rfl, congrArg (sheetVertex c) (by
    simpa only [SimpleGraph.Walk.length_append] using toggleSheet_add p.length q.length σ), ?_⟩
  rw [← liftWalk_append H p q σ]
  exact .refl _

theorem liftWalk_changeSheet {a b : V} (p : H.Walk a b) {σ τ : Bool} (h : σ = τ) :
    HeteroReducedHomotopic H.bipartiteDoubleCover (liftWalk H p σ) (liftWalk H p τ) := by
  subst τ
  exact .refl _

/-- Every defining reduced-homotopy move lifts to the bipartite double cover.
Endpoint transport is recorded explicitly rather than assumed. -/
theorem ReducedHomotopic.lift_to_doubleCover {a b : V} {p q : H.Walk a b}
    (hpq : ReducedHomotopic H p q) (σ : Bool) :
    HeteroReducedHomotopic H.bipartiteDoubleCover (liftWalk H p σ) (liftWalk H q σ) := by
  induction hpq generalizing σ with
  | refl p => exact .refl _
  | symm _ ih => exact (ih σ).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ σ).trans (ih₂ σ)
  | @append a b c p q r s hpq hrs ih₁ ih₂ =>
    have he : toggleSheet p.length σ = toggleSheet q.length σ :=
      toggleSheet_eq_of_mod_eq hpq.length_mod_two σ
    have htail : HeteroReducedHomotopic H.bipartiteDoubleCover
        (liftWalk H r (toggleSheet p.length σ)) (liftWalk H s (toggleSheet q.length σ)) := by
      exact (ih₂ (toggleSheet p.length σ)).trans (liftWalk_changeSheet H s he)
    exact (liftWalk_append_hetero H p r σ).trans
      (((ih₁ σ).append htail).trans (liftWalk_append_hetero H q s σ).symm)
  | spur h =>
    cases σ
    · exact ⟨rfl, rfl, .spur (liftedEdge H h false)⟩
    · exact ⟨rfl, rfl, .spur (liftedEdge H h true)⟩
  | @four a p hp =>
    have he : sheetVertex a (toggleSheet p.length σ) = sheetVertex a σ := by
      rw [hp]
      cases σ <;> rfl
    refine ⟨rfl, he, .four _ ?_⟩
    exact (SimpleGraph.Walk.length_copy (liftWalk H p σ) rfl he).trans
      ((liftWalk_length H p σ).trans hp)

/-- A reduced-null closed walk lifts to a reduced-null closed walk in the
binary cover; its endpoint equality is part of the conclusion. -/
theorem liftWalk_null {a : V} {p : H.Walk a a}
    (hp : ReducedHomotopic H p .nil) (σ : Bool) :
    ∃ he : sheetVertex a (toggleSheet p.length σ) = sheetVertex a σ,
      ReducedHomotopic H.bipartiteDoubleCover ((liftWalk H p σ).copy rfl he) .nil := by
  rcases ReducedHomotopic.lift_to_doubleCover H hp σ with ⟨_, he, h⟩
  exact ⟨he, h⟩

/-- A reduced-null loop has an actual nullhomotopic continuous realization
in the support complex after lifting to the binary cover. -/
theorem liftPath_null [Fintype V] (s : V → V) (hs : ∀ v, H.Adj v (s v))
    {a : V} {p : H.Walk a a} (hp : ReducedHomotopic H p .nil) (σ : Bool) :
    ∃ he : sheetVertex a (toggleSheet p.length σ) = sheetVertex a σ,
      (walkPath H.bipartiteDoubleCover (doublePoint H s hs) (doubleEdgePath H s hs)
        ((liftWalk H p σ).copy rfl he)).Homotopic
        (Path.refl (doublePoint H s hs (sheetVertex a σ))) := by
  obtain ⟨he, hnull⟩ := liftWalk_null H hp σ
  refine ⟨he, ?_⟩
  exact (doubleCoverReducedEdgeClasses H s hs).nullhomotopic hnull _
    (doubleWalkPath_class H s hs _)

noncomputable section

variable [Fintype V] (s : V → V) (hs : ∀ v, H.Adj v (s v))

def supportLiftPath {a b : V} (p : H.Walk a b) (σ : Bool) :
    Path (doublePoint H s hs (sheetVertex a σ))
      (doublePoint H s hs (sheetVertex b (toggleSheet p.length σ))) :=
  walkPath H.bipartiteDoubleCover (doublePoint H s hs) (doubleEdgePath H s hs) (liftWalk H p σ)

set_option backward.isDefEq.respectTransparency false in
theorem doubleEdgePath_sheet_swap {a b : V} (h : H.Adj a b) (σ : Bool)
    (t : unitInterval) :
    SupportPair.swap H (doubleEdgePath H s hs (liftedEdge H h σ) t) =
      doubleEdgePath H s hs (liftedEdge H h (!σ)) t := by
  cases σ
  · exact congrArg (fun P => P t)
      (SupportPair.doubleEdgePath_map_swap H (hs a) h (hs b).symm)
  · have he := congrArg Path.symm
      (SupportPair.doubleEdgePath_map_swap H (hs b) h.symm (hs a).symm)
    simp only [Path.map_symm, Path.symm_symm] at he
    exact congrArg (fun P => P t) he

set_option backward.isDefEq.respectTransparency false in
/-- The lifted graph paths are exactly equivariant under the shore swap. -/
theorem supportLiftPath_swap {a b : V} (p : H.Walk a b) (σ : Bool) (t : unitInterval) :
    SupportPair.swap H (supportLiftPath H s hs p σ t) = supportLiftPath H s hs p (!σ) t := by
  induction p generalizing σ t with
  | nil => cases σ <;> rfl
  | @cons a b c h p ih =>
    change SupportPair.swap H
      (((doubleEdgePath H s hs (liftedEdge H h σ)).trans (supportLiftPath H s hs p (!σ))) t) =
      ((doubleEdgePath H s hs (liftedEdge H h (!σ))).trans
        (supportLiftPath H s hs p (!(!σ)))) t
    simp only [Path.trans_apply]
    split_ifs
    · exact doubleEdgePath_sheet_swap H s hs h σ _
    · exact ih (!σ) _

end

end AbelianTargets
