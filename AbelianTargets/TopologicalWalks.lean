import AbelianTargets.ReducedWalks
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Passing the reduced walk presentation to topological path classes

This file proves the presentation argument used in Lemma 6.2.  A realization
of graph edges in a space, respecting reversal and filling every four-walk,
factors through the reduced graph-walk homotopy relation.  The geometric
edge maps and fillings themselves are constructed in `SupportGeometry`.
-/

namespace AbelianTargets

noncomputable section

variable {V X : Type*} [TopologicalSpace X] (H : SimpleGraph V) (f : V → X)

/-- A choice of topological path class for each oriented graph edge. -/
abbrev EdgeClasses := ∀ ⦃a b : V⦄, H.Adj a b → Path.Homotopic.Quotient (f a) (f b)

abbrev EdgePaths := ∀ ⦃a b : V⦄, H.Adj a b → Path (f a) (f b)

/-- An actual continuous path, obtained by concatenating realized graph edges. -/
def walkPath (E : EdgePaths H f) : {a b : V} → H.Walk a b → Path (f a) (f b)
  | _, _, .nil => Path.refl _
  | _, _, .cons h p => (E h).trans (walkPath E p)

/-- Concatenate the edge classes along an actual graph walk. -/
def walkClass (E : EdgeClasses H f) : {a b : V} → H.Walk a b →
    Path.Homotopic.Quotient (f a) (f b)
  | _, _, .nil => Path.Homotopic.Quotient.refl _
  | _, _, .cons h p => Path.Homotopic.Quotient.trans (E h) (walkClass E p)

@[simp] theorem walkClass_nil (E : EdgeClasses H f) (a : V) :
    walkClass H f E (SimpleGraph.Walk.nil : H.Walk a a) = Path.Homotopic.Quotient.refl (f a) := rfl

@[simp] theorem walkClass_cons (E : EdgeClasses H f) {a b c : V}
    (h : H.Adj a b) (p : H.Walk b c) :
    walkClass H f E (.cons h p) = Path.Homotopic.Quotient.trans (E h) (walkClass H f E p) := rfl

theorem walkPath_class (E : EdgePaths H f) {a b : V} (p : H.Walk a b) :
    Path.Homotopic.Quotient.mk (walkPath H f E p) =
      walkClass H f (fun {_ _} h => Path.Homotopic.Quotient.mk (E h)) p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simpa only [walkPath, walkClass_cons, Path.Homotopic.Quotient.mk_trans] using
      congrArg (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk (E h))) ih

theorem walkPath_copy (E : EdgePaths H f) {a b a' b' : V} (p : H.Walk a b)
    (ha : a = a') (hb : b = b') :
    walkPath H f E (p.copy ha hb) =
      (walkPath H f E p).cast (congrArg f ha.symm) (congrArg f hb.symm) := by
  subst a'
  subst b'
  rfl

theorem walkPath_append (E : EdgePaths H f) {a b c : V}
    (p : H.Walk a b) (q : H.Walk b c) :
    (walkPath H f E (p.append q)).Homotopic
      ((walkPath H f E p).trans (walkPath H f E q)) := by
  induction p with
  | nil => exact (Path.Homotopic.refl_trans _).symm
  | cons h p ih =>
    exact ((Path.Homotopic.refl (E h)).hcomp (ih q)).trans
      (Path.Homotopic.trans_assoc _ _ _).symm

theorem walkClass_append (E : EdgeClasses H f) {a b c : V}
    (p : H.Walk a b) (q : H.Walk b c) :
    walkClass H f E (p.append q) =
      Path.Homotopic.Quotient.trans (walkClass H f E p) (walkClass H f E q) := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp only [SimpleGraph.Walk.cons_append, walkClass_cons, ih,
      Path.Homotopic.Quotient.trans_assoc]

/-- The exact hypotheses a topological edge realization must check. -/
structure ReducedEdgeClasses where
  edge : EdgeClasses H f
  reverse : ∀ ⦃a b⦄ (h : H.Adj a b), edge h.symm = Path.Homotopic.Quotient.symm (edge h)
  four : ∀ ⦃a⦄ (p : H.Walk a a), p.length = 4 →
    walkClass H f edge p = Path.Homotopic.Quotient.refl (f a)

namespace ReducedEdgeClasses

variable {H f}

/-- Every generator of reduced walk homotopy becomes an actual equality of
topological path homotopy classes. -/
theorem respects_reducedHomotopic (E : ReducedEdgeClasses H f)
    {a b : V} {p q : H.Walk a b} (hpq : ReducedHomotopic H p q) :
    walkClass H f E.edge p = walkClass H f E.edge q := by
  induction hpq with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | append _ _ ih₁ ih₂ => simp only [walkClass_append, ih₁, ih₂]
  | spur h =>
    simp only [walkClass_cons, walkClass_nil, Path.Homotopic.Quotient.trans_refl]
    rw [E.reverse h]
    exact Path.Homotopic.Quotient.trans_symm _
  | four p hp => exact E.four p hp

/-- A reduced nullhomotopy gives a genuine topological nullhomotopy once
the concrete edge maps and square fillings have been checked. -/
theorem nullhomotopic (E : ReducedEdgeClasses H f) {a : V} {p : H.Walk a a}
    (hp : ReducedHomotopic H p .nil)
    (P : Path (f a) (f a)) (hP : Path.Homotopic.Quotient.mk P = walkClass H f E.edge p) :
    P.Homotopic (Path.refl (f a)) := by
  apply Path.Homotopic.Quotient.exact
  calc
    Path.Homotopic.Quotient.mk P = walkClass H f E.edge p := hP
    _ = walkClass H f E.edge .nil := E.respects_reducedHomotopic hp
    _ = Path.Homotopic.Quotient.mk (Path.refl (f a)) := rfl

end ReducedEdgeClasses

end

end AbelianTargets
