import AbelianTargets.DimensionEmbedding
import AbelianTargets.Statements

/-!
Finite carrier reindexing and the strict-decrease consequence of the exact
Proposition 7.7 statement. `Proposition77.lean` supplies the proved input.
-/

namespace AbelianTargets

theorem inClass_of_iso {d : ℕ} {V W : Type*}
    [TopologicalSpace V] [DiscreteTopology V] [TopologicalSpace W]
    {H : SimpleGraph V} {J : SimpleGraph W} (e : H ≃g J)
    (h : InClass d H) : InClass d J := by
  obtain ⟨c, hc, he⟩ := h
  refine ⟨fun x => e (c x),
    (continuous_of_discreteTopology (f := fun v => e v)).comp hc, ?_⟩
  intro x y hxy
  exact e.toHom.map_rel (he x y hxy)

theorem inClass_iff_of_iso {d : ℕ} {V W : Type*}
    [TopologicalSpace V] [DiscreteTopology V]
    [TopologicalSpace W] [DiscreteTopology W]
    {H : SimpleGraph V} {J : SimpleGraph W} (e : H ≃g J) :
    InClass d H ↔ InClass d J :=
  ⟨inClass_of_iso e, inClass_of_iso e.symm⟩

/-- Reindex a finite graph by the standard finite graph-code carrier. -/
noncomputable def finiteGraphCodeOf {V : Type*} [Fintype V]
    (H : SimpleGraph V) : FiniteGraphCode :=
  ⟨Fintype.card V, H.comap (Fintype.equivFin V).symm⟩

theorem inClass_finiteGraphCodeOf_iff {d : ℕ} {V : Type*} [Fintype V]
    [TopologicalSpace V] [DiscreteTopology V] (H : SimpleGraph V) :
    InClass d (finiteGraphCodeOf H).2 ↔ InClass d H := by
  exact inClass_iff_of_iso (SimpleGraph.Iso.comap (Fintype.equivFin V).symm H)

/-- The claimed strict decrease follows from the exact requested
Proposition 7.7, after actual finite-carrier reindexing. This does not prove
the twelve-tile obstruction separately; that proof is in `Proposition77.lean`. -/
theorem strictDecrease_of_proposition7_7 (h77 : Proposition77Statement) :
    ∀ d : ℕ, 1 ≤ d → finiteGraphClass (d + 1) ⊂ finiteGraphClass d := by
  apply finiteGraphClasses_strictDecrease_of_witnesses
  intro d hd
  let M := MarkerGraph d 4 (by decide)
  obtain ⟨hyes, hno⟩ := h77 d 4 hd (by decide)
  refine ⟨finiteGraphCodeOf M, (inClass_finiteGraphCodeOf_iff M).mpr hyes, ?_⟩
  intro hnext
  exact hno ((inClass_finiteGraphCodeOf_iff M).mp hnext)

end AbelianTargets
