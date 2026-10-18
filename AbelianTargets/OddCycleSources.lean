import AbelianTargets.MixedCompactSources
import AbelianTargets.ShiftTransitivity
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Odd cycle sources

The one-dimensional compact factor in the odd-dimensional source
construction contains an odd closed walk. The proof below establishes the
graph-theoretic parity criterion directly and uses actual free-shift
transitivity to exclude a continuous two-coloring.
-/

namespace AbelianTargets

open SimpleGraph

theorem exists_twoColorHom_of_even_loops_reachable
    {V : Type*} (G : SimpleGraph V) (b : V)
    (hreach : ∀ v, G.Reachable b v)
    (heven : ∀ (p : G.Walk b b), p.length % 2 = 0) :
    Nonempty (G →g SimpleGraph.completeGraph (Fin 2)) := by
  classical
  let p : (v : V) → G.Walk b v := fun v => (hreach v).some
  refine ⟨{ toFun := fun v => ⟨(p v).length % 2, Nat.mod_lt _ (by decide)⟩
            map_rel' := ?_ }⟩
  intro v w hvw
  change (⟨(p v).length % 2, _⟩ : Fin 2) ≠ ⟨(p w).length % 2, _⟩
  intro heq
  have heq' := congrArg Fin.val heq
  change (p v).length % 2 = (p w).length % 2 at heq'
  have h := heven (((p v).append (Walk.cons hvw (Walk.nil))).append ((p w).reverse))
  simp only [Walk.length_append, Walk.length_cons, Walk.length_nil,
    Walk.length_reverse] at h
  omega

/-- A graph with no odd closed walk has an ordinary two-coloring.
The component choices are ordinary classical choices of actual walks. -/
theorem exists_twoColorHom_of_even_loops
    {V : Type*} (G : SimpleGraph V)
    (heven : ∀ b, ∀ (p : G.Walk b b), p.length % 2 = 0) :
    Nonempty (G →g SimpleGraph.completeGraph (Fin 2)) := by
  classical
  have hf : ∀ C : G.ConnectedComponent,
      Nonempty (C.toSimpleGraph →g SimpleGraph.completeGraph (Fin 2)) := by
    intro C
    let b : C := ⟨C.out, C.out_eq⟩
    apply exists_twoColorHom_of_even_loops_reachable C.toSimpleGraph b
    · exact fun v => C.connected_toSimpleGraph.preconnected b v
    · intro p
      have hp := heven b.val (p.map C.toSimpleGraph_hom)
      exact (congrArg (fun n : ℕ => n % 2 = 0)
        (SimpleGraph.Walk.length_map C.toSimpleGraph_hom p)).mp hp
  exact ⟨G.homOfConnectedComponents (fun C => Classical.choice (hf C))⟩

/-- There is no continuous proper two-coloring of the free binary
shift of the integers. The even translation has a transitive cyclic
action, so a two-coloring would be both constant and proper. -/
theorem not_continuous_freeShift_one_twoColor :
    ¬HasContinuousHom (d := 1) (X := FreeShift 1)
      (SimpleGraph.completeGraph (Fin 2)) := by
  rintro ⟨c, hc, hproper⟩
  let e : Lattice 1 := unitVector 0
  have hstep : ∀ x : FreeShift 1, c (e +ᵥ x) ≠ c x := by
    intro x
    exact (hproper x (e +ᵥ x) ⟨0, Or.inl rfl⟩).symm
  have hdouble : ∀ x : FreeShift 1, c ((e + e) +ᵥ x) = c x := by
    intro x
    have h₁ := hstep x
    have h₂ := hstep (e +ᵥ x)
    rw [add_vadd]
    apply Fin.ext
    have h₁' : (c (e +ᵥ x)).val ≠ (c x).val := fun h => h₁ (Fin.ext h)
    have h₂' : (c (e +ᵥ (e +ᵥ x))).val ≠ (c (e +ᵥ x)).val := fun h => h₂ (Fin.ext h)
    have := (c x).isLt
    have := (c (e +ᵥ x)).isLt
    have := (c (e +ᵥ (e +ᵥ x))).isLt
    omega
  let t : Unit → Lattice 1 := fun _ => e + e
  have ht : ∀ i, t i ≠ 0 := by
    intro i h
    have h0 := congrFun h (0 : Fin 1)
    norm_num [t, e, unitVector] at h0
  letI : AddAction.IsTopologicallyTransitive ℤ (CyclicProductShift 1 t) :=
    cyclicProductShift_transitive (by decide) t ht
  let c' : CyclicProductShift 1 t → Fin 2 := fun x => c (x ())
  have hc' : Continuous c' := hc.comp (continuous_apply ())
  have hstep' : ∀ x, c' ((1 : ℤ) +ᵥ x) = c' x := by
    intro x
    change c ((1 : ℤ) • t () +ᵥ x ()) = c (x ())
    simpa only [one_zsmul, t] using hdouble (x ())
  have hconstant := cyclic_invariant_discrete_coloring_constant c' hc' hstep'
  let x : FreeShift 1 := originFreeConfiguration 1
  exact hstep x (hconstant (fun _ => e +ᵥ x) (fun _ => x))

/-- Every graph in the paper's class `𝓗₁` contains an actual odd closed
walk; this assertion uses no external reference axiom. -/
theorem inClass_one_has_odd_closedWalk
    {V : Type*} [TopologicalSpace V] [DiscreteTopology V]
    (G : SimpleGraph V) (hG : InClass 1 G) :
    ∃ b, ∃ p : G.Walk b b, Odd p.length := by
  classical
  by_contra hnone
  have heven : ∀ b, ∀ p : G.Walk b b, p.length % 2 = 0 := by
    intro b p
    exact Nat.not_odd_iff.mp (fun hp => hnone ⟨b, p, hp⟩)
  obtain ⟨β⟩ := exists_twoColorHom_of_even_loops G heven
  obtain ⟨c, hc, hproper⟩ := hG
  apply not_continuous_freeShift_one_twoColor
  refine ⟨fun x => β (c x), ?_, ?_⟩
  · exact continuous_of_discreteTopology.comp hc
  · intro x y hxy
    exact β.map_rel (hproper x y hxy)

theorem odd_closedWalk_length_ge_three
    {V : Type*} {G : SimpleGraph V} {b : V}
    (p : G.Walk b b) (hp : Odd p.length) : 3 ≤ p.length := by
  have hmod := Nat.odd_iff.mp hp
  have hone : p.length ≠ 1 := by
    intro h
    exact G.irrefl (Walk.adj_of_length_eq_one h)
  omega

/-- A closed walk of length at least two induces a homomorphism
from the literal cycle graph of the same length, including the closing edge. -/
def closedWalkCycleHom {V : Type*} {G : SimpleGraph V} {b : V} {n : ℕ}
    (p : G.Walk b b) (hlen : p.length = n + 2) :
    SimpleGraph.cycleGraph (n + 2) →g G := by
  have hnext : ∀ i : Fin (n + 2), G.Adj (p.getVert i.val) (p.getVert (i + 1).val) := by
    intro i
    have ha := p.adj_getVert_succ (by rw [hlen]; exact i.isLt)
    have hval : (i + 1).val = (i.val + 1) % (n + 2) := by
      simp only [Fin.val_add, Fin.val_one]
    by_cases hi : i.val + 1 < n + 2
    · rw [hval, Nat.mod_eq_of_lt hi]
      exact ha
    · have hlast : i.val + 1 = n + 2 := by omega
      rw [hval, hlast, Nat.mod_self]
      have hv : p.getVert (i.val + 1) = p.getVert 0 := by
        rw [hlast, ← hlen, Walk.getVert_length, Walk.getVert_zero]
      rwa [hv] at ha
  refine { toFun := fun i => p.getVert i.val
           map_rel' := ?_ }
  intro u v huv
  obtain h | h := SimpleGraph.cycleGraph_adj.mp huv
  · have hu : u = v + 1 := (sub_eq_iff_eq_add').mp h
    rw [hu]
    exact (hnext v).symm
  · have hv : v = u + 1 := (sub_eq_iff_eq_add').mp h
    rw [hv]
    exact hnext u

theorem inClass_one_odd_cycle_source
    {V : Type*} [TopologicalSpace V] [DiscreteTopology V]
    (G : SimpleGraph V) (hG : InClass 1 G) :
    ∃ r : ℕ, Odd r ∧ 3 ≤ r ∧ Nonempty (SimpleGraph.cycleGraph r →g G) := by
  obtain ⟨b, p, hp⟩ := inClass_one_has_odd_closedWalk G hG
  have hlen := odd_closedWalk_length_ge_three p hp
  let n := p.length - 2
  have hn : p.length = n + 2 := by dsimp [n]; omega
  exact ⟨p.length, hp, hlen, ⟨hn.symm ▸ closedWalkCycleHom p hn⟩⟩

end AbelianTargets
