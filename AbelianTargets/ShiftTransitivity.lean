import AbelianTargets.FreeShiftDensity
import AbelianTargets.Dimension
import Mathlib.Data.Set.Finite.Lattice

/-!
# Transitivity of a common nonzero translation on active free-shift factors

Finite cylinder supports in finitely many factors can be separated by one
integer multiple of the prescribed translations. Their combined patterns
then extend to free configurations. This is the cylinder argument in
Lemma 7.6, proved without a dynamical reference axiom.
-/

namespace AbelianTargets

noncomputable section

/-- Invariance under the generator of a cyclic action implies invariance
under every integer iterate, including negative iterates. -/
theorem cyclic_coloring_invariant_all
    {Y V : Type*} [AddAction ℤ Y] (c : Y → V)
    (hstep : ∀ x, c ((1 : ℤ) +ᵥ x) = c x) :
    ∀ (n : ℤ) (x : Y), c (n +ᵥ x) = c x := by
  have hnat : ∀ n : ℕ, ∀ x : Y, c ((n : ℤ) +ᵥ x) = c x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Nat.cast_add, Nat.cast_one, add_comm (n : ℤ) 1, add_vadd, hstep, ih]
  intro n x
  cases n with
  | ofNat n => exact hnat n x
  | negSucc n =>
    have hh := hnat (n + 1) (Int.negSucc n +ᵥ x)
    rw [← add_vadd] at hh
    have hn : ((n + 1 : ℕ) : ℤ) + Int.negSucc n = 0 := by omega
    rw [hn, zero_vadd] at hh
    exact hh.symm

/-- A continuous discrete coloring invariant under one step of a
topologically transitive cyclic action is constant. -/
theorem cyclic_invariant_discrete_coloring_constant
    {Y V : Type*} [TopologicalSpace Y] [AddAction ℤ Y]
    [AddAction.IsTopologicallyTransitive ℤ Y]
    [TopologicalSpace V] [DiscreteTopology V]
    (c : Y → V) (hc : Continuous c) (hstep : ∀ x, c ((1 : ℤ) +ᵥ x) = c x) :
    ∀ x y, c x = c y :=
  invariant_discrete_coloring_constant c hc (cyclic_coloring_invariant_all c hstep)

theorem exists_freeShift_cylinder_subset {d : ℕ}
    {U : Set (FreeShift d)} (hU : IsOpen U) {x : FreeShift d} (hx : x ∈ U) :
    ∃ F : Finset (Lattice d),
      ∀ y : FreeShift d, (∀ u ∈ F, y.val u = x.val u) → y ∈ U := by
  classical
  obtain ⟨W, hW, hWU⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hU
  have hxW : x.val ∈ W := by rw [← hWU] at hx; exact hx
  obtain ⟨F, A, hA, hsub⟩ := isOpen_pi_iff.mp hW x.val hxW
  refine ⟨F, fun y hy => ?_⟩
  rw [← hWU]
  apply hsub
  intro u hu
  rw [hy u hu]
  exact (hA u hu).2

theorem zsmul_lattice_injective {d : ℕ} {t : Lattice d} (ht : t ≠ 0) :
    Function.Injective (fun n : ℤ => n • t) := by
  have hj : ∃ j, t j ≠ 0 := by
    by_contra h
    push Not at h
    exact ht (funext h)
  obtain ⟨j, hj⟩ := hj
  intro a b hab
  have hh := congrFun hab j
  simp only [Pi.smul_apply, zsmul_eq_mul] at hh
  exact mul_right_cancel₀ hj hh

theorem exists_common_separating_multiple
    {I : Type*} [Fintype I] {d : ℕ} (t : I → Lattice d)
    (ht : ∀ i, t i ≠ 0) (F G : I → Finset (Lattice d)) :
    ∃ n : ℤ, ∀ i, ∀ a ∈ F i, ∀ b ∈ G i, a ≠ b + n • t i := by
  classical
  let D : I → Finset (Lattice d) := fun i =>
    ((F i).product (G i)).image (fun z => z.1 - z.2)
  let B : I → Set ℤ := fun i => (fun n : ℤ => n • t i) ⁻¹' (D i : Set (Lattice d))
  have hB : ∀ i, (B i).Finite := fun i =>
    Set.Finite.preimage (zsmul_lattice_injective (ht i)).injOn (D i).finite_toSet
  obtain ⟨n, hn⟩ := (Set.finite_iUnion hB).exists_notMem
  refine ⟨n, fun i a ha b hb hab => ?_⟩
  apply hn
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  change n • t i ∈ D i
  apply Finset.mem_image.mpr
  refine ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, ?_⟩
  rw [hab, add_sub_cancel_left]

theorem exists_product_freeShift_pattern_bridge
    {I : Type*} [Fintype I] {d : ℕ} (hd : 1 ≤ d)
    (t : I → Lattice d) (ht : ∀ i, t i ≠ 0)
    (F G : I → Finset (Lattice d)) (x y : I → FreeShift d) :
    ∃ (n : ℤ) (z : I → FreeShift d),
      (∀ i, ∀ u ∈ F i, (z i).val u = (x i).val u) ∧
      ∀ i, ∀ u ∈ G i, shift (n • t i) (z i).val u = (y i).val u := by
  classical
  obtain ⟨n, hn⟩ := exists_common_separating_multiple t ht F G
  let P : I → ShiftSpace d := fun i u =>
    if u ∈ F i then (x i).val u else (y i).val (u - n • t i)
  let K : I → Finset (Lattice d) := fun i =>
    F i ∪ (G i).image (fun u => u + n • t i)
  choose z hz using (fun i => exists_freeShift_extension hd (K i) (P i))
  refine ⟨n, z, ?_, ?_⟩
  · intro i u hu
    rw [hz i u (Finset.mem_union_left _ hu)]
    simp [P, hu]
  · intro i u hu
    have hnot : u + n • t i ∉ F i := by
      intro h
      exact hn i (u + n • t i) h u hu rfl
    change (z i).val (u + n • t i) = (y i).val u
    rw [hz i _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩))]
    simp only [P, if_neg hnot, add_sub_cancel_right]

/-- A finite product of free shifts, equipped with the cyclic action
whose translation in factor `i` is `t i`. Only active factors are included. -/
def CyclicProductShift {I : Type*} (d : ℕ) (_t : I → Lattice d) := I → FreeShift d

instance cyclicProductShiftTopology {I : Type*} {d : ℕ} (t : I → Lattice d) :
    TopologicalSpace (CyclicProductShift d t) :=
  inferInstanceAs (TopologicalSpace (I → FreeShift d))

instance cyclicProductShiftAction {I : Type*} {d : ℕ} (t : I → Lattice d) :
    AddAction ℤ (CyclicProductShift d t) where
  vadd n x := fun i => (n • t i) +ᵥ x i
  zero_vadd x := by
    funext i
    change (0 : ℤ) • t i +ᵥ x i = x i
    simp
  add_vadd n m x := by
    funext i
    change (n + m) • t i +ᵥ x i = n • t i +ᵥ (m • t i +ᵥ x i)
    rw [add_smul, add_vadd]

theorem cyclicProductShift_transitive
    {I : Type*} [Fintype I] {d : ℕ} (hd : 1 ≤ d)
    (t : I → Lattice d) (ht : ∀ i, t i ≠ 0) :
    AddAction.IsTopologicallyTransitive ℤ (CyclicProductShift d t) := by
  classical
  letI : AddAction ℤ (I → FreeShift d) := cyclicProductShiftAction t
  constructor
  intro U V hU hUne hV hVne
  obtain ⟨x, hx⟩ := hUne
  obtain ⟨y, hy⟩ := hVne
  obtain ⟨A, hA, hAsub⟩ := isOpen_pi_iff'.mp hU x hx
  obtain ⟨B, hB, hBsub⟩ := isOpen_pi_iff'.mp hV y hy
  choose F hF using (fun i => exists_freeShift_cylinder_subset (hA i).1 (hA i).2)
  choose G hG using (fun i => exists_freeShift_cylinder_subset (hB i).1 (hB i).2)
  obtain ⟨n, z, hzx, hzy⟩ := exists_product_freeShift_pattern_bridge hd t ht F G x y
  have hzU : z ∈ U := hAsub (fun i _ => hF i (z i) (hzx i))
  have hzV : n +ᵥ (z : CyclicProductShift d t) ∈ V :=
    hBsub (fun i _ => hG i ((n • t i) +ᵥ z i) (hzy i))
  refine ⟨n, n +ᵥ (z : CyclicProductShift d t), ?_, hzV⟩
  exact Set.mem_vadd_set.mpr ⟨z, hzU, rfl⟩

/-- Invariance under one nonzero lattice translation makes a continuous
discrete coloring of the full free shift constant. -/
theorem freeShift_invariant_nezero_constant
    {d : ℕ} (hd : 1 ≤ d) (t : Lattice d) (ht : t ≠ 0)
    {V : Type*} [TopologicalSpace V] [DiscreteTopology V]
    (c : FreeShift d → V) (hc : Continuous c)
    (hinv : ∀ x, c (t +ᵥ x) = c x) : ∀ x y, c x = c y := by
  let t' : Unit → Lattice d := fun _ => t
  let Y := CyclicProductShift d t'
  letI : AddAction.IsTopologicallyTransitive ℤ Y :=
    cyclicProductShift_transitive hd t' (fun _ => ht)
  let c' : Y → V := fun z => c (z ())
  have hc' : Continuous c' := hc.comp (continuous_apply ())
  have hi' : ∀ z : Y, c' ((1 : ℤ) +ᵥ z) = c' z := by
    intro z
    change c ((1 : ℤ) • t +ᵥ z ()) = c (z ())
    simpa only [one_smul] using hinv (z ())
  have hconst := cyclic_invariant_discrete_coloring_constant c' hc' hi'
  intro x y
  exact hconst (fun _ => x) (fun _ => y)

end

end AbelianTargets
