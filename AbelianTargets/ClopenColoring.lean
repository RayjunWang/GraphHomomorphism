import AbelianTargets.ClopenMarkers
import Mathlib.Data.Fintype.Card
import Mathlib.Topology.Instances.Discrete

/-!
# Continuous finite coloring from a countable clopen independent cover

Iterated relative clopen maximal independent sets give a proper coloring
with one more color than the degree bound. The relative construction and
the finite neighbor-count contradiction are proved explicitly.
-/

namespace AbelianTargets

noncomputable section

variable {X : Type*} [TopologicalSpace X] (G : SimpleGraph X) (C : ℕ → Set X)

def relativeMarkerSet (R : Set X) : Set X :=
  maximalMarkerSet G (fun n => C n ∩ R)

omit [TopologicalSpace X] in
theorem relativeMarkerSet_subset (R : Set X) : relativeMarkerSet G C R ⊆ R := by
  have hstage : ∀ n,markerAccumulation G (fun n => C n ∩ R) n ⊆ R := by
    intro n
    induction n with
    | zero => exact Set.empty_subset R
    | succ n ih =>
        rintro x (hx | hx)
        · exact ih hx
        · exact hx.1.2
  intro x hx
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
  exact hstage n hn

omit [TopologicalSpace X] in
theorem relativeMarkerSet_independent (R : Set X)
    (hindep : ∀ n,GraphIndependent G (C n)) : GraphIndependent G (relativeMarkerSet G C R) :=
  maximalMarkerSet_independent _ (fun n x hx y hy => hindep n x hx.1 y hy.1)

omit [TopologicalSpace X] in
theorem relativeMarkerSet_maximal (R : Set X) (hcover : ∀ x,∃ n,x ∈ C n) :
    ∀ x,x ∈ R → x ∉ relativeMarkerSet G C R →
      ∃ a ∈ relativeMarkerSet G C R,G.Adj a x := by
  intro x hx hxA
  obtain ⟨n,hxn⟩ := hcover x
  have hn : x ∈ NeighborSet G (markerAccumulation G (fun n => C n ∩ R) n) := by
    by_contra hnot
    exact hxA (Set.mem_iUnion.mpr ⟨n+1,Or.inr ⟨⟨hxn,hx⟩,hnot⟩⟩)
  obtain ⟨a,ha,hadj⟩ := hn
  exact ⟨a,Set.mem_iUnion.mpr ⟨n,ha⟩,hadj⟩

theorem relativeMarkerSet_clopen (R : Set X) (hR : IsClopen R)
    (hclopen : ∀ n,IsClopen (C n)) (hindep : ∀ n,GraphIndependent G (C n))
    (hcover : ∀ x,∃ n,x ∈ C n)
    (hneigh : ∀ S,IsClopen S → IsClopen (NeighborSet G S)) :
    IsClopen (relativeMarkerSet G C R) := by
  have hc : ∀ n,IsClopen (C n ∩ R) := fun n => (hclopen n).inter hR
  have hi : ∀ n,GraphIndependent G (C n ∩ R) :=
    fun n x hx y hy => hindep n x hx.1 y hy.1
  have heq : (relativeMarkerSet G C R)ᶜ = Rᶜ ∪
      ⋃ n,NeighborSet G (markerAccumulation G (fun n => C n ∩ R) n) := by
    ext x
    constructor
    · intro hx
      by_cases hxR : x ∈ R
      · right
        obtain ⟨n,hxn⟩ := hcover x
        apply Set.mem_iUnion.mpr
        refine ⟨n,?_⟩
        by_contra hnot
        exact hx (Set.mem_iUnion.mpr ⟨n+1,Or.inr ⟨⟨hxn,hxR⟩,hnot⟩⟩)
      · exact Or.inl hxR
    · rintro (hx | hx) hxA
      · exact hx (relativeMarkerSet_subset G C R hxA)
      · obtain ⟨n,a,ha,hadj⟩ := Set.mem_iUnion.mp hx
        exact relativeMarkerSet_independent G C R hindep a
          (Set.mem_iUnion.mpr ⟨n,ha⟩) x hxA hadj
  have ho : IsOpen (relativeMarkerSet G C R) :=
    isOpen_iUnion (fun n => (markerAccumulation_clopen _ hc hneigh n).isOpen)
  have hco : IsOpen (relativeMarkerSet G C R)ᶜ := by
    rw [heq]
    exact hR.compl.isOpen.union (isOpen_iUnion (fun n =>
      (hneigh _ (markerAccumulation_clopen _ hc hneigh n)).isOpen))
  exact ⟨by simpa only [compl_compl] using hco.isClosed_compl,ho⟩

def coloredUnion : ℕ → Set X
  | 0 => ∅
  | n+1 => coloredUnion n ∪ relativeMarkerSet G C (coloredUnion n)ᶜ

def colorClass (n : ℕ) : Set X := relativeMarkerSet G C (coloredUnion G C n)ᶜ

omit [TopologicalSpace X] in
theorem coloredUnion_monotone : Monotone (coloredUnion G C) :=
  monotone_nat_of_le_succ (fun _ _ hx => Or.inl hx)

omit [TopologicalSpace X] in
theorem colorClass_subset_succ (n : ℕ) : colorClass G C n ⊆ coloredUnion G C (n+1) :=
  fun _ hx => Or.inr hx

omit [TopologicalSpace X] in
theorem colorClasses_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (colorClass G C i) (colorClass G C j) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hW := coloredUnion_monotone G C (show i+1 ≤ j by omega)
      (colorClass_subset_succ G C i hxi)
    exact relativeMarkerSet_subset G C _ hxj hW
  · have hW := coloredUnion_monotone G C (show j+1 ≤ i by omega)
      (colorClass_subset_succ G C j hxj)
    exact relativeMarkerSet_subset G C _ hxi hW

theorem coloredUnion_clopen (hclopen : ∀ n,IsClopen (C n))
    (hindep : ∀ n,GraphIndependent G (C n)) (hcover : ∀ x,∃ n,x ∈ C n)
    (hneigh : ∀ S,IsClopen S → IsClopen (NeighborSet G S)) (n : ℕ) :
    IsClopen (coloredUnion G C n) := by
  induction n with
  | zero => exact isClopen_empty
  | succ n ih => exact ih.union (relativeMarkerSet_clopen G C _ ih.compl hclopen hindep hcover hneigh)

theorem colorClass_clopen (hclopen : ∀ n,IsClopen (C n))
    (hindep : ∀ n,GraphIndependent G (C n)) (hcover : ∀ x,∃ n,x ∈ C n)
    (hneigh : ∀ S,IsClopen S → IsClopen (NeighborSet G S)) (n : ℕ) :
    IsClopen (colorClass G C n) :=
  relativeMarkerSet_clopen G C _ (coloredUnion_clopen G C hclopen hindep hcover hneigh n).compl
    hclopen hindep hcover hneigh

omit [TopologicalSpace X] in
theorem mem_coloredUnion_iff (n : ℕ) (x : X) :
    x ∈ coloredUnion G C n ↔ ∃ i,i < n ∧ x ∈ colorClass G C i := by
  induction n with
  | zero => simp [coloredUnion]
  | succ n ih =>
      change (x ∈ coloredUnion G C n ∨ x ∈ colorClass G C n) ↔ _
      rw [ih]
      constructor
      · rintro (⟨i,hi,hx⟩ | hx)
        · exact ⟨i,by omega,hx⟩
        · exact ⟨n,by omega,hx⟩
      · rintro ⟨i,hi,hx⟩
        by_cases heq : i = n
        · exact Or.inr (heq ▸ hx)
        · exact Or.inl ⟨i,by omega,hx⟩

omit [TopologicalSpace X] in
theorem coloredUnion_covers (hcover : ∀ x,∃ n,x ∈ C n) (Δ : ℕ)
    (neighbors : X → Finset X) (hdegree : ∀ x,(neighbors x).card ≤ Δ)
    (hadj : ∀ x y,G.Adj y x → y ∈ neighbors x) :
    coloredUnion G C (Δ+1) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  by_contra hx
  have hsmall : ∀ i : Fin (Δ+1),x ∉ coloredUnion G C i := by
    intro i hi
    exact hx (coloredUnion_monotone G C (by omega) hi)
  have hneighbor : ∀ i : Fin (Δ+1),∃ a,a ∈ colorClass G C i ∧ G.Adj a x := by
    intro i
    apply relativeMarkerSet_maximal G C _ hcover x (hsmall i)
    intro hi
    exact hx (coloredUnion_monotone G C (show i.val+1 ≤ Δ+1 by omega)
      (colorClass_subset_succ G C i hi))
  choose a ha hadja using hneighbor
  let f : Fin (Δ+1) → {y // y ∈ neighbors x} := fun i => ⟨a i,hadj x (a i) (hadja i)⟩
  have hinj : Function.Injective f := by
    intro i j heq
    by_contra hne
    have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have he : a i = a j := congrArg Subtype.val heq
    exact Set.disjoint_left.mp (colorClasses_disjoint G C hval) (ha i) (he ▸ ha j)
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin,Fintype.card_coe] at hc
  have := hdegree x
  omega

/-- The continuous `(Δ+1)`-coloring assertion of Lemma 3.1. A finite
neighbor list with the degree bound is an explicit representation of
the paper's finite-degree hypothesis. -/
theorem exists_continuous_finite_coloring
    (hclopen : ∀ n,IsClopen (C n)) (hindep : ∀ n,GraphIndependent G (C n))
    (hcover : ∀ x,∃ n,x ∈ C n)
    (hneigh : ∀ S,IsClopen S → IsClopen (NeighborSet G S))
    (Δ : ℕ) (neighbors : X → Finset X) (hdegree : ∀ x,(neighbors x).card ≤ Δ)
    (hadj : ∀ x y,G.Adj y x → y ∈ neighbors x) :
    ∃ c : X → Fin (Δ+1),Continuous c ∧ ∀ x y,G.Adj x y → c x ≠ c y := by
  classical
  have hfull := coloredUnion_covers G C hcover Δ neighbors hdegree hadj
  have hexists : ∀ x : X,∃ i : Fin (Δ+1),x ∈ colorClass G C i := by
    intro x
    have hx : x ∈ coloredUnion G C (Δ+1) := by rw [hfull]; trivial
    obtain ⟨i,hi,hxi⟩ := (mem_coloredUnion_iff G C (Δ+1) x).mp hx
    exact ⟨⟨i,hi⟩,hxi⟩
  choose c hc using hexists
  have hfiber : ∀ (x : X) (i : Fin (Δ+1)),c x = i ↔ x ∈ colorClass G C i := by
    intro x i
    constructor
    · intro heq
      simpa only [heq] using hc x
    · intro hx
      by_contra hne
      have hval : (c x).val ≠ i.val := fun h => hne (Fin.ext h)
      exact Set.disjoint_left.mp (colorClasses_disjoint G C hval) (hc x) hx
  refine ⟨c,?_,?_⟩
  · apply continuous_def.mpr
    intro S _hS
    have heq : c ⁻¹' S = ⋃ i : Fin (Δ+1),⋃ (_hi : i ∈ S),colorClass G C i := by
      ext x
      simp only [Set.mem_preimage,Set.mem_iUnion]
      constructor
      · intro hx
        exact ⟨c x,hx,hc x⟩
      · rintro ⟨i,hi,hx⟩
        exact (hfiber x i).mpr hx ▸ hi
    rw [heq]
    exact isOpen_iUnion (fun i => isOpen_iUnion (fun _ =>
      (colorClass_clopen G C hclopen hindep hcover hneigh i).isOpen))
  · intro x y hxy heq
    have hy : y ∈ colorClass G C (c x) := by simpa only [heq] using hc y
    exact relativeMarkerSet_independent G C _ hindep x (hc x) y hy hxy

end

end AbelianTargets

