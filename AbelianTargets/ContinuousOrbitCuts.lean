import AbelianTargets.ContinuousPriorityCuts
import AbelianTargets.OrbitMarkerCuts

namespace AbelianTargets
noncomputable section
open Filter Topology

def markerPriorityExtension {X V : Type*} [TopologicalSpace X]
    (A : Set X) (c : A → V) (v : V) (x : X) : V := by
  classical
  exact if hx : x ∈ A then c ⟨x,hx⟩ else v

theorem continuous_markerPriorityExtension {X V : Type*}
    [TopologicalSpace X] [TopologicalSpace V] (A : Set X)
    (hA : IsClopen A) (c : A → V) (hc : Continuous c) (v : V) :
    Continuous (markerPriorityExtension A c v) := by
  classical
  apply continuous_def.mpr
  intro U hU
  have heq : markerPriorityExtension A c v ⁻¹' U =
      Subtype.val '' (c ⁻¹' U) ∪ (if v ∈ U then Aᶜ else ∅) := by
    ext x
    by_cases hx : x ∈ A
    · simp only [Set.mem_preimage,markerPriorityExtension,dif_pos hx,Set.mem_union,
        Set.mem_image]
      constructor
      · intro h
        exact Or.inl ⟨⟨x,hx⟩,h,rfl⟩
      · rintro (⟨a,ha,he⟩ | h)
        · subst x; exact ha
        · split_ifs at h <;> simp_all
    · simp only [Set.mem_preimage,markerPriorityExtension,dif_neg hx,Set.mem_union,
        Set.mem_image]
      constructor
      · intro h; right; simp [h,hx]
      · rintro (⟨a,ha,he⟩ | h)
        · exact (hx (he ▸ a.property)).elim
        · split_ifs at h with hv
          · exact hv
          · exact (Set.notMem_empty x h).elim
  rw [heq]
  apply (hA.isOpen.isOpenMap_subtype_val _ (hc.isOpen_preimage U hU)).union
  split_ifs
  · exact hA.compl.isOpen
  · exact isOpen_empty

def markerFlag {X : Type*} [TopologicalSpace X] (A : Set X) (x : X) : Bool := by
  classical
  exact if x ∈ A then true else false

theorem continuous_markerFlag {X : Type*} [TopologicalSpace X]
    (A : Set X) (hA : IsClopen A) : Continuous (markerFlag A) := by
  classical
  have h := continuous_markerPriorityExtension A hA (fun _ => true) continuous_const false
  simpa [markerPriorityExtension,markerFlag] using h

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]

def orbitCandidateBox (S : ℕ) (L : Fin d → ℕ) (g : Lattice d) : Finset (Lattice d) :=
  (Fintype.piFinset (fun i => Finset.Icc (-(S : ℤ)*(L i : ℤ)) ((S : ℤ)*(L i : ℤ)))).image
    (fun h => h+g)

def inactiveOrbitNeighbors (M : AnisotropicClopenMarkers d L X) (S : ℕ)
    (x : X) (g : Lattice d) : Finset (Lattice d) := by
  classical
  exact if g +ᵥ x ∈ M.markers then
    (orbitCandidateBox S L g).filter (fun h => h +ᵥ x ∈ M.markers) else {g}

/-- The actual finite neighbor lists on a fixed lattice index vary
continuously. Inactive indices have only their self-neighbor. -/
theorem continuous_inactiveOrbitNeighbors
    (M : AnisotropicClopenMarkers d L X) (S : ℕ) (g : Lattice d)
    [TopologicalSpace (Finset (Lattice d))] [DiscreteTopology (Finset (Lattice d))] :
    Continuous (fun x => inactiveOrbitNeighbors M S x g) := by
  classical
  let B := orbitCandidateBox S L g
  let mask (x : X) : B → Bool := fun h => markerFlag M.markers (h.val +ᵥ x)
  have hm : Continuous mask := continuous_pi (fun h =>
    (continuous_markerFlag M.markers M.clopen).comp (continuous_const_vadd h.val))
  have hg : Continuous (fun x => markerFlag M.markers (g +ᵥ x)) :=
    (continuous_markerFlag M.markers M.clopen).comp (continuous_const_vadd g)
  let output (u : Bool × (B → Bool)) : Finset (Lattice d) :=
    if u.1 then B.attach.filter (fun h => u.2 h = true) |>.image Subtype.val else {g}
  have ho : Continuous output := continuous_of_discreteTopology
  convert ho.comp (hg.prodMk hm) using 1
  funext x
  dsimp [output,mask,inactiveOrbitNeighbors]
  by_cases hx : g +ᵥ x ∈ M.markers
  · simp only [markerFlag,if_pos hx,if_true]
    ext h
    simp [B,and_comm]
  · simp [markerFlag,hx]

theorem continuous_orbitPriorityExtension {P : ℕ}
    (M : AnisotropicClopenMarkers d L X) (c : M.markers → Fin P)
    (hc : Continuous c) (v : Fin P) (g : Lattice d) :
    Continuous (fun x => markerPriorityExtension M.markers c v (g +ᵥ x)) :=
  (continuous_markerPriorityExtension M.markers M.clopen c hc v).comp
    (continuous_const_vadd g)

/-- Once the elementary neighborhood fields are packaged, the actual
fixed-index origin cuts are continuous. The hypotheses specify the exact
neighbor and priority data, rather than assuming continuity of the cuts.
This scratch file does not yet package the neighborhood fields itself. -/
theorem continuous_actualOrbitCuts {P : ℕ}
    [TopologicalSpace (Finset (Lattice d))] [DiscreteTopology (Finset (Lattice d))]
    (M : AnisotropicClopenMarkers d L X) (S : ℕ)
    (c : M.markers → Fin P) (hc : Continuous c) (v : Fin P)
    (N : X → PriorityNeighborhood (Lattice d) P)
    (hnear : ∀ x g,(N x).nearby g = inactiveOrbitNeighbors M S x g)
    (hpriority : ∀ x g,(N x).priority g = markerPriorityExtension M.markers c v (g +ᵥ x))
    (hP : 1 ≤ P) (hL : ∀ i,32*P ≤ L i) (i : Fin d) (n : ℕ) (g : Lattice d) :
    Continuous (fun x => priorityCutIteration (N x) hP (hL i) (fun h => h i) n g) := by
  apply continuous_priorityCutIteration N hP (hL i) (fun _ h => h i)
  · intro h
    simpa only [hnear] using continuous_inactiveOrbitNeighbors M S h
  · intro h
    simpa only [hpriority] using continuous_orbitPriorityExtension M c hc v h
  · intro h
    exact continuous_const

theorem continuous_actualOriginCuts {P : ℕ}
    [TopologicalSpace (Finset (Lattice d))] [DiscreteTopology (Finset (Lattice d))]
    (M : AnisotropicClopenMarkers d L X) (S : ℕ)
    (c : M.markers → Fin P) (hc : Continuous c) (v : Fin P)
    (N : X → PriorityNeighborhood (Lattice d) P)
    (hnear : ∀ x g,(N x).nearby g = inactiveOrbitNeighbors M S x g)
    (hpriority : ∀ x g,(N x).priority g = markerPriorityExtension M.markers c v (g +ᵥ x))
    (hP : 1 ≤ P) (hL : ∀ i,32*P ≤ L i) (i : Fin d) :
    Continuous (fun x => priorityCutIteration (N x) hP (hL i) (fun h => h i) P 0) :=
  continuous_actualOrbitCuts M S c hc v N hnear hpriority hP hL i P 0

end
end AbelianTargets
