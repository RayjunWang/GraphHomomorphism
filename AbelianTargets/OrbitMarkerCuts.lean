import AbelianTargets.MarkerCutNeighborhoods
import AbelianTargets.AtlasBoxes
import Mathlib.Data.Finset.Preimage

/-!
# Priority cuts in actual orbit coordinates

A free action identifies each orbit marker with its lattice coordinate.
Pulling the actual finite marker neighborhood back along this injection
gives the priority input on that orbit. Coordinatewise iteration then
constructs literal `RectangularCuts`, including the side bounds and
separation of cuts of nearby markers. The retained-box CW subdivision
is a separate construction.
-/

namespace AbelianTargets
noncomputable section

def PriorityNeighborhood.pullback {I J : Type*} {P : ℕ}
    (N : PriorityNeighborhood J P) (f : I → J) (hf : Function.Injective f) :
    PriorityNeighborhood I P where
  nearby i := (N.nearby (f i)).preimage f hf.injOn
  bound i := by
    classical
    rw [Finset.card_preimage]
    exact (Finset.card_filter_le _ _).trans (N.bound (f i))
  symmetric i j hij := by
    apply Finset.mem_preimage.mpr
    exact N.symmetric _ _ (Finset.mem_preimage.mp hij)
  priority i := N.priority (f i)
  proper i j hij hne := N.proper _ _ (Finset.mem_preimage.mp hij)
    (fun h => hne (hf h))

@[simp] theorem PriorityNeighborhood.mem_pullback {I J : Type*} {P : ℕ}
    (N : PriorityNeighborhood J P) (f : I → J) (hf : Function.Injective f) (i j : I) :
    j ∈ (N.pullback f hf).nearby i ↔ f j ∈ N.nearby (f i) :=
  Finset.mem_preimage (hf := hf.injOn)

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X]

abbrev OrbitMarkers (M : AnisotropicClopenMarkers d L X) (x : X) :=
  {a : Lattice d // a +ᵥ x ∈ M.markers}

def orbitMarkerPoint (M : AnisotropicClopenMarkers d L X) (x : X)
    (a : OrbitMarkers M x) : M.markers := ⟨a.val +ᵥ x,a.property⟩

theorem orbitMarkerPoint_injective (M : AnisotropicClopenMarkers d L X) (x : X)
    (free : IsFree (G := Lattice d) (X := X)) :
    Function.Injective (orbitMarkerPoint M x) := by
  intro a b hab
  have hfix : (a.val-b.val) +ᵥ (b.val +ᵥ x) = b.val +ᵥ x := by
    rw [← add_vadd,sub_add_cancel]
    exact congrArg Subtype.val hab
  exact Subtype.ext (sub_eq_zero.mp (free _ _ hfix))

def orbitPriorityNeighborhood (M : AnisotropicClopenMarkers d L X) (x : X)
    (free : IsFree (G := Lattice d) (X := X)) {P : ℕ}
    (N : PriorityNeighborhood M.markers P) : PriorityNeighborhood (OrbitMarkers M x) P :=
  N.pullback (orbitMarkerPoint M x) (orbitMarkerPoint_injective M x free)

theorem orbitMarkerProximity_adj_of_close
    (M : AnisotropicClopenMarkers d L X) (x : X) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X)) {a b : OrbitMarkers M x}
    (hne : a ≠ b) (hclose : ∀ i,|a.val i-b.val i| ≤ (S*L i : ℕ)) :
    (markerProximityGraph M S free).Adj (orbitMarkerPoint M x a) (orbitMarkerPoint M x b) := by
  refine ⟨b.val-a.val,(mem_anisotropicDisplacements (fun i => S*L i) _).mpr ⟨?_,?_⟩,?_⟩
  · intro i
    simpa only [Pi.sub_apply,abs_sub_comm] using hclose i
  · intro hzero
    exact hne (Subtype.ext (sub_eq_zero.mp hzero).symm)
  · change (b.val-a.val) +ᵥ (a.val +ᵥ x) = b.val +ᵥ x
    rw [← add_vadd,sub_add_cancel]

def priorityRectangularCuts {A : Set (Lattice d)} {P : ℕ}
    (N : PriorityNeighborhood A P) (hP : 1 ≤ P)
    (hL : ∀ i,32*P ≤ L i) : RectangularCuts L A where
  lower a i := (priorityCutIteration N hP (hL i) (fun b => b.val i) P a).1
  upper a i := (priorityCutIteration N hP (hL i) (fun b => b.val i) P a).2
  lower_bound a i := by
    have h := priorityCutIteration_bounds N hP (hL i) (fun b => b.val i) P a
    exact ⟨h.1,h.2.1⟩
  upper_bound a i := by
    have h := priorityCutIteration_bounds N hP (hL i) (fun b => b.val i) P a
    exact ⟨h.2.2.1,h.2.2.2⟩

theorem priorityRectangularCuts_separated {A : Set (Lattice d)} {P : ℕ}
    (N : PriorityNeighborhood A P) (hP : 1 ≤ P) (hL : ∀ i,32*P ≤ L i)
    {a b : A} (hnear : b ∈ N.nearby a) (hne : a ≠ b) (i : Fin d) (s t : Bool) :
    ((L i/(16*P) : ℕ) : ℤ) <
      |cutSide ((priorityRectangularCuts N hP hL).lower a i,
          (priorityRectangularCuts N hP hL).upper a i) s -
        cutSide ((priorityRectangularCuts N hP hL).lower b i,
          (priorityRectangularCuts N hP hL).upper b i) t| :=
  priorityCuts_separated N hP (hL i) (fun a => a.val i) hnear hne s t

/-- Coordinate proximity in the actual orbit suffices for cut separation;
there is no supplied numerical or combinatorial separation assumption. -/
theorem orbitPriorityRectangularCuts_separated {P : ℕ}
    (M : AnisotropicClopenMarkers d L X) (x : X) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X))
    (N : PriorityNeighborhood M.markers P)
    (hN : ∀ u v,v ∈ N.nearby u ↔ u = v ∨ (markerProximityGraph M S free).Adj u v)
    (hP : 1 ≤ P) (hL : ∀ i,32*P ≤ L i)
    {a b : OrbitMarkers M x} (hne : a ≠ b)
    (hclose : ∀ i,|a.val i-b.val i| ≤ (S*L i : ℕ)) (i : Fin d) (s t : Bool) :
    ((L i/(16*P) : ℕ) : ℤ) <
      |cutSide ((priorityRectangularCuts (orbitPriorityNeighborhood M x free N) hP hL).lower a i,
          (priorityRectangularCuts (orbitPriorityNeighborhood M x free N) hP hL).upper a i) s -
        cutSide ((priorityRectangularCuts (orbitPriorityNeighborhood M x free N) hP hL).lower b i,
          (priorityRectangularCuts (orbitPriorityNeighborhood M x free N) hP hL).upper b i) t| := by
  apply priorityRectangularCuts_separated _ hP hL _ hne i s t
  apply (Finset.mem_preimage (hf := (orbitMarkerPoint_injective M x free).injOn)).mpr
  exact (hN _ _).mpr (Or.inr (orbitMarkerProximity_adj_of_close M x S free hne hclose))

/-- Actual continuous marker priorities produce orbit-coordinate cuts.
The conclusion preserves the exact ambient marker-proximity relation.
Continuity of these cuts in compatible local orbit charts and subdivision
into a CW atlas remain further obligations. -/
theorem exists_orbitMarkerCuts
    [ContinuousVAdd (Lattice d) X] [T1Space X] [SecondCountableTopology X]
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (S : ℕ)
    (hscale : ∀ i,32*((2*S+1)^d) ≤ L i)
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X)) (x : X) :
    ∃ N : PriorityNeighborhood (OrbitMarkers M x) ((2*S+1)^d),
      (∀ a b,b ∈ N.nearby a ↔ a = b ∨
        (markerProximityGraph M S free).Adj (orbitMarkerPoint M x a) (orbitMarkerPoint M x b)) ∧
      ∃ cuts : RectangularCuts L {a : Lattice d | a +ᵥ x ∈ M.markers},
        cuts = priorityRectangularCuts N (Nat.one_le_pow _ _ (by omega)) hscale := by
  classical
  obtain ⟨N,hcontinuous,hnear⟩ := exists_markerPriorityNeighborhood M hL S zeroDim free
  let O := orbitPriorityNeighborhood M x free N
  refine ⟨O,?_,priorityRectangularCuts O (Nat.one_le_pow _ _ (by omega)) hscale,rfl⟩
  intro a b
  simp only [O,orbitPriorityNeighborhood,PriorityNeighborhood.mem_pullback]
  rw [hnear]
  exact or_congr (orbitMarkerPoint_injective M x free).eq_iff Iff.rfl

end
end AbelianTargets
