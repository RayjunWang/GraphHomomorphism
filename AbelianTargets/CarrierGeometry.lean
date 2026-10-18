import AbelianTargets.CarrierTriangulation
import AbelianTargets.SupportLipschitz
import Mathlib.Data.Finset.Powerset

set_option backward.isDefEq.respectTransparency false

/-!
# The actual finite barycentric interval carrier

The carrier is the union of the probability-simplex faces specified by
the finite fan triangulation. Its vertices and simplex charts are actual
points and continuous maps. No contraction is included as an assumption.
-/

namespace AbelianTargets

open scoped BigOperators NNReal

noncomputable section

namespace Probability

variable {V : Type*} [Fintype V]

theorem supportedOn_iff_zero {p : Probability V} {A : Set V} :
    p.SupportedOn A ↔ ∀ v, v ∉ A → p.mass v = 0 := by
  constructor
  · intro h v hv
    by_contra hne
    exact hv (h v (lt_of_le_of_ne (p.nonneg v) (Ne.symm hne)))
  · intro h v hv
    by_contra hnot
    rw [h v hnot] at hv
    exact (lt_irrefl _ hv)

theorem isClosed_supportedOn (A : Set V) : IsClosed {p : Probability V | p.SupportedOn A} := by
  have he : {p : Probability V | p.SupportedOn A} =
      ⋂ v : V, {p | v ∈ A ∨ p.mass v = 0} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter, supportedOn_iff_zero]
    constructor
    · intro h v
      by_cases hv : v ∈ A
      · exact Or.inl hv
      · exact Or.inr (h v hv)
    · intro h v hv
      exact (h v).resolve_left hv
  rw [he]
  apply isClosed_iInter
  intro v
  by_cases hv : v ∈ A
  · simp [hv]
  · simpa only [hv, false_or] using
      isClosed_eq (continuous_mass_apply v) continuous_const

theorem dist_le_one (p q : Probability V) : dist p q ≤ 1 := by
  change dist p.mass q.mass ≤ 1
  apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).2
  intro v
  rw [Real.dist_eq, abs_le]
  constructor
  · have hp := p.nonneg v
    have hq := q.mass_le_one v
    linarith
  · have hp := p.mass_le_one v
    have hq := q.nonneg v
    linarith

end Probability

namespace IntervalCarriers

abbrev CarrierVertex (K : ℕ) (A B : ℤ) := {v : Vertex // v ∈ carrierVertices K A B}

instance (K : ℕ) (A B : ℤ) : Fintype (CarrierVertex K A B) := by
  classical
  exact Fintype.ofFinset (carrierVertices K A B) (by simp)

def simplexFaces (m K : ℕ) (A B : ℤ) : Finset (Finset (CarrierVertex K A B)) := by
  classical
  exact Finset.univ.powerset.filter (fun s => CarrierFace m K A B (s.image Subtype.val))

theorem mem_simplexFaces {m K : ℕ} {A B : ℤ} (s : Finset (CarrierVertex K A B)) :
    s ∈ simplexFaces m K A B ↔ CarrierFace m K A B (s.image Subtype.val) := by
  classical
  simp only [simplexFaces, Finset.mem_filter, Finset.mem_powerset]
  exact and_iff_right (Finset.subset_univ s)

def InRealization (m K : ℕ) (A B : ℤ) (p : Probability (CarrierVertex K A B)) : Prop :=
  ∃ s ∈ simplexFaces m K A B, p.SupportedOn (s : Set _)

def Realization (m K : ℕ) (A B : ℤ) :=
  {p : Probability (CarrierVertex K A B) // InRealization m K A B p}

instance (m K : ℕ) (A B : ℤ) : TopologicalSpace (Realization m K A B) :=
  inferInstanceAs (TopologicalSpace (Subtype _))

instance (m K : ℕ) (A B : ℤ) : MetricSpace (Realization m K A B) :=
  inferInstanceAs (MetricSpace (Subtype _))

theorem isClosed_inRealization (m K : ℕ) (A B : ℤ) :
    IsClosed {p : Probability (CarrierVertex K A B) | InRealization m K A B p} := by
  have he : {p : Probability (CarrierVertex K A B) | InRealization m K A B p} =
      ⋃ s ∈ simplexFaces m K A B, {p | p.SupportedOn (s : Set _)} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, InRealization]
    constructor
    · rintro ⟨s,hs,hp⟩
      exact ⟨s,hs,hp⟩
    · rintro ⟨s,hs,hp⟩
      exact ⟨s,hs,hp⟩
  rw [he]
  exact isClosed_biUnion_finset (fun s _ => Probability.isClosed_supportedOn (V := CarrierVertex K A B) (s : Set _))

instance (m K : ℕ) (A B : ℤ) : CompactSpace (Realization m K A B) :=
  isCompact_iff_compactSpace.mp (isClosed_inRealization m K A B).isCompact

def point {m K : ℕ} {A B : ℤ} (v : CarrierVertex K A B) : Realization m K A B := by
  refine ⟨Probability.dirac v, {v}, ?_, Probability.supportedOn_dirac v (by simp)⟩
  apply (mem_simplexFaces {v}).mpr
  classical
  simp only [Finset.image_singleton]
  exact Or.inl ⟨v.1,v.2,Finset.Subset.refl _⟩

def faceMix {m K : ℕ} {A B : ℤ} (s : Finset (CarrierVertex K A B))
    (hs : CarrierFace m K A B (s.image Subtype.val)) (p q : Realization m K A B)
    (hp : p.1.SupportedOn (s : Set _)) (hq : q.1.SupportedOn (s : Set _))
    (r : unitInterval) : Realization m K A B :=
  ⟨Probability.mix p.1 q.1 r,s,(mem_simplexFaces s).mpr hs,Probability.supportedOn_mix hp hq r⟩

theorem continuous_faceMix {m K : ℕ} {A B : ℤ} (s : Finset (CarrierVertex K A B))
    (hs : CarrierFace m K A B (s.image Subtype.val))
    {X : Type*} [TopologicalSpace X] (p q : X → Realization m K A B)
    (hp : ∀ x, (p x).1.SupportedOn (s : Set _)) (hq : ∀ x, (q x).1.SupportedOn (s : Set _))
    (r : X → unitInterval) (hpc : Continuous p) (hqc : Continuous q) (hrc : Continuous r) :
    Continuous (fun x => faceMix s hs (p x) (q x) (hp x) (hq x) (r x)) :=
  (Probability.continuous_mix_of_continuous (continuous_subtype_val.comp hpc)
    (continuous_subtype_val.comp hqc) hrc).subtype_mk _

def edgePath {m K : ℕ} {A B : ℤ} (v w : CarrierVertex K A B)
    (hface : CarrierFace m K A B {v.1,w.1}) : Path (point (m := m) v) (point w) where
  toFun r := faceMix {v,w} (by simpa using hface) (point v) (point w)
    (Probability.supportedOn_dirac v (by simp)) (Probability.supportedOn_dirac w (by simp)) r
  continuous_toFun := continuous_faceMix {v,w} (by simpa using hface)
    (fun _ => point v) (fun _ => point w)
    (fun _ => Probability.supportedOn_dirac v (by simp))
    (fun _ => Probability.supportedOn_dirac w (by simp)) id
    continuous_const continuous_const continuous_id
  source' := by apply Subtype.ext; exact Probability.mix_zero _ _
  target' := by apply Subtype.ext; exact Probability.mix_one _ _

theorem edgePath_lipschitz {m K : ℕ} {A B : ℤ} (v w : CarrierVertex K A B)
    (hface : CarrierFace m K A B {v.1,w.1}) : LipschitzWith 1 (edgePath v w hface) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  have he : dist (Probability.mix (Probability.dirac v) (Probability.dirac w) r)
      (Probability.mix (Probability.dirac v) (Probability.dirac w) s) =
      dist (FixedSlots.mix (Probability.dirac v).mass (Probability.dirac w).mass r)
        (FixedSlots.mix (Probability.dirac v).mass (Probability.dirac w).mass s) := rfl
  change dist (Probability.mix (Probability.dirac v) (Probability.dirac w) r)
      (Probability.mix (Probability.dirac v) (Probability.dirac w) s) ≤ _
  rw [he]
  exact (FixedSlots.mix_lipschitz _ _ 1 (Probability.dist_le_one _ _)).dist_le_mul r s

end IntervalCarriers

end

end AbelianTargets
