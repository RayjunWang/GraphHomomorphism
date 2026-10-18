import AbelianTargets.CarrierGeometry
import AbelianTargets.SimplexMetricGluing
import Mathlib.Topology.LocallyFinite

/-!
# Concrete continuous maps from finite probability-simplex carriers

Continuous face charts agreeing on their literal intersections produce an
actual global continuous map. The construction chooses a supporting face,
and the agreement proof makes its value independent of that choice.
-/

namespace AbelianTargets

noncomputable section

abbrev ProbabilityFace {V : Type*} [Fintype V] (s : Finset V) :=
  {p : Probability V // p.SupportedOn (s : Set V)}

structure SimplicialChartData {V : Type*} [Fintype V] (F : Finset (Finset V))
    (Z : Type*) [TopologicalSpace Z] where
  chart : ∀ s, s ∈ F → ProbabilityFace s → Z
  continuous_chart : ∀ s hs, Continuous (chart s hs)
  agree : ∀ (s : Finset V) (hs : s ∈ F) (t : Finset V) (ht : t ∈ F)
    (p : Probability V) (hps : p.SupportedOn (s : Set V))
    (hpt : p.SupportedOn (t : Set V)), chart s hs ⟨p,hps⟩=chart t ht ⟨p,hpt⟩

namespace SimplicialChartData

variable {V Z : Type*} [Fintype V] [TopologicalSpace Z] {F : Finset (Finset V)}

def eval (D : SimplicialChartData F Z) (p : SimplicialCarrier F) : Z :=
  D.chart (Classical.choose p.2) (Classical.choose_spec p.2).1
    ⟨p.1,(Classical.choose_spec p.2).2⟩

theorem eval_eq_chart (D : SimplicialChartData F Z) (p : SimplicialCarrier F)
    (s : Finset V) (hs : s ∈ F) (hp : p.1.SupportedOn (s : Set V)) :
    D.eval p=D.chart s hs ⟨p.1,hp⟩ :=
  D.agree _ _ s hs p.1 _ hp

def faceSet (s : Finset V) : Set (SimplicialCarrier F) := {p | p.1.SupportedOn (s : Set V)}

theorem isClosed_faceSet (s : Finset V) : IsClosed (faceSet (F := F) s) :=
  (Probability.isClosed_supportedOn (s : Set V)).preimage continuous_subtype_val

theorem continuousOn_eval_face (D : SimplicialChartData F Z) (s : Finset V) (hs : s ∈ F) :
    ContinuousOn D.eval (faceSet (F := F) s) := by
  apply continuousOn_iff_continuous_restrict.mpr
  let lift : faceSet (F := F) s → ProbabilityFace s := fun p => ⟨p.1.1,p.2⟩
  have hlift : Continuous lift :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hc := (D.continuous_chart s hs).comp hlift
  apply hc.congr
  intro p
  exact (D.eval_eq_chart p.1 s hs p.2).symm

theorem continuous_eval (D : SimplicialChartData F Z) : Continuous D.eval := by
  classical
  letI : Fintype {s : Finset V // s ∈ F} := Fintype.ofFinset F (by simp)
  apply (locallyFinite_of_finite (fun s : {s : Finset V // s ∈ F} => faceSet (F := F) s.1)).continuous
    _ (fun s => isClosed_faceSet s.1) (fun s => D.continuousOn_eval_face s.1 s.2)
  ext p
  simp only [Set.mem_iUnion,Set.mem_univ,iff_true]
  obtain ⟨s,hs,hp⟩ := p.2
  exact ⟨⟨s,hs⟩,hp⟩

end SimplicialChartData

end

end AbelianTargets
