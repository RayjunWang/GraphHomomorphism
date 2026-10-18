import AbelianTargets.SupportWitness
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.CompactOpen

/-!
# The literal parity presentation one-skeleton

Two vertices, two directed `a` edges switching the sheet, and two `t`
loops form the one-skeleton of the parity cover of the Baumslag--Solitar
presentation complex.  This file constructs its actual topological quotient.
-/

namespace AbelianTargets.ParitySkeleton

set_option backward.isDefEq.respectTransparency false

noncomputable section

abbrev Raw := Bool ⊕ ((Bool × Bool) × unitInterval)

/-- The generator label is false for `a` and true for `t`. -/
def edgeTarget (sheet generator : Bool) : Bool := if generator then sheet else !sheet

inductive Glue : Raw → Raw → Prop
  | source (sheet generator : Bool) : Glue (.inr ((sheet,generator),0)) (.inl sheet)
  | target (sheet generator : Bool) : Glue (.inr ((sheet,generator),1)) (.inl (edgeTarget sheet generator))

def Space := Quot Glue

instance : TopologicalSpace Space := inferInstanceAs (TopologicalSpace (Quot Glue))
instance : CompactSpace Space := inferInstanceAs (CompactSpace (Quot Glue))

def vertex (sheet : Bool) : Space := Quot.mk Glue (.inl sheet)

def aPath (sheet : Bool) : Path (vertex sheet) (vertex (!sheet)) where
  toFun t := Quot.mk Glue (.inr ((sheet,false),t))
  continuous_toFun := continuous_quot_mk.comp (by fun_prop)
  source' := Quot.sound (.source sheet false)
  target' := Quot.sound (.target sheet false)

def tPath (sheet : Bool) : Path (vertex sheet) (vertex sheet) where
  toFun t := Quot.mk Glue (.inr ((sheet,true),t))
  continuous_toFun := continuous_quot_mk.comp (by fun_prop)
  source' := Quot.sound (.source sheet true)
  target' := Quot.sound (.target sheet true)

def rawFlip : Raw → Raw
  | .inl sheet => .inl (!sheet)
  | .inr ((sheet,generator),t) => .inr ((!sheet,generator),t)

theorem rawFlip_glue {x y : Raw} (h : Glue x y) : Glue (rawFlip x) (rawFlip y) := by
  cases h with
  | source sheet generator => exact .source (!sheet) generator
  | target sheet generator =>
    cases generator <;> exact .target (!sheet) _

theorem continuous_rawFlip : Continuous rawFlip := by
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_inl.comp (continuous_of_discreteTopology)
  · change Continuous (fun z : (Bool×Bool)×unitInterval => Sum.inr ((!z.1.1,z.1.2),z.2))
    fun_prop

def deck : Space → Space := Quot.map rawFlip (fun _ _ h => rawFlip_glue h)

theorem continuous_deck : Continuous deck := continuous_quot_map _ continuous_rawFlip

@[simp] theorem deck_vertex (sheet : Bool) : deck (vertex sheet) = vertex (!sheet) := rfl

@[simp] theorem deck_deck (z : Space) : deck (deck z) = z := by
  induction z using Quot.ind with | _ z =>
  cases z with
  | inl sheet => cases sheet <;> rfl
  | inr z => rcases z with ⟨⟨sheet,generator⟩,t⟩; cases sheet <;> rfl

variable {Z : Type*} [TopologicalSpace Z]

/-- Continuous edge data with the actual one-skeleton incidence conditions. -/
structure MapData where
  point : Bool → Z
  a : ∀ sheet, Path (point sheet) (point (!sheet))
  t : ∀ sheet, Path (point sheet) (point sheet)

namespace MapData

def edgeMap (D : MapData (Z := Z)) (sg : Bool×Bool) : ContinuousMap unitInterval Z :=
  if sg.2 then (D.t sg.1).toContinuousMap else (D.a sg.1).toContinuousMap

def rawEval (D : MapData (Z := Z)) : Raw → Z
  | .inl sheet => D.point sheet
  | .inr (sg,t) => D.edgeMap sg t

theorem rawEval_glue (D : MapData (Z := Z)) {x y : Raw} (h : Glue x y) :
    D.rawEval x = D.rawEval y := by
  cases h with
  | source sheet generator => cases generator <;> simp [rawEval, edgeMap]
  | target sheet generator => cases generator <;> simp [rawEval, edgeMap, edgeTarget]

theorem continuous_rawEval (D : MapData (Z := Z)) : Continuous D.rawEval := by
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_of_discreteTopology
  · have he : Continuous D.edgeMap := continuous_of_discreteTopology
    exact continuous_eval.comp ((he.comp continuous_fst).prodMk continuous_snd)

def eval (D : MapData (Z := Z)) : Space → Z := Quot.lift D.rawEval (fun _ _ h => D.rawEval_glue h)

theorem continuous_eval (D : MapData (Z := Z)) : Continuous D.eval :=
  continuous_quot_lift _ D.continuous_rawEval

@[simp] theorem eval_vertex (D : MapData (Z := Z)) (sheet : Bool) : D.eval (vertex sheet) = D.point sheet := rfl

theorem aPath_map (D : MapData (Z := Z)) (sheet : Bool) :
    (aPath sheet).map D.continuous_eval = D.a sheet := by
  apply Path.ext
  funext t
  rfl

theorem tPath_map (D : MapData (Z := Z)) (sheet : Bool) :
    (tPath sheet).map D.continuous_eval = D.t sheet := by
  apply Path.ext
  funext t
  rfl

end MapData

end

end AbelianTargets.ParitySkeleton
