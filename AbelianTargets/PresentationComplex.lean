import AbelianTargets.PresentationSkeleton

/-!
# The compact parity presentation quotient and its support map

The two relation cells are cones on the literal boundary words
`t a t⁻¹ a⁻(2k+1)`. Their boundaries are glued to the actual one-skeleton.
No equality of target images is used as a source-space identification.
-/

namespace AbelianTargets.ParityPresentation

set_option backward.isDefEq.respectTransparency false

noncomputable section

open ParitySkeleton

def aLoop : Path (vertex false) (vertex false) := (aPath false).trans (aPath true)

def boundaryPlus (k : ℕ) : Path (vertex false) (vertex false) :=
  (((tPath false).trans (aPath false)).trans (tPath true).symm).trans
    ((pathLoopPower aLoop k).trans (aPath false)).symm

def boundary (k : ℕ) : ∀ sheet : Bool, Path (vertex sheet) (vertex sheet)
  | false => boundaryPlus k
  | true => (boundaryPlus k).map continuous_deck

theorem deck_boundary (k : ℕ) (sheet : Bool) (t : unitInterval) :
    deck (boundary k sheet t) = boundary k (!sheet) t := by
  cases sheet
  · rfl
  · exact deck_deck _

abbrev Raw := ParitySkeleton.Space ⊕ (Bool × (unitInterval × unitInterval))

inductive Glue (k : ℕ) : Raw → Raw → Prop
  | boundary (sheet : Bool) (t : unitInterval) :
      Glue k (.inr (sheet,(0,t))) (.inl (ParityPresentation.boundary k sheet t))
  | tip (sheet : Bool) (t : unitInterval) : Glue k (.inr (sheet,(1,t))) (.inl (vertex sheet))
  | sideZero (sheet : Bool) (r : unitInterval) : Glue k (.inr (sheet,(r,0))) (.inl (vertex sheet))
  | sideOne (sheet : Bool) (r : unitInterval) : Glue k (.inr (sheet,(r,1))) (.inl (vertex sheet))

def Space (k : ℕ) := Quot (Glue k)

instance (k : ℕ) : TopologicalSpace (Space k) := inferInstanceAs (TopologicalSpace (Quot (Glue k)))
instance (k : ℕ) : CompactSpace (Space k) := inferInstanceAs (CompactSpace (Quot (Glue k)))

def rawFlip : Raw → Raw
  | .inl z => .inl (ParitySkeleton.deck z)
  | .inr (sheet,ru) => .inr (!sheet,ru)

theorem rawFlip_glue {k : ℕ} {x y : Raw} (h : Glue k x y) : Glue k (rawFlip x) (rawFlip y) := by
  cases h with
  | boundary sheet t => simpa only [rawFlip, deck_boundary] using Glue.boundary (k := k) (!sheet) t
  | tip sheet t => exact .tip (!sheet) t
  | sideZero sheet r => exact .sideZero (!sheet) r
  | sideOne sheet r => exact .sideOne (!sheet) r

theorem continuous_rawFlip : Continuous rawFlip := by
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_inl.comp ParitySkeleton.continuous_deck
  · change Continuous (fun z : Bool × (unitInterval × unitInterval) => Sum.inr (!z.1,z.2))
    fun_prop

def deck (k : ℕ) : Space k → Space k := Quot.map rawFlip (fun _ _ h => rawFlip_glue h)

theorem continuous_deck (k : ℕ) : Continuous (deck k) := continuous_quot_map _ continuous_rawFlip

@[simp] theorem deck_deck (k : ℕ) (z : Space k) : deck k (deck k z) = z := by
  induction z using Quot.ind with | _ z =>
  cases z with
  | inl z => exact congrArg (Quot.mk (Glue k) ∘ Sum.inl) (ParitySkeleton.deck_deck z)
  | inr z => rcases z with ⟨sheet,ru⟩; cases sheet <;> rfl

variable {V : Type*} [Fintype V] {H : SimpleGraph V}

def skeletonData (D : SupportTorsionData H) : ParitySkeleton.MapData (Z := SupportPair H) where
  point sheet := if sheet then SupportPair.swap H D.base else D.base
  a sheet := by cases sheet; exact D.a; exact D.b
  t sheet := Path.refl _

theorem skeletonEval_deck (D : SupportTorsionData H) (z : ParitySkeleton.Space) :
    (skeletonData D).eval (ParitySkeleton.deck z) =
      SupportPair.swap H ((skeletonData D).eval z) := by
  induction z using Quot.ind with | _ z =>
  cases z with
  | inl sheet =>
    cases sheet
    · rfl
    · exact (SupportPair.swap_swap H D.base).symm
  | inr z =>
    rcases z with ⟨⟨sheet,generator⟩,t⟩
    cases generator <;> cases sheet
    · exact D.b_swap t
    · exact ((congrArg (SupportPair.swap H) (D.b_swap t)).trans (SupportPair.swap_swap H (D.a t))).symm
    · rfl
    · exact (SupportPair.swap_swap H D.base).symm

private theorem pathLoopPower_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : X} (P : Path p p) {f : X → Y} (hf : Continuous f) (n : ℕ) :
    (pathLoopPower P n).map hf = pathLoopPower (P.map hf) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (P.trans (pathLoopPower P n)).map hf = (P.map hf).trans (pathLoopPower (P.map hf) n)
    rw [Path.map_trans, ih]

theorem boundary_image_null (D : SupportTorsionData H) :
    ((boundaryPlus D.power).map (skeletonData D).continuous_eval).Homotopic (Path.refl D.base) := by
  simp only [boundaryPlus, Path.map_trans, ← Path.map_symm, pathLoopPower_map,
    aLoop, ParitySkeleton.MapData.aPath_map, ParitySkeleton.MapData.tPath_map]
  change (((Path.refl D.base).trans D.a).trans (Path.refl (SupportPair.swap H D.base))).trans
      ((pathLoopPower (D.a.trans D.b) D.power).trans D.a).symm |>.Homotopic (Path.refl D.base)
  have hhead := ((Path.Homotopic.refl_trans D.a).hcomp
    (Path.Homotopic.refl (Path.refl (SupportPair.swap H D.base)))).trans (Path.Homotopic.trans_refl D.a)
  exact (hhead.hcomp (Path.Homotopic.refl _)).trans D.boundary_null

def plusFilling (D : SupportTorsionData H) :
    ((boundaryPlus D.power).map (skeletonData D).continuous_eval).Homotopy (Path.refl D.base) :=
  (boundary_image_null D).some

def cellMap (D : SupportTorsionData H) : Bool → ContinuousMap (unitInterval × unitInterval) (SupportPair H)
  | false => (plusFilling D).toHomotopy.toContinuousMap
  | true => ⟨fun ru => SupportPair.swap H (plusFilling D ru),
      (SupportPair.continuous_swap H).comp (plusFilling D).continuous⟩

theorem cellMap_boundary (D : SupportTorsionData H) (sheet : Bool) (t : unitInterval) :
    cellMap D sheet (0,t) = (skeletonData D).eval (boundary D.power sheet t) := by
  cases sheet
  · exact (plusFilling D).apply_zero t
  · change SupportPair.swap H (plusFilling D (0,t)) =
      (skeletonData D).eval (ParitySkeleton.deck (boundaryPlus D.power t))
    rw [(plusFilling D).apply_zero, skeletonEval_deck]
    rfl

theorem cellMap_tip (D : SupportTorsionData H) (sheet : Bool) (t : unitInterval) :
    cellMap D sheet (1,t) = (skeletonData D).eval (vertex sheet) := by
  cases sheet
  · exact (plusFilling D).apply_one t
  · exact congrArg (SupportPair.swap H) ((plusFilling D).apply_one t)

theorem cellMap_sideZero (D : SupportTorsionData H) (sheet : Bool) (r : unitInterval) :
    cellMap D sheet (r,0) = (skeletonData D).eval (vertex sheet) := by
  cases sheet
  · exact (plusFilling D).source r
  · exact congrArg (SupportPair.swap H) ((plusFilling D).source r)

theorem cellMap_sideOne (D : SupportTorsionData H) (sheet : Bool) (r : unitInterval) :
    cellMap D sheet (r,1) = (skeletonData D).eval (vertex sheet) := by
  cases sheet
  · exact (plusFilling D).target r
  · exact congrArg (SupportPair.swap H) ((plusFilling D).target r)

def rawEval (D : SupportTorsionData H) : Raw → SupportPair H
  | .inl z => (skeletonData D).eval z
  | .inr (sheet,ru) => cellMap D sheet ru

theorem rawEval_glue (D : SupportTorsionData H) {x y : Raw} (h : Glue D.power x y) :
    rawEval D x = rawEval D y := by
  cases h with
  | boundary sheet t => exact cellMap_boundary D sheet t
  | tip sheet t => exact cellMap_tip D sheet t
  | sideZero sheet r => exact cellMap_sideZero D sheet r
  | sideOne sheet r => exact cellMap_sideOne D sheet r

theorem continuous_rawEval (D : SupportTorsionData H) : Continuous (rawEval D) := by
  apply continuous_sum_dom.mpr
  constructor
  · exact (skeletonData D).continuous_eval
  · have hc : Continuous (cellMap D) := continuous_of_discreteTopology
    exact continuous_eval.comp ((hc.comp continuous_fst).prodMk continuous_snd)

/-- The actual map `η` from the compact parity presentation quotient to
the support complex, obtained by gluing the two filled relation cells. -/
def eta (D : SupportTorsionData H) : Space D.power → SupportPair H :=
  Quot.lift (rawEval D) (fun _ _ h => rawEval_glue D h)

theorem continuous_eta (D : SupportTorsionData H) : Continuous (eta D) :=
  continuous_quot_lift _ (continuous_rawEval D)

theorem eta_deck (D : SupportTorsionData H) (z : Space D.power) :
    eta D (deck D.power z) = SupportPair.swap H (eta D z) := by
  induction z using Quot.ind with | _ z =>
  cases z with
  | inl z => exact skeletonEval_deck D z
  | inr z =>
    rcases z with ⟨sheet,ru⟩
    cases sheet
    · rfl
    · exact (SupportPair.swap_swap H (plusFilling D ru)).symm

theorem deck_free (D : SupportTorsionData H) (z : Space D.power) : deck D.power z ≠ z := by
  intro h
  have he := congrArg (eta D) h
  rw [eta_deck D] at he
  exact SupportPair.swap_ne_self H (eta D z) he

end

end AbelianTargets.ParityPresentation
