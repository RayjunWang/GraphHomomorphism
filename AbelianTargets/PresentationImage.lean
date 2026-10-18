import AbelianTargets.PresentationComplex

/-!
# A compact metric parity model obtained from the actual presentation map

The presentation quotient has literal relation-cell attachments. Its image
under the already constructed map into the support complex is a compact
metric parity space. This image construction does not assert that the
presentation quotient itself has been proved Hausdorff or metrizable.
-/

namespace AbelianTargets.ParityPresentation

noncomputable section

variable {V : Type*} [Fintype V] {H : SimpleGraph V}

/-- The support image of the literal parity presentation quotient. -/
def Image (D : SupportTorsionData H) := {z : SupportPair H // z ∈ Set.range (eta D)}

instance (D : SupportTorsionData H) : TopologicalSpace (Image D) :=
  inferInstanceAs (TopologicalSpace (Set.range (eta D)))

instance (D : SupportTorsionData H) : MetricSpace (Image D) :=
  inferInstanceAs (MetricSpace (Set.range (eta D)))

instance (D : SupportTorsionData H) : CompactSpace (Image D) :=
  isCompact_iff_compactSpace.mp (isCompact_range (continuous_eta D))

/-- The actual presentation map, with codomain restricted to its image. -/
def etaImage (D : SupportTorsionData H) (z : Space D.power) : Image D :=
  ⟨eta D z, z, rfl⟩

theorem continuous_etaImage (D : SupportTorsionData H) : Continuous (etaImage D) :=
  (continuous_eta D).subtype_mk _

theorem etaImage_surjective (D : SupportTorsionData H) : Function.Surjective (etaImage D) := by
  rintro ⟨z,w,rfl⟩
  exact ⟨w,rfl⟩

/-- Swap preserves the image because the original map is equivariant. -/
def imageSwap (D : SupportTorsionData H) (z : Image D) : Image D := by
  refine ⟨SupportPair.swap H z.1, ?_⟩
  obtain ⟨w,hw⟩ := z.2
  exact ⟨deck D.power w, (eta_deck D w).trans (congrArg (SupportPair.swap H) hw)⟩

@[simp] theorem imageSwap_val (D : SupportTorsionData H) (z : Image D) :
    (imageSwap D z).1 = SupportPair.swap H z.1 := rfl

@[simp] theorem imageSwap_imageSwap (D : SupportTorsionData H) (z : Image D) :
    imageSwap D (imageSwap D z) = z := by
  apply Subtype.ext
  exact SupportPair.swap_swap H z.1

theorem isometry_imageSwap (D : SupportTorsionData H) : Isometry (imageSwap D) := by
  intro z w
  exact SupportPair.isometry_swap H z.1 w.1

theorem continuous_imageSwap (D : SupportTorsionData H) : Continuous (imageSwap D) :=
  (isometry_imageSwap D).continuous

theorem imageSwap_ne_self (D : SupportTorsionData H) (z : Image D) : imageSwap D z ≠ z := by
  intro he
  exact SupportPair.swap_ne_self H z.1 (congrArg Subtype.val he)

theorem etaImage_deck (D : SupportTorsionData H) (z : Space D.power) :
    etaImage D (deck D.power z) = imageSwap D (etaImage D z) := by
  apply Subtype.ext
  exact eta_deck D z

/-- The concrete coordinate support model on the compact metric image. -/
def imageModel (D : SupportTorsionData H) : SupportModel H (imageSwap D) where
  p z := SupportPair.left H z.1
  q z := SupportPair.right H z.1
  continuous_p := (SupportPair.continuous_left H).comp continuous_subtype_val
  compatible z := SupportPair.compatible H z.1
  first_swap z := rfl

/-- Continuous graph rounding from approximate maps into this concrete model.
The approximate parity maps remain an explicit geometric input. -/
theorem hasContinuousHom_of_approximateImage
    {d : ℕ} {X : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]
    [Nonempty V] [TopologicalSpace V] (D : SupportTorsionData H)
    (approx : ApproximateParityMaps (d := d) X (Image D) (imageSwap D)) :
    HasContinuousHom (d := d) (X := X) H :=
  hasContinuousHom_of_supportModel (imageModel D) approx

end

end AbelianTargets.ParityPresentation
