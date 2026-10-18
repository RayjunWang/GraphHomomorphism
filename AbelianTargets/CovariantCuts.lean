import AbelianTargets.AtlasCuts

/-!
# Translation-covariant local cut selection

Offsets depend only on the earlier cuts relative to the candidate
interval's left endpoint. Thus the choice commutes literally with
translation, even though its noncomputable finite choice need not be
continuous on a larger unrelated space of cut configurations.
-/

namespace AbelianTargets

noncomputable section

def relativeCuts (a : ℤ) (earlier : Finset ℤ) : Finset ℤ :=
  earlier.image (fun b => b-a)

@[simp] theorem relativeCuts_card (a : ℤ) (earlier : Finset ℤ) :
    (relativeCuts a earlier).card = earlier.card := by
  apply Finset.card_image_of_injective
  intro x y h
  dsimp at h
  omega

def selectedOffset {P L : ℕ} (hP : 1 ≤ P) (hL : 32*P ≤ L)
    (earlier : Finset ℤ) (hcard : earlier.card ≤ 2*P) : ℤ :=
  Classical.choose (exists_separated_cut hP hL 0 earlier hcard)

theorem selectedOffset_spec {P L : ℕ} (hP : 1 ≤ P) (hL : 32*P ≤ L)
    (earlier : Finset ℤ) (hcard : earlier.card ≤ 2*P) :
    0 ≤ selectedOffset hP hL earlier hcard ∧
      selectedOffset hP hL earlier hcard ≤ L ∧
      ∀ b ∈ earlier,((L/(16*P) : ℕ) : ℤ) < |selectedOffset hP hL earlier hcard-b| := by
  simpa only [selectedOffset,zero_add] using Classical.choose_spec (exists_separated_cut hP hL 0 earlier hcard)

def selectedCut {P L : ℕ} (hP : 1 ≤ P) (hL : 32*P ≤ L)
    (a : ℤ) (earlier : Finset ℤ) (hcard : earlier.card ≤ 2*P) : ℤ :=
  a + selectedOffset hP hL (relativeCuts a earlier) (by simpa using hcard)

theorem selectedCut_spec {P L : ℕ} (hP : 1 ≤ P) (hL : 32*P ≤ L)
    (a : ℤ) (earlier : Finset ℤ) (hcard : earlier.card ≤ 2*P) :
    a ≤ selectedCut hP hL a earlier hcard ∧
      selectedCut hP hL a earlier hcard ≤ a+L ∧
      ∀ b ∈ earlier,((L/(16*P) : ℕ) : ℤ) < |selectedCut hP hL a earlier hcard-b| := by
  obtain ⟨hlo,hhi,hsep⟩ := selectedOffset_spec hP hL (relativeCuts a earlier)
    (by simpa using hcard)
  refine ⟨by unfold selectedCut; omega,by unfold selectedCut; omega,?_⟩
  intro b hb
  have h := hsep (b-a) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
  have he : selectedCut hP hL a earlier hcard-b =
      selectedOffset hP hL (relativeCuts a earlier) (by simpa using hcard)-(b-a) := by
    unfold selectedCut
    ring
  rw [he]
  exact h

def translatedCuts (s : ℤ) (earlier : Finset ℤ) : Finset ℤ :=
  earlier.image (fun b => b+s)

@[simp] theorem translatedCuts_card (s : ℤ) (earlier : Finset ℤ) :
    (translatedCuts s earlier).card = earlier.card := by
  apply Finset.card_image_of_injective
  intro x y h
  dsimp at h
  omega

theorem relativeCuts_translated (a s : ℤ) (earlier : Finset ℤ) :
    relativeCuts (a+s) (translatedCuts s earlier) = relativeCuts a earlier := by
  unfold relativeCuts translatedCuts
  rw [Finset.image_image]
  congr 1
  funext b
  dsimp
  ring

/-- The local cut choice commutes exactly with integer translation. -/
theorem selectedCut_translated {P L : ℕ} (hP : 1 ≤ P) (hL : 32*P ≤ L)
    (a s : ℤ) (earlier : Finset ℤ) (hcard : earlier.card ≤ 2*P) :
    selectedCut hP hL (a+s) (translatedCuts s earlier) (by simpa using hcard) =
      selectedCut hP hL a earlier hcard+s := by
  unfold selectedCut
  simp only [relativeCuts_translated]
  ring

end

end AbelianTargets
