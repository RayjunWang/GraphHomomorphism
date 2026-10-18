import AbelianTargets.UniformCarrierContraction

/-! Contractions are selected once at zero-based interval widths and then
transported by an explicit isometry. The normalized data are retained as
data rather than being reselected from an existential proof at every cell. -/

namespace AbelianTargets.IntervalCarriers
open scoped unitInterval NNReal
noncomputable section
variable {m K : ℕ} {A B C D E F : ℤ}

def intervalShiftEquiv (a : ℤ) (hA : A+a=C) (hB : B+a=D) :
    Realization m K A B ≃ᵢ Realization m K C D := by
  subst C
  subst D
  exact realizationTranslationEquiv a

def intervalVertexShift (a : ℤ) (hA : A+a=C) (hB : B+a=D)
    (v : CarrierVertex K A B) : CarrierVertex K C D :=
  ⟨translate a v.val,by
    have hh := (translate_mem_carrierVertices a v.val).mpr v.property
    simpa only [hA,hB] using hh⟩

@[simp] theorem intervalShiftEquiv_val (a : ℤ) (hA : A+a=C) (hB : B+a=D)
    (p : Realization m K A B) :
    (intervalShiftEquiv a hA hB p).val=Probability.push (intervalVertexShift a hA hB) p.val := by
  subst C
  subst D
  rfl

theorem intervalShiftEquiv_comp (a b : ℤ) (hA : A+a=C) (hB : B+a=D)
    (hC : C+b=E) (hD : D+b=F) (p : Realization m K A B) :
    intervalShiftEquiv b hC hD (intervalShiftEquiv a hA hB p)=
      intervalShiftEquiv (a+b) (by omega) (by omega) p := by
  apply Subtype.ext
  simp only [intervalShiftEquiv_val,Probability.push_comp]
  congr 1
  funext v
  apply Subtype.ext
  simp [intervalVertexShift,translate,Function.comp_def,add_assoc]

def NormalizedContractionFamily (m K S : ℕ) (J : ℝ≥0) :=
  ∀ (R : ℕ) (hR : 0<R),R≤S →
    ControlledContraction (point (carrierBase K R) : Realization m K 0 R)
      (uniformCarrierSpeed m K) J

theorem exists_normalizedContractionFamily (m : ℕ) (hm : 2≤m) (K S : ℕ)
    (hSK : Nat.log m S≤K) : ∃ J : ℝ≥0,Nonempty (NormalizedContractionFamily m K S J) := by
  classical
  obtain ⟨J,hJ⟩ := exists_uniformCarrierContractions m hm K S hSK
  exact ⟨J,⟨fun R hR hRS=>Classical.choice (hJ R hR hRS)⟩⟩

def NormalizedContractionFamily.atInterval {S : ℕ} {J : ℝ≥0}
    (H : NormalizedContractionFamily m K S J) (A B : ℤ)
    (hAB : A<B) (hS : (B-A).toNat≤S) :
    ControlledContraction
      (intervalShiftEquiv A (by simp : (0:ℤ)+A=A)
        (by rw [Int.toNat_of_nonneg (by omega : 0≤B-A)])
        (point (carrierBase K (B-A).toNat) : Realization m K 0 (B-A).toNat))
      (uniformCarrierSpeed m K) J :=
  (H (B-A).toNat (by omega) hS).transport (intervalShiftEquiv A (by simp)
    (by rw [Int.toNat_of_nonneg (by omega : 0≤B-A)]))

def leftBase (K : ℕ) (A B : ℤ) (hAB : A≤B) : CarrierVertex K A B :=
  ⟨(A,0),mem_carrierVertices.mpr ⟨le_rfl,hAB,Nat.zero_le K⟩⟩

theorem intervalShiftEquiv_base (n : ℕ) (A B : ℤ) (hb : (n:ℤ)+A=B)
    (hAB : A≤B) :
    intervalShiftEquiv A (by simp : (0:ℤ)+A=A) hb
      (point (carrierBase K n) : Realization m K 0 n)=point (leftBase K A B hAB) := by
  apply Subtype.ext
  simp only [intervalShiftEquiv_val]
  change Probability.push _ (Probability.dirac _)=Probability.dirac _
  rw [Probability.push_dirac]
  congr 1
  apply Subtype.ext
  simp [intervalVertexShift,carrierBase,leftBase,translate]

end
end AbelianTargets.IntervalCarriers

namespace AbelianTargets.ControlledContraction
open scoped NNReal unitInterval
noncomputable section
variable {Z : Type*} [MetricSpace Z] {p q : Z} {D J : ℝ≥0}

def rebase (H : ControlledContraction p D J) (h : p=q) : ControlledContraction q D J := by
  subst q
  exact H

@[simp] theorem rebase_map (H : ControlledContraction p D J) (h : p=q) (z : Z×unitInterval) :
    (H.rebase h).map z=H.map z := by
  subst q
  rfl

end
end AbelianTargets.ControlledContraction

namespace AbelianTargets.IntervalCarriers
open scoped unitInterval NNReal
noncomputable section
variable {m K S : ℕ} {J : ℝ≥0}

def NormalizedContractionFamily.atWidthInterval (H : NormalizedContractionFamily m K S J)
    (n : ℕ) (hn : 0<n) (hS : n≤S) (A B : ℤ) (hb : (n:ℤ)+A=B) :
    ControlledContraction (point (leftBase K A B (by omega)) : Realization m K A B)
      (uniformCarrierSpeed m K) J :=
  ((H n hn hS).transport (intervalShiftEquiv (A := 0) (B := n) (C := A) (D := B)
    A (by simp) hb)).rebase
    (intervalShiftEquiv_base n A B hb (by omega))

theorem NormalizedContractionFamily.atWidthInterval_shift
    (H : NormalizedContractionFamily m K S J) (n : ℕ) (hn : 0<n) (hS : n≤S)
    (A B C D a : ℤ) (hb : (n:ℤ)+A=B) (hA : A+a=C) (hB : B+a=D)
    (p : Realization m K A B) (t : I) :
    (H.atWidthInterval n hn hS C D (by omega)).map (intervalShiftEquiv a hA hB p,t)=
      intervalShiftEquiv a hA hB ((H.atWidthInterval n hn hS A B hb).map (p,t)) := by
  let e₀ : Realization m K 0 n ≃ᵢ Realization m K A B := intervalShiftEquiv A (by simp) hb
  let e₁ : Realization m K A B ≃ᵢ Realization m K C D := intervalShiftEquiv a hA hB
  let e₂ : Realization m K 0 n ≃ᵢ Realization m K C D := intervalShiftEquiv C (by simp) (by omega)
  have hcomp : ∀q,e₁ (e₀ q)=e₂ q := by
    intro q
    dsimp [e₀,e₁,e₂]
    have hh := intervalShiftEquiv_comp A a (by simp : (0:ℤ)+A=A) hb hA hB q
    simpa only [hA] using hh
  have hinv : e₂.symm (e₁ p)=e₀.symm p := by
    apply e₂.injective
    rw [e₂.apply_symm_apply,←hcomp,e₀.apply_symm_apply]
  simp only [atWidthInterval,ControlledContraction.rebase_map,ControlledContraction.transport]
  change e₂ ((H n hn hS).map (e₂.symm (e₁ p),t))=e₁ (e₀ ((H n hn hS).map (e₀.symm p,t)))
  rw [hinv,hcomp]

end
end AbelianTargets.IntervalCarriers
