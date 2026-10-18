import AbelianTargets.IntegerRectangleProbes
import AbelianTargets.RectangularLocalFiniteness
import Mathlib.Data.Finset.Max

namespace AbelianTargets
noncomputable section
namespace RectangularCell
variable {d : ℕ}

theorem closedBox_injective : Function.Injective (fun R : RectangularCell d => R.closedBox) := by
  intro R Q he
  change R.closedBox = Q.closedBox at he
  have hRlo : (fun i => (R.lower i : ℝ)) ∈ R.closedBox := fun i =>
    ⟨le_rfl,by dsimp only; exact_mod_cast R.ordered i⟩
  have hQlo : (fun i => (Q.lower i : ℝ)) ∈ Q.closedBox := fun i =>
    ⟨le_rfl,by dsimp only; exact_mod_cast Q.ordered i⟩
  have hRhi : (fun i => (R.upper i : ℝ)) ∈ R.closedBox := fun i =>
    ⟨by dsimp only; exact_mod_cast R.ordered i,le_rfl⟩
  have hQhi : (fun i => (Q.upper i : ℝ)) ∈ Q.closedBox := fun i =>
    ⟨by dsimp only; exact_mod_cast Q.ordered i,le_rfl⟩
  have hlo : R.lower = Q.lower := by
    funext i
    apply le_antisymm
    · have h := ((he.symm ▸ hQlo) i).1
      dsimp only at h
      exact_mod_cast h
    · have h := ((he ▸ hRlo) i).1
      dsimp only at h
      exact_mod_cast h
  have hhi : R.upper = Q.upper := by
    funext i
    apply le_antisymm
    · have h := ((he ▸ hRhi) i).2
      dsimp only at h
      exact_mod_cast h
    · have h := ((he.symm ▸ hQhi) i).2
      dsimp only at h
      exact_mod_cast h
  exact endpoint_pair_injective (Prod.ext hlo hhi)

theorem closedBox_subset_iff (R Q : RectangularCell d) :
    R.closedBox ⊆ Q.closedBox ↔ ∀ i,Q.lower i ≤ R.lower i ∧ R.upper i ≤ Q.upper i := by
  constructor
  · intro hs i
    have hlo := hs (show (fun j => (R.lower j : ℝ)) ∈ R.closedBox from
      fun j => ⟨le_rfl,by dsimp only; exact_mod_cast R.ordered j⟩)
    have hhi := hs (show (fun j => (R.upper j : ℝ)) ∈ R.closedBox from
      fun j => ⟨by dsimp only; exact_mod_cast R.ordered j,le_rfl⟩)
    exact ⟨by have h := (hlo i).1; dsimp only at h; exact_mod_cast h,
      by have h := (hhi i).2; dsimp only at h; exact_mod_cast h⟩
  · intro hs z hz i
    have h₁ : (Q.lower i : ℝ) ≤ (R.lower i : ℝ) := by exact_mod_cast (hs i).1
    have h₂ : (R.upper i : ℝ) ≤ (Q.upper i : ℝ) := by exact_mod_cast (hs i).2
    exact ⟨h₁.trans (hz i).1,(hz i).2.trans h₂⟩

theorem relativeInterior_subset_of_shared_base (R Q : RectangularCell d)
    (hs : R.closedBox ⊆ Q.closedBox) {x : RealCoordinates d}
    (hxR : x ∈ R.relativeInterior) (hxQ : x ∈ Q.relativeInterior) :
    R.relativeInterior ⊆ Q.relativeInterior := by
  intro y hy i
  have hyQ := hs (R.relativeInterior_subset hy)
  by_cases hQ : Q.lower i = Q.upper i
  · simp only [if_pos hQ]
    exact le_antisymm (by simpa only [hQ] using (hyQ i).2) (hyQ i).1
  · simp only [if_neg hQ]
    by_cases hR : R.lower i = R.upper i
    · have hxRi := hxR i
      have hyRi := hy i
      simp only [hR,if_true] at hxRi hyRi
      have he : y i = x i := hyRi.trans hxRi.symm
      simpa only [he,hQ,if_false] using hxQ i
    · have hsub := (closedBox_subset_iff R Q).mp hs i
      have hlo : (Q.lower i : ℝ) ≤ (R.lower i : ℝ) := by exact_mod_cast hsub.1
      have hhi : (R.upper i : ℝ) ≤ (Q.upper i : ℝ) := by exact_mod_cast hsub.2
      have hyi := hy i
      simp only [hR,if_false] at hyi
      exact ⟨hlo.trans_lt hyi.1,hyi.2.trans_le hhi⟩

def faceIntersection (F : Finset (RectangularCell d)) (hF : F.Nonempty)
    (x : RealCoordinates d) (hx : ∀ R ∈ F,x ∈ R.closedBox) : RectangularCell d where
  lower i := F.sup' hF (fun R => (R.faceAt x).lower i)
  upper i := F.inf' hF (fun R => (R.faceAt x).upper i)
  ordered i := by
    apply Finset.sup'_le hF (fun R => (R.faceAt x).lower i)
    intro R hR
    apply Finset.le_inf' hF (fun Q => (Q.faceAt x).upper i)
    intro Q hQ
    have hr := (R.faceAt x).relativeInterior_subset (R.mem_relativeInterior_faceAt (hx R hR))
    have hq := (Q.faceAt x).relativeInterior_subset (Q.mem_relativeInterior_faceAt (hx Q hQ))
    exact_mod_cast (hr i).1.trans (hq i).2

theorem mem_faceIntersection (F : Finset (RectangularCell d)) (hF : F.Nonempty)
    (x : RealCoordinates d) (hx : ∀ R ∈ F,x ∈ R.closedBox) (y : RealCoordinates d) :
    y ∈ (faceIntersection F hF x hx).closedBox ↔ ∀ R ∈ F,y ∈ (R.faceAt x).closedBox := by
  constructor
  · intro hy R hR i
    have hlo := Finset.le_sup' (fun T => (T.faceAt x).lower i) hR
    have hhi := Finset.inf'_le (fun T => (T.faceAt x).upper i) hR
    have hlo' : ((R.faceAt x).lower i : ℝ) ≤ ((faceIntersection F hF x hx).lower i : ℝ) := by
      exact_mod_cast hlo
    have hhi' : ((faceIntersection F hF x hx).upper i : ℝ) ≤ ((R.faceAt x).upper i : ℝ) := by
      exact_mod_cast hhi
    exact ⟨hlo'.trans (hy i).1,(hy i).2.trans hhi'⟩
  · intro hy i
    obtain ⟨R,hR,hlo⟩ := F.exists_mem_eq_sup' hF (fun T => (T.faceAt x).lower i)
    obtain ⟨Q,hQ,hhi⟩ := F.exists_mem_eq_inf' hF (fun T => (T.faceAt x).upper i)
    change ((F.sup' hF (fun T => (T.faceAt x).lower i) : ℤ) : ℝ) ≤ y i ∧
      y i ≤ ((F.inf' hF (fun T => (T.faceAt x).upper i) : ℤ) : ℝ)
    rw [hlo,hhi]
    exact ⟨(hy R hR i).1,(hy Q hQ i).2⟩

theorem mem_relativeInterior_faceIntersection
    (F : Finset (RectangularCell d)) (hF : F.Nonempty)
    (x : RealCoordinates d) (hx : ∀ R ∈ F,x ∈ R.closedBox) :
    x ∈ (faceIntersection F hF x hx).relativeInterior := by
  let Q := faceIntersection F hF x hx
  have hxQ : x ∈ Q.closedBox := (mem_faceIntersection F hF x hx x).mpr
    (fun R hR => (R.faceAt x).relativeInterior_subset (R.mem_relativeInterior_faceAt (hx R hR)))
  intro i
  change if Q.lower i = Q.upper i then x i = (Q.lower i : ℝ)
    else (Q.lower i : ℝ) < x i ∧ x i < (Q.upper i : ℝ)
  by_cases he : Q.lower i = Q.upper i
  · simp only [if_pos he]
    exact le_antisymm (by simpa only [he] using (hxQ i).2) (hxQ i).1
  · simp only [if_neg he]
    obtain ⟨R,hR,hlo⟩ := F.exists_mem_eq_sup' hF (fun T => (T.faceAt x).lower i)
    obtain ⟨T,hT,hhi⟩ := F.exists_mem_eq_inf' hF (fun T => (T.faceAt x).upper i)
    have hr := R.mem_relativeInterior_faceAt (hx R hR)
    have ht := T.mem_relativeInterior_faceAt (hx T hT)
    have hQlo : Q.lower i = (R.faceAt x).lower i := hlo
    have hQhi : Q.upper i = (T.faceAt x).upper i := hhi
    constructor
    · by_cases hRface : (R.faceAt x).lower i = (R.faceAt x).upper i
      · have hle := Finset.inf'_le (fun U => (U.faceAt x).upper i) hR
        have hQle : Q.upper i ≤ Q.lower i := by simpa only [hQlo,hRface] using hle
        exact (he (le_antisymm (Q.ordered i) hQle)).elim
      · have hri := hr i
        simp only [hRface,if_false] at hri
        simpa only [hQlo] using hri.1
    · by_cases hTface : (T.faceAt x).lower i = (T.faceAt x).upper i
      · have hle := Finset.le_sup' (fun U => (U.faceAt x).lower i) hT
        have hQle : Q.upper i ≤ Q.lower i := by simpa only [hQhi,hTface] using hle
        exact (he (le_antisymm (Q.ordered i) hQle)).elim
      · have hti := ht i
        simp only [hTface,if_false] at hti
        simpa only [hQhi] using hti.2

theorem faceIntersection_relativeInterior_subset
    (F : Finset (RectangularCell d)) (hF : F.Nonempty)
    (x : RealCoordinates d) (hx : ∀ R ∈ F,x ∈ R.closedBox) {R : RectangularCell d} (hR : R ∈ F) :
    (faceIntersection F hF x hx).relativeInterior ⊆ (R.faceAt x).relativeInterior := by
  apply relativeInterior_subset_of_shared_base _ _ _
    (mem_relativeInterior_faceIntersection F hF x hx) (R.mem_relativeInterior_faceAt (hx R hR))
  intro y hy
  exact (mem_faceIntersection F hF x hx y).mp hy R hR

end RectangularCell
end
end AbelianTargets
