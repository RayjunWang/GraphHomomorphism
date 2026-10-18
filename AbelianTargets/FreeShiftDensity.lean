import AbelianTargets.FreeShiftTopology
import Mathlib.Data.Finset.Max

/-!
# Finite patterns extend to free binary configurations

A nonempty finitely supported binary configuration has no nonzero lattice
period: a maximum in each support coordinate bounds both signs of a period.
This gives explicit free extensions of all finite binary patterns.
-/

namespace AbelianTargets

noncomputable section

theorem finite_nonempty_support_isFree {d : ℕ} (x : ShiftSpace d)
    (hfinite : {u : Lattice d | x u = true}.Finite)
    (hne : ∃ u, x u = true) :
    ∀ g : Lattice d, shift g x = x → g = 0 := by
  classical
  let S := hfinite.toFinset
  have hS : S.Nonempty := by
    obtain ⟨u, hu⟩ := hne
    exact ⟨u, by simpa [S] using hu⟩
  intro g hg
  funext i
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image S (fun z => z i) hS
  have hxu : x u = true := by simpa [S] using hu
  have hplus : u + g ∈ S := by
    have hh := congrFun hg u
    change x (u + g) = x u at hh
    simpa [S, hh] using hxu
  have hminus : u - g ∈ S := by
    have hh := congrFun hg (u - g)
    change x (u - g + g) = x (u - g) at hh
    rw [sub_add_cancel] at hh
    simpa [S, hh] using hxu
  have h₁ := hmax (u + g) hplus
  have h₂ := hmax (u - g) hminus
  simp only [Pi.add_apply, Pi.sub_apply] at h₁ h₂
  change g i = 0
  omega

theorem lattice_infinite {d : ℕ} (hd : 1 ≤ d) : Infinite (Lattice d) := by
  let i : Fin d := ⟨0, by omega⟩
  let f : ℤ → Lattice d := fun z j => if j = i then z else 0
  apply Infinite.of_injective f
  intro a b h
  have hi := congrFun h i
  simpa [f] using hi

/-- Every finite binary pattern extends to an actual free configuration. -/
theorem exists_freeShift_extension {d : ℕ} (hd : 1 ≤ d)
    (F : Finset (Lattice d)) (p : Lattice d → Bool) :
    ∃ x : FreeShift d, ∀ u ∈ F, x.val u = p u := by
  classical
  letI : Infinite (Lattice d) := lattice_infinite hd
  obtain ⟨a, ha⟩ := F.exists_notMem
  let S := insert a (F.filter (fun u => p u = true))
  let x : ShiftSpace d := fun u => decide (u ∈ S)
  have hfinite : {u : Lattice d | x u = true}.Finite := by
    have hs : {u : Lattice d | x u = true} = (S : Set (Lattice d)) := by
      ext u
      simp [x]
    rw [hs]
    exact S.finite_toSet
  have hpos : ∃ u, x u = true := ⟨a, by simp [x, S]⟩
  refine ⟨⟨x, finite_nonempty_support_isFree x hfinite hpos⟩, ?_⟩
  intro u hu
  have hua : u ≠ a := fun h => ha (h ▸ hu)
  change x u = p u
  cases hp : p u <;> simp [x, S, hua, hu, hp]

/-- In particular, the positive-dimensional free binary shift is nonempty. -/
theorem freeShift_nonempty {d : ℕ} (hd : 1 ≤ d) : Nonempty (FreeShift d) := by
  obtain ⟨x, _⟩ := exists_freeShift_extension hd ∅ (fun _ => false)
  exact ⟨x⟩

end

end AbelianTargets
