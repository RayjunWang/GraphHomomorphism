import AbelianTargets.OneHeightRetraction
import AbelianTargets.CurveFamilyStages

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Actual height-by-height deformation curves in one fixed carrier. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

structure HeightChain (m K : ℕ) (A B : ℤ) where
  curve : ℕ → Realization m K A B × unitInterval → Realization m K A B
  initial : ∀ p, curve 0 (p,0) = p
  seam : ∀ n p, curve n (p,1) = curve (n+1) (p,0)
  terminal : ∀ p v, 0 < (curve K (p,0)).1.mass v → v.1.2 = 0
  tail : ∀ n, K ≤ n → ∀ p t, curve n (p,t) = curve K (p,0)
  track : ∀ n p, LipschitzWith ((m+2 : ℕ) : ℝ≥0) (fun t => curve n (p,t))
  joint : ∀ n, ∃ J : ℝ≥0, LipschitzWith J (curve n)
  fixes_bottom : ∀ p, (∀ v, 0 < p.1.mass v → v.1.2 = 0) → ∀ n t, curve n (p,t) = p

theorem exists_heightChain {m : ℕ} (hm : 1 ≤ m) (K : ℕ) (A B : ℤ) : Nonempty (HeightChain m K A B) := by
  induction K with
  | zero =>
    refine ⟨{
      curve := fun _ z => z.1
      initial := fun _ => rfl
      seam := fun _ _ => rfl
      terminal := ?_
      tail := fun _ _ _ _ => rfl
      track := ?_
      joint := fun _ => ⟨1,LipschitzWith.prod_fst⟩
      fixes_bottom := fun _ _ _ _ => rfl }⟩
    · intro p v hv
      have hh := (mem_carrierVertices.mp v.2).2.2
      omega
    · intro n p
      exact (LipschitzWith.const p).weaken (by positivity)
  | succ K ih =>
    obtain ⟨G⟩ := ih
    let r : Realization m (K+1) A B → Realization m K A B := oneHeightRetraction hm
    let e : Realization m K A B → Realization m (K+1) A B := carrierInclude (by omega)
    let H : ℕ → Realization m (K+1) A B × unitInterval → Realization m (K+1) A B
      | 0 => fun z => oneHeightHomotopy hm z.1 z.2
      | n+1 => fun z => e (G.curve n (r z.1,z.2))
    refine ⟨{
      curve := H
      initial := ?_
      seam := ?_
      terminal := ?_
      tail := ?_
      track := ?_
      joint := ?_
      fixes_bottom := ?_ }⟩
    · intro p
      exact oneHeightHomotopy_zero hm p
    · intro n p
      cases n with
      | zero =>
        change oneHeightHomotopy hm p 1 = e (G.curve 0 (r p,0))
        rw [G.initial]
        exact (include_oneHeightRetraction hm p).symm
      | succ n =>
        change e (G.curve n (r p,1)) = e (G.curve (n+1) (r p,0))
        rw [G.seam]
    · intro p v hv
      change 0 < (Probability.push (vertexInclude (by omega)) (G.curve K (r p,0)).1).mass v at hv
      obtain ⟨u,hu,hup⟩ := (Probability.push_pos_iff (vertexInclude (by omega)) _ v).mp hv
      rw [←hu]
      exact G.terminal (r p) u hup
    · intro n hn p t
      cases n with
      | zero => omega
      | succ n =>
        change e (G.curve n (r p,t)) = e (G.curve K (r p,0))
        rw [G.tail n (by omega)]
    · intro n p
      cases n with
      | zero => exact oneHeightHomotopy_track hm p
      | succ n =>
        simpa only [H,Function.comp_def,one_mul] using
          (isometry_include (m := m) (A := A) (B := B) (by omega : K ≤ K+1)).lipschitz.comp (G.track n (r p))
    · intro n
      cases n with
      | zero => exact oneHeightHomotopy_joint hm
      | succ n =>
        obtain ⟨Jr,hJr⟩ := oneHeightRetraction_joint (K := K) (A := A) (B := B) hm
        obtain ⟨Jg,hJg⟩ := G.joint n
        have hp := (hJr.comp LipschitzWith.prod_fst).prodMk
          (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : Realization m (K+1) A B × unitInterval → unitInterval))
        refine ⟨Jg * max (Jr * 1) 1,?_⟩
        simpa only [H,r,e,Function.comp_def,one_mul] using
          (isometry_include (m := m) (A := A) (B := B) (by omega : K ≤ K+1)).lipschitz.comp (hJg.comp hp)
    · intro p hp n t
      have hpl : ∀ v, 0 < p.1.mass v → v.1.2 ≤ K := fun v hv => by rw [hp v hv]; exact Nat.zero_le _
      cases n with
      | zero => exact oneHeightHomotopy_fixes_lower hm p hpl t
      | succ n =>
        change e (G.curve n (r p,t)) = p
        rw [G.fixes_bottom (r p) (oneHeightRetraction_preserves_bottom hm p hp) n t]
        exact (include_oneHeightRetraction hm p).trans (oneHeightHomotopy_fixes_lower hm p hpl 1)

def heightChain {m : ℕ} (hm : 1 ≤ m) (K : ℕ) (A B : ℤ) : HeightChain m K A B :=
  Classical.choice (exists_heightChain hm K A B)

end
end AbelianTargets.IntervalCarriers
