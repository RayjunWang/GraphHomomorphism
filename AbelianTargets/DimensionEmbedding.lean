import AbelianTargets.Actions
import Mathlib.Data.Fin.Tuple.Basic
import Lean.Elab.Tactic.Omega

/-!
# Actual inclusion of successive target classes

For `d ≥ 1`, a free binary configuration on `ℤ^d` embeds continuously
and equivariantly into the free binary configurations on `ℤ^(d+1)`.
The construction puts the original configuration on the last-coordinate
zero plane, and puts `false` elsewhere. This proves
`InClass (d + 1) H → InClass d H` without external universality inputs.
-/

namespace AbelianTargets

@[simp] theorem latticeInit_add {d : ℕ} (u v : Lattice (d + 1)) :
    Fin.init (u + v) = Fin.init u + Fin.init v := rfl

/-- Pad a binary configuration by zero outside the horizontal plane. -/
def padShift {d : ℕ} (x : ShiftSpace d) : ShiftSpace (d + 1) :=
  fun z => if z (Fin.last d) = 0 then x (Fin.init z) else false

/-- A free binary configuration in positive dimension has a nonzero symbol. -/
theorem freeShift_exists_true {d : ℕ} (hd : 1 ≤ d) (x : FreeShift d) :
    ∃ u : Lattice d, x.val u = true := by
  by_contra h
  have hfalse : ∀ u : Lattice d, x.val u = false := by
    intro u
    cases hx : x.val u with
    | false => rfl
    | true => exact (h ⟨u, hx⟩).elim
  let i : Fin d := ⟨0, by omega⟩
  have hperiod : shift (unitVector i) x.val = x.val := by
    funext u
    simp only [shift, hfalse]
  have hzero := x.property (unitVector i) hperiod
  have hi := congrFun hzero i
  simp [unitVector] at hi

/-- The padded configuration is still free: a transverse period moves
the only possible nonzero symbols off their plane; a horizontal period
would be a period of the original free configuration. -/
theorem padShift_isFree {d : ℕ} (hd : 1 ≤ d) (x : FreeShift d)
    (g : Lattice (d + 1))
    (hg : shift g (padShift x.val) = padShift x.val) : g = 0 := by
  obtain ⟨u, hu⟩ := freeShift_exists_true hd x
  have hlast : g (Fin.last d) = 0 := by
    by_contra hne
    have h := congrFun hg (Fin.snoc u 0)
    simp [shift, padShift, Pi.add_apply, hne, hu] at h
  have hperiod : shift (Fin.init g) x.val = x.val := by
    funext z
    have h := congrFun hg (Fin.snoc z 0)
    simpa [shift, padShift, Pi.add_apply, hlast] using h
  have hinit := x.property (Fin.init g) hperiod
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact hlast
  · exact congrFun hinit j

/-- The genuine map between free parts. -/
def padFreeShift {d : ℕ} (hd : 1 ≤ d) (x : FreeShift d) : FreeShift (d + 1) :=
  ⟨padShift x.val, padShift_isFree hd x⟩

theorem continuous_padShift {d : ℕ} :
    Continuous (padShift : ShiftSpace d → ShiftSpace (d + 1)) := by
  apply continuous_pi
  intro z
  by_cases hz : z (Fin.last d) = 0
  · simpa only [padShift, hz, if_true] using continuous_apply (Fin.init z)
  · simpa only [padShift, hz, if_false] using
      (continuous_const : Continuous (fun _ : ShiftSpace d => false))

theorem continuous_padFreeShift {d : ℕ} (hd : 1 ≤ d) :
    Continuous (padFreeShift hd : FreeShift d → FreeShift (d + 1)) := by
  apply continuous_induced_rng.mpr
  exact continuous_padShift.comp continuous_induced_dom

/-- Equivariance for every horizontal displacement. -/
theorem padShift_equivariant {d : ℕ} (g : Lattice d) (x : ShiftSpace d) :
    padShift (shift g x) = shift (Fin.snoc g 0) (padShift x) := by
  funext z
  simp [padShift, shift, Pi.add_apply]

theorem snoc_unitVector {d : ℕ} (i : Fin d) :
    Fin.snoc (unitVector i) 0 = unitVector i.castSucc := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [unitVector, Ne.symm (Fin.castSucc_ne_last i)]
  · simp [unitVector]

/-- Equivariance for the standard generators used by the Schreier graphs. -/
theorem padFreeShift_unitVector {d : ℕ} (hd : 1 ≤ d) (i : Fin d)
    (x : FreeShift d) :
    padFreeShift hd (unitVector i +ᵥ x) =
      unitVector i.castSucc +ᵥ padFreeShift hd x := by
  apply Subtype.ext
  change padShift (shift (unitVector i) x.val) =
    shift (unitVector i.castSucc) (padShift x.val)
  rw [← snoc_unitVector]
  exact padShift_equivariant (unitVector i) x.val

/-- Successive target classes are actually nested, without any assumption
about the finite marker graphs or the twelve-tile theorem. -/
theorem inClass_succ_subset {d : ℕ} (hd : 1 ≤ d)
    {V : Type*} [TopologicalSpace V] {H : SimpleGraph V}
    (h : InClass (d + 1) H) : InClass d H := by
  obtain ⟨c, hc, he⟩ := h
  let f : FreeShift d → V := fun x => c (padFreeShift hd x)
  apply hasContinuousHom_of_positive f (hc.comp (continuous_padFreeShift hd))
  intro x i
  have hxy : StandardEdge (d := d + 1)
      (padFreeShift hd x) (unitVector i.castSucc +ᵥ padFreeShift hd x) :=
    ⟨i.castSucc, Or.inl rfl⟩
  simpa only [f, ← padFreeShift_unitVector hd i x] using he _ _ hxy

/-- One standard carrier for finite simple graph codes. -/
abbrev FiniteGraphCode := Σ n : ℕ, SimpleGraph (Fin n)

/-- The paper's target class expressed on the finite graph codes. -/
def finiteGraphClass (d : ℕ) : Set FiniteGraphCode :=
  {C | InClass d C.2}

/-- Actual monotonic inclusion, on finite graph codes. -/
theorem finiteGraphClass_succ_subset {d : ℕ} (hd : 1 ≤ d) :
    finiteGraphClass (d + 1) ⊆ finiteGraphClass d := by
  intro C hC
  exact inClass_succ_subset hd hC

/-- Once successive separating witnesses are supplied, the actual nested
classes are strictly decreasing. The witnesses remain an explicit input,
so this does not claim an unconditional proof of Proposition 7.7. -/
theorem finiteGraphClasses_strictDecrease_of_witnesses
    (witnesses : ∀ d : ℕ, 1 ≤ d →
      ∃ C : FiniteGraphCode, C ∈ finiteGraphClass d ∧
        C ∉ finiteGraphClass (d + 1)) :
    ∀ d : ℕ, 1 ≤ d → finiteGraphClass (d + 1) ⊂ finiteGraphClass d := by
  intro d hd
  refine Set.ssubset_iff_subset_ne.mpr ⟨finiteGraphClass_succ_subset hd, ?_⟩
  intro heq
  obtain ⟨C, hC, hnot⟩ := witnesses d hd
  apply hnot
  rw [heq]
  exact hC

end AbelianTargets
