import AbelianTargets.FiniteAtlasDependencyPatterns

/-! A function determined by a locally constant finite pattern is itself
locally constant and has finite range. This is the action-parameter step
used after proving literal recursive dependence on the atlas pattern. -/

namespace AbelianTargets
noncomputable section
open Filter Topology

theorem locallyConstant_of_pattern {X P Y : Type*} [TopologicalSpace X]
    (p : X→P) (hp : IsLocallyConstant p) (f : X→Y)
    (hdepends : ∀x y,p x=p y → f x=f y) : IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [hp.eventually_eq x] with y hy
  exact hdepends y x hy

theorem finite_range_of_constant_pattern {X P Y : Type*}
    (p : X→P) (hp : (Set.range p).Finite) (f : X→Y)
    (hdepends : ∀x y,p x=p y → f x=f y) : (Set.range f).Finite := by
  classical
  let g : Set.range p→Y := fun a=>f a.property.choose
  letI : Finite (Set.range p) := hp.to_subtype
  apply (Set.finite_range g).subset
  rintro _ ⟨x,rfl⟩
  let a : Set.range p := ⟨p x,⟨x,rfl⟩⟩
  exact ⟨a,hdepends a.property.choose x a.property.choose_spec⟩

end
end AbelianTargets
