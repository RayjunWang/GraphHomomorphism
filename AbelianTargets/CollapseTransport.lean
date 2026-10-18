import AbelianTargets.ParallelCollapse
import AbelianTargets.ProbabilityPushGeometry

set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Probability
variable {V W : Type*} [Fintype V] [Fintype W]
theorem push_mass_zero_of_not_range (f : V → W) (p : Probability V) (w : W)
    (hw : w ∉ Set.range f) : (push f p).mass w = 0 := by
  rw [push_mass]
  apply Finset.sum_eq_zero
  intro v hv
  simp [show f v ≠ w from fun h => hw ⟨v,h⟩]

theorem push_mix (f : V → W) (p q : Probability V) (t : unitInterval) :
    push f (mix p q t) = mix (push f p) (push f q) t := by
  ext w
  rw [push_mass,mix_mass,push_mass,push_mass]
  have he : (∑ v, if f v = w then (mix p q t).mass v else 0) =
      ∑ v, ((1-(t:ℝ))*(if f v = w then p.mass v else 0) +
        (t:ℝ)*(if f v = w then q.mass v else 0)) := by
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : f v = w <;> simp only [h,if_true,if_false,mix_mass,mul_zero,add_zero]
  rw [he,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
end Probability

namespace CollapseTriangle
variable {V W : Type*}
def map (f : V → W) (hf : Function.Injective f) (D : CollapseTriangle V) : CollapseTriangle W where
  a := f D.a
  b := f D.b
  c := f D.c
  ab := fun h => D.ab (hf h)
  ac := fun h => D.ac (hf h)
  bc := fun h => D.bc (hf h)
variable [Fintype V] [Fintype W]
theorem vertices_map (f : V → W) (hf : Function.Injective f) (D : CollapseTriangle V) :
    (D.map f hf).vertices = D.vertices.image f := by simp [vertices,map]

theorem push_collapse (f : V → W) (hf : Function.Injective f) (D : CollapseTriangle V) (p : Probability V) :
    Probability.push f (Probability.triangleCollapse D.a D.b D.c D.ab D.ac D.bc p) =
      Probability.triangleCollapse (f D.a) (f D.b) (f D.c)
        (D.map f hf).ab (D.map f hf).ac (D.map f hf).bc (Probability.push f p) := by
  ext w
  by_cases hw : w ∈ Set.range f
  · obtain ⟨v,rfl⟩ := hw
    rw [Probability.push_mass_of_injective f hf]
    simp only [Probability.triangleCollapse_mass,Probability.push_mass_of_injective f hf,hf.eq_iff]
  · rw [Probability.push_mass_zero_of_not_range f _ w hw,Probability.triangleCollapse_mass]
    rw [Probability.push_mass_zero_of_not_range f p w hw]
    simp only [show w ≠ f D.a from fun h => hw ⟨D.a,h.symm⟩,
      show w ≠ f D.b from fun h => hw ⟨D.b,h.symm⟩,
      show w ≠ f D.c from fun h => hw ⟨D.c,h.symm⟩,if_false,add_zero,sub_zero]

theorem push_homotopy (f : V → W) (hf : Function.Injective f) (D : CollapseTriangle V)
    (p : Probability V) (t : unitInterval) :
    Probability.push f (D.homotopy p t) = (D.map f hf).homotopy (Probability.push f p) t := by
  unfold homotopy Probability.triangleHomotopy
  rw [Probability.push_mix,D.push_collapse f hf]
  rfl
end CollapseTriangle

theorem mem_image_injective_iff {V W : Type*} [DecidableEq W] (f : V → W)
    (hf : Function.Injective f) (s : Finset V) (v : V) : f v ∈ s.image f ↔ v ∈ s := by
  constructor
  · intro h
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
    simpa only [hf he] using hw
  · intro h; exact Finset.mem_image.mpr ⟨v,h,rfl⟩

namespace FreeCollapseFamily
variable {V W I : Type*} [Fintype V] [Fintype W] {F : Finset (Finset V)}
def pushFamily (D : FreeCollapseFamily F I) (f : V → W) (hf : Function.Injective f) :
    FreeCollapseFamily (F.image (fun s => s.image f)) I where
  triangle i := (D.triangle i).map f hf
  mem_face i := by
    rw [CollapseTriangle.vertices_map]
    exact Finset.mem_image.mpr ⟨_,D.mem_face i,rfl⟩
  free_edge i s hs ha hb := by
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hs
    have ha' := (mem_image_injective_iff f hf u (D.triangle i).a).mp ha
    have hb' := (mem_image_injective_iff f hf u (D.triangle i).b).mp hb
    rw [CollapseTriangle.vertices_map]
    exact Finset.image_subset_image (D.free_edge i u hu ha' hb')
  no_other_edge i j hij := by
    rw [CollapseTriangle.vertices_map]
    rcases D.no_other_edge i j hij with h | h
    · exact Or.inl (fun hn => h ((mem_image_injective_iff f hf _ _).mp hn))
    · exact Or.inr (fun hn => h ((mem_image_injective_iff f hf _ _).mp hn))

theorem mapList_transport (D : FreeCollapseFamily F I) (f : V → W) (hf : Function.Injective f)
    (l : List I) (p : Probability V) (t : unitInterval) :
    Probability.push f (D.mapList l p t) = (D.pushFamily f hf).mapList l (Probability.push f p) t := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [mapList]
    rw [(D.triangle i).push_homotopy f hf,ih]
    rfl
end FreeCollapseFamily
end
end AbelianTargets
