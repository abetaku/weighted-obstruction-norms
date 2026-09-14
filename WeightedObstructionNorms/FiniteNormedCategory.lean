import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.CategoryTheory.Category.Basic

noncomputable section
namespace WeightedObstructionNorms
open CategoryTheory
universe u

/-- Finite-dimensional real normed spaces with linear nonexpansive maps. -/
structure FiniteNormed where
  carrier : Type u
  [group : NormedAddCommGroup carrier]
  [space : NormedSpace ℝ carrier]
  [finite : FiniteDimensional ℝ carrier]
attribute [instance] FiniteNormed.group FiniteNormed.space FiniteNormed.finite

namespace FiniteNormed
structure Hom (X Y : FiniteNormed.{u}) where
  linear : X.carrier →ₗ[ℝ] Y.carrier
  bound : ∀ x, ‖linear x‖ ≤ ‖x‖

@[ext] lemma Hom.ext {X Y : FiniteNormed.{u}} (f g : Hom X Y)
    (h : ∀ x, f.linear x = g.linear x) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have he : f = g := LinearMap.ext h
      subst g
      rfl

instance : Category FiniteNormed.{u} where
  Hom := Hom
  id X := ⟨LinearMap.id, fun _ => le_rfl⟩
  comp f g := ⟨g.linear.comp f.linear, fun x => (g.bound (f.linear x)).trans (f.bound x)⟩
  id_comp f := Hom.ext _ _ (fun _ => rfl)
  comp_id f := Hom.ext _ _ (fun _ => rfl)
  assoc f g h := Hom.ext _ _ (fun _ => rfl)

end FiniteNormed
end WeightedObstructionNorms
