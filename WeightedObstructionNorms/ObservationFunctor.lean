import WeightedObstructionNorms.ObservationListInvariance
import Mathlib.CategoryTheory.Functor.Basic
import WeightedObstructionNorms.FiniteNormedCategory

noncomputable section
set_option maxHeartbeats 1000000
namespace WeightedObstructionNorms
namespace ObservationFunctor
open CategoryTheory
open FiniteObservations CechAllDegrees ObservationRestriction ObservationHomotopy
variable {I : Type*} [Fintype I] [DecidableEq I]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

/-- Finite observation families, with their downward closure explicitly required. -/
structure Object where
  support : Finset (State E)
  observations : Finset (Finset I)
  downward : ∀ A ∈ observations, ∀ B, B ⊆ A → B ∈ observations

instance : CategoryTheory.Category (Object E) where
  Hom X Y := PLift (X.support ⊆ Y.support ∧ Y.observations ⊆ X.observations)
  id _ := ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  comp f g := ⟨f.down.1.trans g.down.1, g.down.2.trans f.down.2⟩

/-- The maximal observations used to select a fixed representative. -/
def maximal (X : Object E) : Finset (Finset I) :=
  X.observations.filter (fun A => ∀ B ∈ X.observations, A ⊆ B → B ⊆ A)

lemma maximal_cover (X : Object E) {A : Finset I} (hA : A ∈ X.observations) :
    ∃ B ∈ maximal E X, A ⊆ B := by
  obtain ⟨B, hB, hmax⟩ := (X.observations.filter (fun B => A ⊆ B)).exists_max_image Finset.card
    ⟨A, Finset.mem_filter.mpr ⟨hA, Finset.Subset.refl _⟩⟩
  obtain ⟨hBO, hAB⟩ := Finset.mem_filter.mp hB
  refine ⟨B, Finset.mem_filter.mpr ⟨hBO, ?_⟩, hAB⟩
  intro C hC hBC
  have hc := hmax C (Finset.mem_filter.mpr ⟨hC, hAB.trans hBC⟩)
  rw [Finset.eq_of_subset_of_card_le hBC hc]

abbrev Index (X : Object E) := {A // A ∈ maximal E X}
instance indexFintype (X : Object E) : Fintype (Index E X) := Fintype.ofFinite _

/-- A fixed total order on the finite collection of all observations. -/
local instance observationOrder : LinearOrder (Finset I) := LinearOrder.lift' (Fintype.equivFin (Finset I)) (Fintype.equivFin (Finset I)).injective
local instance indexOrder (X : Object E) : LinearOrder (Index E X) := inferInstance
local instance indexPartialOrder (X : Object E) : PartialOrder (Index E X) := (indexOrder E X).toPartialOrder

def list (X : Object E) : Index E X → Finset I := Subtype.val

lemma generated_list (X : Object E) : CechLowDegrees.generated (list E X) = ↑X.observations := by
  ext A
  constructor
  · rintro ⟨B, hAB⟩
    exact X.downward B.val (Finset.mem_filter.mp B.property).1 A hAB
  · intro hA
    obtain ⟨B, hB, hAB⟩ := maximal_cover E X hA
    exact ⟨⟨B, hB⟩, hAB⟩

lemma exists_selection {X Y : Object E} (h : X ⟶ Y) :
    ∃ f : Index E Y → Index E X, ∀ a, list E Y a ⊆ list E X (f a) := by
  have hh : ∀ a : Index E Y, ∃ b : Index E X, a.val ⊆ b.val := by
    intro a
    obtain ⟨B, hB, hAB⟩ := maximal_cover E X (h.down.2 (Finset.mem_filter.mp a.property).1)
    exact ⟨⟨B, hB⟩, hAB⟩
  exact ⟨fun a => Classical.choose (hh a), fun a => Classical.choose_spec (hh a)⟩

def selection {X Y : Object E} (h : X ⟶ Y) : Index E Y → Index E X := Classical.choose (exists_selection E h)
lemma selection_valid {X Y : Object E} (h : X ⟶ Y) :
    ∀ a, list E Y a ⊆ list E X (selection E h a) := Classical.choose_spec (exists_selection E h)

def map {X Y : Object E} (h : X ⟶ Y) (p : ℕ) :
    Cohomology E X.support (list E X) p →ₗ[ℝ] Cohomology E Y.support (list E Y) p :=
  (cohomologyMap E Y.support (list E X) (list E Y) (selection E h) (selection_valid E h) p).comp
    (cohomologyExtension E X.support (list E X) h.down.1 p)

lemma map_id (X : Object E) (p : ℕ) (α : Cohomology E X.support (list E X) p) :
    map E (𝟙 X) p α = α := by
  simp only [map, LinearMap.comp_apply]
  rw [cohomologyExtension_identity]
  rw [cohomologyMap_choice_independent E X.support (list E X) (list E X) _ id _
    (fun _ => Finset.Subset.refl _)]
  exact cohomologyMap_identity E X.support (list E X) p α

lemma map_comp {X Y Z : Object E} (h : X ⟶ Y) (k : Y ⟶ Z) (p : ℕ)
    (α : Cohomology E X.support (list E X) p) :
    map E k p (map E h p α) = map E (h ≫ k) p α := by
  simp only [map, LinearMap.comp_apply]
  rw [← cohomologyMap_extension E Y.support (list E X) (list E Y)
    (selection E h) (selection_valid E h) k.down.1 p]
  rw [cohomologyMap_comp E Z.support (list E X) (list E Y)
    (selection E h) (selection_valid E h) (list E Z) (selection E k) (selection_valid E k) p]
  rw [cohomologyExtension_comp E X.support (list E X) h.down.1 k.down.1 p]
  exact cohomologyMap_choice_independent E Z.support _ _ _ _ _ _ p _

variable (o : State E) {q : State E → ℝ} (hq : ∀ z, 0 < q z)

include hq in
lemma map_nonexpansive {X Y : Object E} (h : X ⟶ Y) (p : ℕ)
    (α : Cohomology E X.support (list E X) p) :
    CechObstruction.norm E Y.support (list E Y) o q p (map E h p α) ≤
      CechObstruction.norm E X.support (list E X) o q p α :=
  (ObservationRestrictionNorm.norm_nonexpansive E Y.support (list E X) o (list E Y)
    (selection E h) (selection_valid E h) hq p _).trans
      (CechSupportNorm.norm_nonexpansive E X.support Y.support (list E X) o h.down.1 hq p α)

/-- Theorem 5.3: the functor on support/family pairs, using ordered maximal lists. -/
def functor (p : ℕ) : Object E ⥤ FiniteNormed where
  obj X := ⟨CechObstruction.Normed E X.support (list E X) o q hq p⟩
  map h := ⟨map E h p, map_nonexpansive E o hq h p⟩
  map_id X := by
    apply FiniteNormed.Hom.ext
    intro x
    exact map_id E X p x
  map_comp h k := by
    apply FiniteNormed.Hom.ext
    intro x
    exact (map_comp E h k p x).symm

end ObservationFunctor
end WeightedObstructionNorms
