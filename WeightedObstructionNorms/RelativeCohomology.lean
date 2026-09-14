import WeightedObstructionNorms.RelativeWindow
import Mathlib.LinearAlgebra.Isomorphisms

noncomputable section
open Set
namespace WeightedObstructionNorms

/-- One more differential before a split window. The two equations are the
old and new components of the full square-zero identity. The domain includes
all full cochains in the preceding degree. -/
structure RelativePredecessor {U X V Y Z : Type*} [Fintype U] [Fintype X]
    [Fintype V] [Fintype Y] [Fintype Z] (W : RelativeWindow U X V Y Z)
    (T : Type*) [Fintype T] where
  oldPrevious : (T → ℝ) →ₗ[ℝ] (U → ℝ)
  newPrevious : (T → ℝ) →ₗ[ℝ] (X → ℝ)
  old_square : ∀ z, W.oldD (oldPrevious z) + W.liftD (newPrevious z) = 0
  new_square : ∀ z, W.relativeD (newPrevious z) = 0

namespace RelativePredecessor
variable {U X V Y Z T : Type*} [Fintype U] [Fintype X]
    [Fintype V] [Fintype Y] [Fintype Z] [Fintype T]
    {W : RelativeWindow U X V Y Z} (P : RelativePredecessor W T)

def boundaryToCycles : (T → ℝ) →ₗ[ℝ] LinearMap.ker W.relativeD :=
  P.newPrevious.codRestrict _ P.new_square

abbrev Cohomology := (LinearMap.ker W.relativeD) ⧸ LinearMap.range P.boundaryToCycles

def classOf : LinearMap.ker W.relativeD →ₗ[ℝ] P.Cohomology :=
  (LinearMap.range P.boundaryToCycles).mkQ

lemma boundaries_connecting_zero : LinearMap.range P.boundaryToCycles ≤ LinearMap.ker W.connecting := by
  rintro v ⟨z, rfl⟩
  exact (W.connecting_kernel _).2 ⟨P.oldPrevious z, P.old_square z⟩

/-- Connecting homomorphism on relative cohomology, obtained by descent. -/
def connecting : P.Cohomology →ₗ[ℝ] W.Cohomology :=
  (LinearMap.range P.boundaryToCycles).liftQ W.connecting P.boundaries_connecting_zero

lemma connecting_class (v : LinearMap.ker W.relativeD) :
    P.connecting (P.classOf v) = W.connecting v := rfl

lemma class_surjective : Function.Surjective P.classOf := Submodule.mkQ_surjective _

lemma connecting_surjective : Function.Surjective P.connecting := by
  intro α
  obtain ⟨v, hv⟩ := W.connecting_surjective α
  exact ⟨P.classOf v, hv⟩

/-- The full differential on the old/new split of the preceding degree. -/
def fullDifferential (_P : RelativePredecessor W T) : ((U → ℝ) × (X → ℝ)) →ₗ[ℝ] ((V → ℝ) × (Y → ℝ)) :=
  (W.oldD.coprod W.liftD).prod (W.relativeD.comp (LinearMap.snd ℝ _ _))

abbrev FullCycles := LinearMap.ker P.fullDifferential

def previousToFullCycles : (T → ℝ) →ₗ[ℝ] P.FullCycles :=
  (P.oldPrevious.prod P.newPrevious).codRestrict _ (fun z => Prod.ext (P.old_square z) (P.new_square z))

abbrev FullCohomology := P.FullCycles ⧸ LinearMap.range P.previousToFullCycles

def fullProjection : P.FullCycles →ₗ[ℝ] LinearMap.ker W.relativeD where
  toFun x := ⟨x.val.2, congrArg Prod.snd x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma full_boundaries_map_zero : LinearMap.range P.previousToFullCycles ≤
    LinearMap.ker (P.classOf.comp P.fullProjection) := by
  rintro x ⟨z, rfl⟩
  change P.classOf (P.boundaryToCycles z) = 0
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩

/-- The map from full cohomology to relative cohomology. -/
def fullToRelative : P.FullCohomology →ₗ[ℝ] P.Cohomology :=
  (LinearMap.range P.previousToFullCycles).liftQ (P.classOf.comp P.fullProjection)
    P.full_boundaries_map_zero

lemma fullToRelative_class (x : P.FullCycles) :
    P.fullToRelative ((LinearMap.range P.previousToFullCycles).mkQ x) =
      P.classOf (P.fullProjection x) := rfl

/-- Exactness at relative cohomology, including the potentially nonzero
kernel in augmented degree minus one. -/
theorem connecting_kernel_eq_image : LinearMap.ker P.connecting = LinearMap.range P.fullToRelative := by
  ext β
  constructor
  · intro hβ
    obtain ⟨v, rfl⟩ := P.class_surjective β
    have hv : W.connecting v = 0 := hβ
    obtain ⟨u, hu⟩ := (W.connecting_kernel v).1 hv
    let x : P.FullCycles := ⟨(u, v), Prod.ext hu v.property⟩
    exact ⟨(LinearMap.range P.previousToFullCycles).mkQ x, rfl⟩
  · rintro ⟨γ, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range P.previousToFullCycles) γ
    change W.connecting (P.fullProjection x) = 0
    exact (W.connecting_kernel _).2 ⟨x.val.1, congrArg Prod.fst x.property⟩

/-- Exactness in the preceding full degree, not assumed for degree minus one. -/
def ExactAtPrevious : Prop := ∀ u v, W.oldD u + W.liftD v = 0 → W.relativeD v = 0 →
  ∃ z, P.oldPrevious z = u ∧ P.newPrevious z = v

lemma connecting_injective (hexact : P.ExactAtPrevious) : Function.Injective P.connecting := by
  apply (LinearMap.ker_eq_bot).1
  apply le_antisymm _ bot_le
  intro β hβ
  obtain ⟨v, rfl⟩ := P.class_surjective β
  obtain ⟨u, hu⟩ := (W.connecting_kernel v).1 hβ
  obtain ⟨z, hz, hv⟩ := hexact u v hu v.property
  change P.classOf v = 0
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨z, Subtype.ext hv⟩

/-- The isomorphism for degrees where the preceding full complex is exact. -/
def connectingEquiv (hexact : P.ExactAtPrevious) : P.Cohomology ≃ₗ[ℝ] W.Cohomology :=
  LinearEquiv.ofBijective P.connecting ⟨P.connecting_injective hexact, P.connecting_surjective⟩

/-- In all degrees, quotienting by the connecting kernel gives an isomorphism.
`connecting_kernel_eq_image` identifies this kernel with full cohomology's image. -/
def quotientConnectingEquiv :
    (P.Cohomology ⧸ LinearMap.ker P.connecting) ≃ₗ[ℝ] W.Cohomology :=
  P.connecting.quotKerEquivOfSurjective P.connecting_surjective

lemma quotientConnectingEquiv_class (β : P.Cohomology) :
    P.quotientConnectingEquiv ((LinearMap.ker P.connecting).mkQ β) = P.connecting β := rfl

/-- Closed representatives of a relative cohomology class. -/
def representatives (β : P.Cohomology) : Set (X → ℝ) :=
  {v | ∃ hv : W.relativeD v = 0, P.classOf ⟨v, hv⟩ = β}

def relativeValue (r : X → ℝ) (β : P.Cohomology) : ℝ := minimum r (P.representatives β)

lemma representatives_nonempty (β : P.Cohomology) : (P.representatives β).Nonempty := by
  obtain ⟨v, hv⟩ := P.class_surjective β
  exact ⟨v, v.property, hv⟩

lemma representatives_class (v : LinearMap.ker W.relativeD) :
    P.representatives (P.classOf v) = {x | x - v.val ∈ LinearMap.range P.newPrevious} := by
  ext x
  constructor
  · rintro ⟨hx, hc⟩
    have hm := (Submodule.Quotient.eq (LinearMap.range P.boundaryToCycles)).1 hc
    obtain ⟨z, hz⟩ := hm
    exact ⟨z, congrArg Subtype.val hz⟩
  · rintro ⟨z, hz⟩
    have heq : x = P.newPrevious z + v.val := (eq_sub_iff_add_eq.mp hz).symm
    have hx : W.relativeD x = 0 := by rw [heq, map_add, P.new_square, v.property, zero_add]
    refine ⟨hx, ?_⟩
    apply (Submodule.Quotient.eq (LinearMap.range P.boundaryToCycles)).2
    exact ⟨z, Subtype.ext hz⟩

lemma representatives_closed (β : P.Cohomology) : IsClosed (P.representatives β) := by
  obtain ⟨v, rfl⟩ := P.class_surjective β
  rw [P.representatives_class]
  exact (LinearMap.range P.newPrevious).closed_of_finiteDimensional.preimage
    (continuous_id.sub continuous_const)

lemma relativeValue_attained {r : X → ℝ} (hr : ∀ j, 0 < r j) (β : P.Cohomology) :
    ∃ v ∈ P.representatives β, weightedNorm r v = P.relativeValue r β :=
  minimum_attained hr (P.representatives_closed β) (P.representatives_nonempty β)

lemma representatives_eq_fiber (hexact : P.ExactAtPrevious) (β : P.Cohomology) :
    P.representatives β = W.relativeFeasible (P.connecting β) := by
  ext v
  constructor
  · rintro ⟨hv, hβ⟩
    exact ⟨hv, congrArg P.connecting hβ⟩
  · rintro ⟨hv, hβ⟩
    exact ⟨hv, P.connecting_injective hexact hβ⟩

/-- Equality of the independently defined representative minimum and the
obstruction minimum: the norm-preservation part of the relative isomorphism. -/
theorem connecting_preserves_value (hexact : P.ExactAtPrevious) (r : X → ℝ) (β : P.Cohomology) :
    W.obstructionValue r (P.connectingEquiv hexact β) = P.relativeValue r β := by
  change minimum r (W.relativeFeasible (P.connecting β)) = minimum r (P.representatives β)
  rw [P.representatives_eq_fiber hexact]

/-- Representatives after the further quotient by the connecting kernel. -/
def quotientRepresentatives (γ : P.Cohomology ⧸ LinearMap.ker P.connecting) : Set (X → ℝ) :=
  {v | ∃ hv : W.relativeD v = 0, (LinearMap.ker P.connecting).mkQ (P.classOf ⟨v, hv⟩) = γ}

def quotientValue (r : X → ℝ) (γ : P.Cohomology ⧸ LinearMap.ker P.connecting) : ℝ :=
  minimum r (P.quotientRepresentatives γ)

lemma quotientRepresentatives_eq_fiber (γ : P.Cohomology ⧸ LinearMap.ker P.connecting) :
    P.quotientRepresentatives γ = W.relativeFeasible (P.quotientConnectingEquiv γ) := by
  ext v
  constructor
  · rintro ⟨hv, hγ⟩
    exact ⟨hv, congrArg P.quotientConnectingEquiv hγ⟩
  · rintro ⟨hv, hγ⟩
    exact ⟨hv, P.quotientConnectingEquiv.injective hγ⟩

/-- Norm preservation after the additional quotient, without preceding exactness. -/
theorem quotientConnecting_preserves_value (r : X → ℝ)
    (γ : P.Cohomology ⧸ LinearMap.ker P.connecting) :
    W.obstructionValue r (P.quotientConnectingEquiv γ) = P.quotientValue r γ := by
  change minimum r (W.relativeFeasible _) = minimum r (P.quotientRepresentatives γ)
  rw [P.quotientRepresentatives_eq_fiber]

lemma quotientRepresentatives_nonempty (γ : P.Cohomology ⧸ LinearMap.ker P.connecting) :
    (P.quotientRepresentatives γ).Nonempty := by
  rw [P.quotientRepresentatives_eq_fiber]
  exact W.relativeFeasible_nonempty _

lemma relativeValue_nonneg (r : X → ℝ) (β : P.Cohomology) : 0 ≤ P.relativeValue r β :=
  minimum_nonneg (P.representatives_nonempty β)

lemma quotientValue_le_relativeValue (r : X → ℝ) (β : P.Cohomology) :
    P.quotientValue r ((LinearMap.ker P.connecting).mkQ β) ≤ P.relativeValue r β := by
  apply minimum_antitone (P.representatives_nonempty β)
  rintro v ⟨hv, hβ⟩
  exact ⟨hv, congrArg (LinearMap.ker P.connecting).mkQ hβ⟩

lemma quotientValue_attained {r : X → ℝ} (hr : ∀ j, 0 < r j)
    (γ : P.Cohomology ⧸ LinearMap.ker P.connecting) :
    ∃ v ∈ P.quotientRepresentatives γ, weightedNorm r v = P.quotientValue r γ := by
  rw [← P.quotientConnecting_preserves_value, P.quotientRepresentatives_eq_fiber]
  exact W.obstruction_attained hr _

/-- The second minimization is attained by the relative class of a minimizing
closed representative of the final quotient class. -/
theorem successive_minimum_attained {r : X → ℝ} (hr : ∀ j, 0 < r j)
    (γ : P.Cohomology ⧸ LinearMap.ker P.connecting) :
    ∃ β : P.Cohomology, (LinearMap.ker P.connecting).mkQ β = γ ∧
      P.relativeValue r β = P.quotientValue r γ := by
  obtain ⟨v, ⟨hv, hγ⟩, hmin⟩ := P.quotientValue_attained hr γ
  refine ⟨P.classOf ⟨v, hv⟩, hγ, le_antisymm ?_ ?_⟩
  · exact (minimum_le (show v ∈ P.representatives (P.classOf ⟨v, hv⟩) from ⟨hv, rfl⟩)).trans_eq hmin
  · simpa [hγ] using P.quotientValue_le_relativeValue r (P.classOf ⟨v, hv⟩)

/-- Successive minimization over representatives and then the kernel agrees
with direct minimization over representatives of the final quotient. -/
theorem successive_minimum {r : X → ℝ} (hr : ∀ j, 0 < r j)
    (γ : P.Cohomology ⧸ LinearMap.ker P.connecting) :
    P.quotientValue r γ =
      sInf (P.relativeValue r '' {β | (LinearMap.ker P.connecting).mkQ β = γ}) := by
  let S : Set ℝ := P.relativeValue r '' {β | (LinearMap.ker P.connecting).mkQ β = γ}
  change P.quotientValue r γ = sInf S
  obtain ⟨β, hβ, hmin⟩ := P.successive_minimum_attained hr γ
  have hmem : P.relativeValue r β ∈ S := ⟨β, hβ, rfl⟩
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro x ⟨β', _, rfl⟩
    exact P.relativeValue_nonneg r β'
  apply le_antisymm
  · apply le_csInf (show S.Nonempty from ⟨_, hmem⟩)
    rintro x ⟨β', hβ', rfl⟩
    change (LinearMap.ker P.connecting).mkQ β' = γ at hβ'
    rw [← hβ']
    exact P.quotientValue_le_relativeValue r β'
  · exact (csInf_le hbdd hmem).trans_eq hmin

end RelativePredecessor
end WeightedObstructionNorms
