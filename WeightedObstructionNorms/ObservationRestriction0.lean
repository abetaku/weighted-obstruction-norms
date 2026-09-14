import WeightedObstructionNorms.CechLowDegrees

noncomputable section
namespace WeightedObstructionNorms
namespace CechLowDegrees
open FiniteObservations
variable {I K L : Type*} [Fintype I] [DecidableEq I] [Fintype K] [LinearOrder K]
    [Fintype L] [LinearOrder L]
    (E : I → Type*) [∀ i, Fintype (E i)] (S : Finset (State E))
    (M : K → Finset I) (N : L → Finset I)

/-- A closed degree-zero cochain has equal marginals on every common
subobservation, including reversed or repeated selected indices. -/
lemma closed_marginals_equal (x : LinearMap.ker (d0 E S M)) {i j : K} {A : Finset I}
    (hi : A ⊆ M i) (hj : A ⊆ M j) :
    marginal E S hi (x.val i) = marginal E S hj (x.val j) := by
  have ordered : ∀ i j (hij : i < j) (hi : A ⊆ M i) (hj : A ⊆ M j),
      marginal E S hi (x.val i) = marginal E S hj (x.val j) := by
    intro i j hij hi hj
    let p : Pair (K := K) := ⟨(i,j), hij⟩
    have hx := congrFun x.property p
    change marginal E S Finset.inter_subset_right (x.val j) -
      marginal E S Finset.inter_subset_left (x.val i) = 0 at hx
    have hA : A ⊆ M i ∩ M j := Finset.subset_inter hi hj
    have heq := congrArg (marginal E S hA) (sub_eq_zero.mp hx)
    simp only [marginal_comp] at heq
    exact heq.symm
  rcases lt_trichotomy i j with hij | hij | hij
  · exact ordered i j hij hi hj
  · subst j; rfl
  · exact (ordered j i hij hj hi).symm

/-- The actual degree-zero observation restriction of Equation (5.1). -/
def restriction0 (f : L → K) (hf : ∀ a, N a ⊆ M (f a)) : C0 E S M →ₗ[ℝ] C0 E S N where
  toFun x a := marginal E S (hf a) (x (f a))
  map_add' x y := by funext a; exact map_add _ _ _
  map_smul' c x := by funext a; exact map_smul (marginal E S (hf a)) c (x (f a))

lemma restriction0_closed (f : L → K) (hf : ∀ a, N a ⊆ M (f a))
    (x : LinearMap.ker (d0 E S M)) : d0 E S N (restriction0 E S M N f hf x.val) = 0 := by
  funext p
  change marginal E S Finset.inter_subset_right (marginal E S (hf p.val.2) (x.val (f p.val.2))) -
    marginal E S Finset.inter_subset_left (marginal E S (hf p.val.1) (x.val (f p.val.1))) = 0
  rw [marginal_comp, marginal_comp]
  exact sub_eq_zero.mpr (closed_marginals_equal E S M x _ _)

lemma restriction0_augmentation (f : L → K) (hf : ∀ a, N a ⊆ M (f a))
    (x : {z // z ∈ S} → ℝ) :
    restriction0 E S M N f hf (augmentation E S M x) = augmentation E S N x := by
  funext a
  change Marginal.push _ (Marginal.push _ x) = Marginal.push _ x
  rw [Marginal.push_comp]
  rfl

def restrictionCycle0 (f : L → K) (hf : ∀ a, N a ⊆ M (f a)) :
    LinearMap.ker (d0 E S M) →ₗ[ℝ] LinearMap.ker (d0 E S N) :=
  ((restriction0 E S M N f hf).domRestrict _).codRestrict _ (restriction0_closed E S M N f hf)

lemma restriction0_boundaries (f : L → K) (hf : ∀ a, N a ⊆ M (f a)) :
    LinearMap.range (boundaries0 E S M) ≤ LinearMap.ker
      ((LinearMap.range (boundaries0 E S N)).mkQ.comp (restrictionCycle0 E S M N f hf)) := by
  rintro c ⟨x, rfl⟩
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact ⟨x, Subtype.ext (restriction0_augmentation E S M N f hf x).symm⟩

/-- Restriction on the actual concrete degree-zero cohomology quotient. -/
def restrictionH0 (f : L → K) (hf : ∀ a, N a ⊆ M (f a)) : H0 E S M →ₗ[ℝ] H0 E S N :=
  (LinearMap.range (boundaries0 E S M)).liftQ
    ((LinearMap.range (boundaries0 E S N)).mkQ.comp (restrictionCycle0 E S M N f hf))
    (restriction0_boundaries E S M N f hf)

/-- In degree zero the restrictions agree already on closed cochains. -/
theorem restrictionCycle0_choice_independent (f g : L → K)
    (hf : ∀ a, N a ⊆ M (f a)) (hg : ∀ a, N a ⊆ M (g a))
    (x : LinearMap.ker (d0 E S M)) :
    restrictionCycle0 E S M N f hf x = restrictionCycle0 E S M N g hg x := by
  apply Subtype.ext
  funext a
  exact closed_marginals_equal E S M x (hf a) (hg a)

theorem restrictionH0_choice_independent (f g : L → K)
    (hf : ∀ a, N a ⊆ M (f a)) (hg : ∀ a, N a ⊆ M (g a)) :
    restrictionH0 E S M N f hf = restrictionH0 E S M N g hg := by
  apply LinearMap.ext
  intro α
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (boundaries0 E S M)) α
  change (LinearMap.range (boundaries0 E S N)).mkQ (restrictionCycle0 E S M N f hf x) = _
  rw [restrictionCycle0_choice_independent E S M N f g hf hg]
  rfl

/-- Observation restriction commutes with support extension on actual cochains. -/
lemma restriction0_support {T : Finset (State E)} (hST : S ⊆ T)
    (f : L → K) (hf : ∀ a, N a ⊆ M (f a)) (x : C0 E S M) :
    restriction0 E T M N f hf (extend0 E S M hST x) =
      extend0 E S N hST (restriction0 E S M N f hf x) := by
  funext a
  exact extension_commutes E hST (hf a) (x (f a))

lemma restrictionH0_support {T : Finset (State E)} (hST : S ⊆ T)
    (f : L → K) (hf : ∀ a, N a ⊆ M (f a)) (α : H0 E S M) :
    restrictionH0 E T M N f hf (cohomologyExtend0 E S M hST α) =
      cohomologyExtend0 E S N hST (restrictionH0 E S M N f hf α) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (boundaries0 E S M)) α
  apply congrArg (LinearMap.range (boundaries0 E T N)).mkQ
  apply Subtype.ext
  exact restriction0_support E S M N hST f hf x.val

lemma restriction0_identity (x : C0 E S M) :
    restriction0 E S M M id (fun _ => Finset.Subset.refl _) x = x := by
  funext i
  change Marginal.push (supportRestrict E S (Finset.Subset.refl (M i))) (x i) = x i
  have h : supportRestrict E S (Finset.Subset.refl (M i)) = id := rfl
  rw [h, Marginal.push_id]

lemma restrictionH0_identity (α : H0 E S M) :
    restrictionH0 E S M M id (fun _ => Finset.Subset.refl _) α = α := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (boundaries0 E S M)) α
  apply congrArg (LinearMap.range (boundaries0 E S M)).mkQ
  apply Subtype.ext
  exact restriction0_identity E S M x.val

variable {R : Type*} [Fintype R] [LinearOrder R]

lemma restriction0_comp (O : R → Finset I) (f : L → K) (g : R → L)
    (hf : ∀ a, N a ⊆ M (f a)) (hg : ∀ b, O b ⊆ N (g b)) (x : C0 E S M) :
    restriction0 E S N O g hg (restriction0 E S M N f hf x) =
      restriction0 E S M O (f ∘ g) (fun b => (hg b).trans (hf (g b))) x := by
  funext b
  exact marginal_comp E S (hg b) (hf (g b)) (x (f (g b)))

lemma restrictionH0_comp (O : R → Finset I) (f : L → K) (g : R → L)
    (hf : ∀ a, N a ⊆ M (f a)) (hg : ∀ b, O b ⊆ N (g b)) (α : H0 E S M) :
    restrictionH0 E S N O g hg (restrictionH0 E S M N f hf α) =
      restrictionH0 E S M O (f ∘ g) (fun b => (hg b).trans (hf (g b))) α := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (boundaries0 E S M)) α
  apply congrArg (LinearMap.range (boundaries0 E S O)).mkQ
  apply Subtype.ext
  exact restriction0_comp E S M N O f g hf hg x.val

/-- Two generating lists with mutual selection maps have inverse H^0 maps.
This proves the concrete algebraic part; the obstruction-norm identification
for these concrete complexes remains a separate task. -/
lemma restrictionH0_mutual_inverse (f : L → K) (g : K → L)
    (hf : ∀ a, N a ⊆ M (f a)) (hg : ∀ i, M i ⊆ N (g i)) (α : H0 E S M) :
    restrictionH0 E S N M g hg (restrictionH0 E S M N f hf α) = α := by
  rw [restrictionH0_comp]
  rw [restrictionH0_choice_independent E S M M (f ∘ g) id
    (fun i => (hg i).trans (hf (g i))) (fun _ => Finset.Subset.refl _)]
  exact restrictionH0_identity E S M α

def restrictionH0Equiv (f : L → K) (g : K → L)
    (hf : ∀ a, N a ⊆ M (f a)) (hg : ∀ i, M i ⊆ N (g i)) : H0 E S M ≃ₗ[ℝ] H0 E S N where
  toLinearMap := restrictionH0 E S M N f hf
  invFun := restrictionH0 E S N M g hg
  left_inv := restrictionH0_mutual_inverse E S M N f g hf hg
  right_inv := restrictionH0_mutual_inverse E S N M g f hg hf

/-- The downward-closed observation family generated by a list. -/
def generated (M : K → Finset I) : Set (Finset I) := {A | ∃ i, A ⊆ M i}

lemma exists_selection (h : generated N ⊆ generated M) :
    ∃ f : L → K, ∀ a, N a ⊆ M (f a) := by
  have hex : ∀ a, ∃ i, N a ⊆ M i := fun a => h ⟨a, Finset.Subset.refl _⟩
  exact ⟨fun a => Classical.choose (hex a), fun a => Classical.choose_spec (hex a)⟩

/-- The H^0 group depends only on the generated observation family, with
no supplied cohomology maps or homotopies as assumptions. -/
theorem generated_H0_equiv (h : generated M = generated N) :
    Nonempty (H0 E S M ≃ₗ[ℝ] H0 E S N) := by
  obtain ⟨f, hf⟩ := exists_selection M N (by rw [h])
  obtain ⟨g, hg⟩ := exists_selection N M (by rw [h])
  exact ⟨restrictionH0Equiv E S M N f g hf hg⟩

end CechLowDegrees
end WeightedObstructionNorms
