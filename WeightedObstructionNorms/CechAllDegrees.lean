import WeightedObstructionNorms.FiniteObservations
import WeightedObstructionNorms.AlternatingCancellation
import Mathlib.Order.Fin.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The augmented alternating marginal Cech complex in all degrees.
Index n is the number of selected observations, hence paper degree n-1.
The empty tuple uses the full observation. This is an increasing-tuple
complex, not an unnormalised tuple complex. Acyclicity is not assumed. -/
noncomputable section
open scoped BigOperators
namespace WeightedObstructionNorms
namespace CechAllDegrees
open FiniteObservations
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [PartialOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] (S : Finset (State E)) (M : K → Finset I)

abbrev Tuple (n : ℕ) := Fin n ↪o K

def face {n : ℕ} (i : Fin (n + 1)) (t : Tuple (K := K) (n + 1)) : Tuple (K := K) n :=
  (Fin.succAboveOrderEmb i).trans t

lemma skip_identity {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) (k : Fin n) :
    j.succ.succAbove (i.succAbove k) = i.castSucc.succAbove (j.succAbove k) := by
  apply Fin.ext
  dsimp [Fin.succAbove]
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  split_ifs <;> simp at * <;> omega

lemma face_identity {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) (t : Tuple (K := K) (n + 2)) :
    face i (face j.succ t) = face j (face i.castSucc t) := by
  ext k
  exact congrArg t (skip_identity i j h k)

def observation {n : ℕ} (t : Tuple (K := K) n) : Finset I :=
  Finset.univ.filter (fun a => ∀ i, a ∈ M (t i))

lemma mem_observation {n : ℕ} (t : Tuple (K := K) n) (a : I) :
    a ∈ observation M t ↔ ∀ i, a ∈ M (t i) := by simp [observation]

lemma observation_face {n : ℕ} (i : Fin (n + 1)) (t : Tuple (K := K) (n + 1)) :
    observation M t ⊆ observation M (face i t) := by
  intro a ha
  apply (mem_observation M _ _).2
  intro k
  exact (mem_observation M t a).1 ha (i.succAbove k)

abbrev Cochain (n : ℕ) := ∀ t : Tuple (K := K) n, SupportState E S (observation M t) → ℝ

def coface (n : ℕ) (i : Fin (n + 1)) : Cochain E S M n →ₗ[ℝ] Cochain E S M (n + 1) where
  toFun x t := marginal E S (observation_face M i t) (x (face i t))
  map_add' x y := by funext t; exact map_add _ _ _
  map_smul' a x := by funext t; exact map_smul (marginal E S (observation_face M i t)) a (x (face i t))

lemma marginal_congr {n : ℕ} {A : Finset I} (x : Cochain E S M n)
    {t t' : Tuple (K := K) n} (h : t = t')
    (ht : A ⊆ observation M t) (ht' : A ⊆ observation M t') :
    marginal E S ht (x t) = marginal E S ht' (x t') := by
  subst t'
  rfl

/-- The coface relation follows from deletion of two vertices and transitivity
of the actual marginal maps on projected supports. -/
theorem coface_identity (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) (x : Cochain E S M n) :
    coface E S M (n + 1) j.succ (coface E S M n i x) =
      coface E S M (n + 1) i.castSucc (coface E S M n j x) := by
  funext t
  simp only [coface, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [marginal, Marginal.linear, LinearMap.coe_mk, AddHom.coe_mk,
    Marginal.push_comp, supportRestrict_comp]
  exact marginal_congr E S M x (face_identity i j h t) _ _

def differential (n : ℕ) : Cochain E S M n →ₗ[ℝ] Cochain E S M (n + 1) :=
  ∑ i : Fin (n + 1), ((-1 : ℝ) ^ i.val) • coface E S M n i

/-- Square-zero in every augmented degree, with no truncation bound on n. -/
theorem differential_squared (n : ℕ) (x : Cochain E S M n) :
    differential E S M (n + 1) (differential E S M n x) = 0 := by
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  have h := alternating_cancellation n
    (fun i j => coface E S M (n + 1) j (coface E S M n i x)) (by
      intro i j hji
      have hle : j.castLT (lt_of_le_of_lt hji i.is_lt) ≤ i := hji
      simpa using (coface_identity E S M n _ i hle x).symm)
  simpa only [mul_comm] using h

/-- Boundaries as a subspace of cocycles, for each paper degree p ≥ 0. -/
def boundaries (p : ℕ) : Cochain E S M p →ₗ[ℝ] LinearMap.ker (differential E S M (p + 1)) :=
  (differential E S M p).codRestrict _ (differential_squared E S M p)

abbrev Cohomology (p : ℕ) :=
  (LinearMap.ker (differential E S M (p + 1))) ⧸ LinearMap.range (boundaries E S M p)

/-- Extension by zero on the actual local coordinates, in every degree. -/
def extension {T : Finset (State E)} (h : S ⊆ T) (n : ℕ) :
    Cochain E S M n →ₗ[ℝ] Cochain E T M n where
  toFun x t := extend E h (observation M t) (x t)
  map_add' x y := by funext t; exact map_add _ _ _
  map_smul' a x := by funext t; exact map_smul (extend E h (observation M t)) a (x t)

lemma extension_coface {T : Finset (State E)} (h : S ⊆ T) (n : ℕ) (i : Fin (n + 1))
    (x : Cochain E S M n) :
    coface E T M n i (extension E S M h n x) = extension E S M h (n + 1) (coface E S M n i x) := by
  funext t
  exact extension_commutes E h (observation_face M i t) (x (face i t))

/-- All-degree cochain-map identity for support enlargement. -/
theorem extension_differential {T : Finset (State E)} (h : S ⊆ T) (n : ℕ)
    (x : Cochain E S M n) :
    differential E T M n (extension E S M h n x) =
      extension E S M h (n + 1) (differential E S M n x) := by
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    extension_coface]

lemma extension_injective {T : Finset (State E)} (h : S ⊆ T) (n : ℕ) :
    Function.Injective (extension E S M h n) := by
  intro x y hxy
  funext t
  exact FiniteObservations.extension_injective E h (observation M t) (congrFun hxy t)

def cycleExtension {T : Finset (State E)} (h : S ⊆ T) (n : ℕ) :
    LinearMap.ker (differential E S M n) →ₗ[ℝ] LinearMap.ker (differential E T M n) :=
  ((extension E S M h n).domRestrict _).codRestrict _ (by
    intro c
    change differential E T M n (extension E S M h n c.val) = 0
    rw [extension_differential, c.property, map_zero])

lemma extension_boundaries {T : Finset (State E)} (h : S ⊆ T) (p : ℕ) :
    LinearMap.range (boundaries E S M p) ≤ LinearMap.ker
      ((LinearMap.range (boundaries E T M p)).mkQ.comp (cycleExtension E S M h (p + 1))) := by
  rintro c ⟨x, rfl⟩
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact ⟨extension E S M h p x, Subtype.ext (extension_differential E S M h p x)⟩

def cohomologyExtension {T : Finset (State E)} (h : S ⊆ T) (p : ℕ) :
    Cohomology E S M p →ₗ[ℝ] Cohomology E T M p :=
  (LinearMap.range (boundaries E S M p)).liftQ
    ((LinearMap.range (boundaries E T M p)).mkQ.comp (cycleExtension E S M h (p + 1)))
    (extension_boundaries E S M h p)

lemma cohomologyExtension_class {T : Finset (State E)} (h : S ⊆ T) (p : ℕ)
    (c : LinearMap.ker (differential E S M (p + 1))) :
    cohomologyExtension E S M h p ((LinearMap.range (boundaries E S M p)).mkQ c) =
      (LinearMap.range (boundaries E T M p)).mkQ (cycleExtension E S M h (p + 1) c) := rfl

instance cochainFiniteDimensional (n : ℕ) : FiniteDimensional ℝ (Cochain E S M n) := by
  classical
  letI : Fintype (Tuple (K := K) n) := Fintype.ofFinite _
  infer_instance

instance cohomologyFiniteDimensional (p : ℕ) : FiniteDimensional ℝ (Cohomology E S M p) :=
  inferInstance

/-- A finite observation list gives a bounded complex automatically. -/
lemma tuple_card_bound {n : ℕ} (t : Tuple (K := K) n) : n ≤ Fintype.card K := by
  simpa using Fintype.card_le_of_injective t t.injective

lemma cochain_zero_above {n : ℕ} (hn : Fintype.card K < n) (x : Cochain E S M n) : x = 0 := by
  funext t
  exact False.elim (not_lt_of_ge (tuple_card_bound t) hn)

lemma extension_identity (n : ℕ) (x : Cochain E S M n) :
    extension E S M (Finset.Subset.refl S) n x = x := by
  funext t
  change Marginal.push (supportInclude E (Finset.Subset.refl S) (observation M t)) (x t) = x t
  have h : supportInclude E (Finset.Subset.refl S) (observation M t) = id := rfl
  rw [h, Marginal.push_id]

lemma extension_comp {T U : Finset (State E)} (hST : S ⊆ T) (hTU : T ⊆ U)
    (n : ℕ) (x : Cochain E S M n) :
    extension E T M hTU n (extension E S M hST n x) = extension E S M (hST.trans hTU) n x := by
  funext t
  change Marginal.push _ (Marginal.push _ (x t)) = Marginal.push _ (x t)
  rw [Marginal.push_comp]
  rfl

lemma cohomologyExtension_identity (p : ℕ) (α : Cohomology E S M p) :
    cohomologyExtension E S M (Finset.Subset.refl S) p α = α := by
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (boundaries E S M p)) α
  apply congrArg (LinearMap.range (boundaries E S M p)).mkQ
  apply Subtype.ext
  exact extension_identity E S M (p + 1) x.val

lemma cohomologyExtension_comp {T U : Finset (State E)} (hST : S ⊆ T) (hTU : T ⊆ U)
    (p : ℕ) (α : Cohomology E S M p) :
    cohomologyExtension E T M hTU p (cohomologyExtension E S M hST p α) =
      cohomologyExtension E S M (hST.trans hTU) p α := by
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (boundaries E S M p)) α
  apply congrArg (LinearMap.range (boundaries E U M p)).mkQ
  apply Subtype.ext
  exact extension_comp E S M hST hTU (p + 1) x.val

/-- The unique empty increasing tuple. -/
def emptyTuple : Tuple (K := K) 0 :=
  OrderEmbedding.ofStrictMono Fin.elim0 (by intro i; exact Fin.elim0 i)

lemma tuple_zero_unique (t : Tuple (K := K) 0) : t = emptyTuple := by
  ext i
  exact Fin.elim0 i

lemma observation_zero (t : Tuple (K := K) 0) : observation M t = Finset.univ := by
  ext a
  simp only [mem_observation, Finset.mem_univ, iff_true]
  intro i
  exact Fin.elim0 i

def globalProject {n : ℕ} (t : Tuple (K := K) n) (z : {z // z ∈ S}) :
    SupportState E S (observation M t) :=
  ⟨project E (observation M t) z.val, (projected_mem E S _ _).2 ⟨z.val, z.property, rfl⟩⟩

lemma globalProject_zero_injective (t : Tuple (K := K) 0) :
    Function.Injective (globalProject E S M t) := by
  intro z w h
  apply Subtype.ext
  funext a
  have ha : a ∈ observation M t := (mem_observation M t a).2 (fun i => Fin.elim0 i)
  exact congrFun (congrArg (fun y : SupportState E S (observation M t) => y.val) h) ⟨a,ha⟩

lemma globalProject_surjective {n : ℕ} (t : Tuple (K := K) n) :
    Function.Surjective (globalProject E S M t) := by
  intro y
  obtain ⟨z,hz,hzy⟩ := (projected_mem E S _ _).1 y.property
  exact ⟨⟨z,hz⟩, Subtype.ext hzy⟩

def globalPointEquiv (t : Tuple (K := K) 0) : {z // z ∈ S} ≃ SupportState E S (observation M t) :=
  Equiv.ofBijective (globalProject E S M t)
    ⟨globalProject_zero_injective E S M t, globalProject_surjective E S M t⟩

/-- Index zero of this complex is genuinely the global signed-measure space
R^S appearing in paper degree minus one. -/
def augmentationEquiv : ({z // z ∈ S} → ℝ) ≃ₗ[ℝ] Cochain E S M 0 where
  toFun x t y := x ((globalPointEquiv E S M t).symm y)
  invFun x z := x emptyTuple (globalProject E S M emptyTuple z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    funext z
    exact congrArg x ((globalPointEquiv E S M emptyTuple).symm_apply_apply z)
  right_inv x := by
    funext t y
    have ht := tuple_zero_unique t
    subst t
    exact congrArg (x emptyTuple) ((globalPointEquiv E S M emptyTuple).apply_symm_apply y)

lemma augmentationEquiv_push (x : {z // z ∈ S} → ℝ) (t : Tuple (K := K) 0) :
    augmentationEquiv E S M x t = Marginal.push (globalProject E S M t) x := by
  funext y
  obtain ⟨z,rfl⟩ := globalProject_surjective E S M t y
  rw [Marginal.push_injective_apply _ (globalProject_zero_injective E S M t)]
  exact congrArg x ((globalPointEquiv E S M t).symm_apply_apply z)

/-- The first differential is precisely the family of global marginal maps. -/
theorem differential_augmentation (x : {z // z ∈ S} → ℝ) (t : Tuple (K := K) 1) :
    differential E S M 0 (augmentationEquiv E S M x) t = Marginal.push (globalProject E S M t) x := by
  have hd : differential E S M 0 = coface E S M 0 0 := by
    simp [differential, Fin.sum_univ_succ]
  rw [hd]
  change Marginal.push _ (augmentationEquiv E S M x (face 0 t)) = _
  rw [augmentationEquiv_push, Marginal.push_comp]
  rfl

end CechAllDegrees
end WeightedObstructionNorms
