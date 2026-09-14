import WeightedObstructionNorms.AlternatingEvaluation

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace WeightedObstructionNorms
namespace ObservationRestriction
open FiniteObservations CechAllDegrees AlternatingEvaluation
variable {I K L : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [LinearOrder K] [Fintype L] [LinearOrder L]
    (E : I → Type*) [∀ i, Fintype (E i)] (S : Finset (State E)) (M : K → Finset I)

abbrev Vertex (A : Finset I) := {k : K // A ⊆ M k}
instance vertexFintype (A : Finset I) : Fintype (Vertex M A) := Fintype.ofFinite _

def forget {A : Finset I} {n : ℕ} (t : Tuple (K := Vertex M A) n) : Tuple (K := K) n :=
  OrderEmbedding.ofStrictMono (fun i => (t i).val) t.strictMono

lemma contains {A : Finset I} {n : ℕ} (t : Tuple (K := Vertex M A) n) : A ⊆ observation M (forget M t) := by
  intro a ha
  exact (mem_observation M _ a).2 (fun i => (t i).property ha)

def project (A : Finset I) (n : ℕ) : Cochain E S M n →ₗ[ℝ]
    (Tuple (K := Vertex M A) n → SupportState E S A → ℝ) where
  toFun x t := marginal E S (contains M t) (x (forget M t))
  map_add' x y := by funext t; exact map_add _ _ _
  map_smul' a x := by funext t; exact map_smul (marginal E S (contains M t)) a _

lemma project_differential (A : Finset I) (n : ℕ) (x : Cochain E S M n) :
    project E S M A (n + 1) (differential E S M n x) =
      SimplexContraction.differential n (project E S M A n x) := by
  funext t
  simp only [project, differential, coface, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply,
    map_sum, map_smul, SimplexContraction.differential]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [marginal_comp]
  rfl

def vertexInclude {A B : Finset I} (h : A ⊆ B) : Vertex M B ↪o Vertex M A :=
  OrderEmbedding.ofStrictMono (fun k => ⟨k.val, h.trans k.property⟩) (fun _ _ hk => hk)

lemma project_naturality {A B : Finset I} (h : A ⊆ B) (n : ℕ) (x : Cochain E S M n)
    (t : Tuple (K := Vertex M B) n) :
    marginal E S h (project E S M B n x t) = project E S M A n x (t.trans (vertexInclude M h)) := by
  change marginal E S h (marginal E S (contains M t) (x (forget M t))) = _
  rw [marginal_comp]
  rfl

lemma evaluate_naturality {A B : Finset I} (h : A ⊆ B) (n : ℕ) (x : Cochain E S M n)
    (v : Fin n → Vertex M B) :
    marginal E S h (evaluate (project E S M B n x) v) =
      evaluate (project E S M A n x) (vertexInclude M h ∘ v) := by
  rw [evaluate_linear, evaluate_orderEmbedding]
  congr 1
  funext t
  exact project_naturality E S M h n x t

variable (N : L → Finset I) (f : L → K) (hf : ∀ a, N a ⊆ M (f a))

def selected {n : ℕ} (t : Tuple (K := L) n) : Fin n → Vertex M (observation N t) :=
  fun i => ⟨f (t i), fun a ha => hf (t i) ((mem_observation N t a).1 ha i)⟩

lemma selected_face {n : ℕ} (t : Tuple (K := L) (n + 1)) (i : Fin (n + 1)) :
    vertexInclude M (observation_face N i t) ∘ selected M N f hf (face i t) =
      selected M N f hf t ∘ i.succAbove := rfl

/-- The actual observation restriction, using alternating evaluation to handle
arbitrary selections, repeated indices, and out-of-order indices. -/
def restriction (n : ℕ) : Cochain E S M n →ₗ[ℝ] Cochain E S N n where
  toFun x t := evaluate (project E S M (observation N t) n x) (selected M N f hf t)
  map_add' x y := by funext t; rw [map_add, evaluate_add]; rfl
  map_smul' a x := by funext t; rw [map_smul, evaluate_smul]; rfl

/-- Theorem 5.1: the concrete restriction commutes with the Cech differential
in all augmented degrees, without an order-preserving assumption on f. -/
theorem restriction_differential (n : ℕ) (x : Cochain E S M n) :
    differential E S N n (restriction E S M N f hf n x) =
      restriction E S M N f hf (n + 1) (differential E S M n x) := by
  funext t
  change _ = evaluate (project E S M (observation N t) (n + 1)
    (differential E S M n x)) (selected M N f hf t)
  rw [project_differential, evaluate_differential]
  conv_lhs => simp only [differential, coface, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, restriction]
  unfold rawDifferential
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [evaluate_naturality, selected_face]

def vertexSelect (A : Finset I) : Vertex N A → Vertex M A :=
  fun a => ⟨f a.val, a.property.trans (hf a.val)⟩

lemma project_restriction (A : Finset I) (n : ℕ) (x : Cochain E S M n) :
    project E S N A n (restriction E S M N f hf n x) =
      pull (vertexSelect M N f hf A) (project E S M A n x) := by
  funext t
  change marginal E S (contains N t)
    (evaluate (project E S M (observation N (forget N t)) n x) (selected M N f hf (forget N t))) = _
  rw [evaluate_naturality]
  rfl

lemma restriction_comp {P : Type*} [Fintype P] [LinearOrder P]
    (O : P → Finset I) (g : P → L) (hg : ∀ a, O a ⊆ N (g a))
    (n : ℕ) (x : Cochain E S M n) :
    restriction E S N O g hg n (restriction E S M N f hf n x) =
      restriction E S M O (f ∘ g) (fun a => (hg a).trans (hf (g a))) n x := by
  funext t
  change evaluate (project E S N (observation O t) n (restriction E S M N f hf n x)) _ = _
  rw [project_restriction, evaluate_pull]
  rfl

lemma restriction_identity (n : ℕ) (x : Cochain E S M n) :
    restriction E S M M id (fun _ => Finset.Subset.refl _) n x = x := by
  funext t
  let u : Tuple (K := Vertex M (observation M t)) n :=
    OrderEmbedding.ofStrictMono (selected M M id (fun _ => Finset.Subset.refl _) t) t.strictMono
  change evaluate (project E S M (observation M t) n x) u = x t
  rw [evaluate_ordered]
  change Marginal.push (supportRestrict E S (contains M u)) (x t) = x t
  exact Marginal.push_id (x t)

lemma project_extension {T : Finset (State E)} (hST : S ⊆ T) (A : Finset I)
    (n : ℕ) (x : Cochain E S M n) :
    project E T M A n (extension E S M hST n x) =
      fun t => extend E hST A (project E S M A n x t) := by
  funext t
  exact extension_commutes E hST (contains M t) (x (forget M t))

/-- Restriction commutes with extension by zero on the prescribed support. -/
theorem restriction_extension {T : Finset (State E)} (hST : S ⊆ T)
    (n : ℕ) (x : Cochain E S M n) :
    restriction E T M N f hf n (extension E S M hST n x) =
      extension E S N hST n (restriction E S M N f hf n x) := by
  funext t
  change evaluate (project E T M (observation N t) n (extension E S M hST n x)) _ = _
  rw [project_extension, ← evaluate_linear]
  rfl

def cycleMap (p : ℕ) : LinearMap.ker (differential E S M (p + 1)) →ₗ[ℝ]
    LinearMap.ker (differential E S N (p + 1)) :=
  ((restriction E S M N f hf (p + 1)).domRestrict _).codRestrict _ (fun c => by
    change differential E S N (p + 1) (restriction E S M N f hf (p + 1) c.val) = 0
    rw [restriction_differential, c.property, map_zero])

lemma boundaries_map (p : ℕ) : LinearMap.range (boundaries E S M p) ≤
    LinearMap.ker ((LinearMap.range (boundaries E S N p)).mkQ.comp (cycleMap E S M N f hf p)) := by
  rintro c ⟨u, rfl⟩
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact ⟨restriction E S M N f hf p u, Subtype.ext (restriction_differential E S M N f hf p u)⟩

def cohomologyMap (p : ℕ) : Cohomology E S M p →ₗ[ℝ] Cohomology E S N p :=
  (LinearMap.range (boundaries E S M p)).liftQ
    ((LinearMap.range (boundaries E S N p)).mkQ.comp (cycleMap E S M N f hf p))
    (boundaries_map E S M N f hf p)

@[simp] lemma cohomologyMap_class (p : ℕ) (c : LinearMap.ker (differential E S M (p + 1))) :
    cohomologyMap E S M N f hf p (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (cycleMap E S M N f hf p c) := rfl

lemma cohomologyMap_identity (p : ℕ) (α : Cohomology E S M p) :
    cohomologyMap E S M M id (fun _ => Finset.Subset.refl _) p α = α := by
  induction α using Submodule.Quotient.induction_on with
  | H c =>
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact restriction_identity E S M (p + 1) c.val

lemma cohomologyMap_comp {P : Type*} [Fintype P] [LinearOrder P]
    (O : P → Finset I) (g : P → L) (hg : ∀ a, O a ⊆ N (g a))
    (p : ℕ) (α : Cohomology E S M p) :
    cohomologyMap E S N O g hg p (cohomologyMap E S M N f hf p α) =
      cohomologyMap E S M O (f ∘ g) (fun a => (hg a).trans (hf (g a))) p α := by
  induction α using Submodule.Quotient.induction_on with
  | H c =>
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact restriction_comp E S M N f hf O g hg (p + 1) c.val

lemma cohomologyMap_extension {T : Finset (State E)} (hST : S ⊆ T)
    (p : ℕ) (α : Cohomology E S M p) :
    cohomologyMap E T M N f hf p (cohomologyExtension E S M hST p α) =
      cohomologyExtension E S N hST p (cohomologyMap E S M N f hf p α) := by
  induction α using Submodule.Quotient.induction_on with
  | H c =>
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact restriction_extension E S M N f hf hST (p + 1) c.val

end ObservationRestriction
end WeightedObstructionNorms
