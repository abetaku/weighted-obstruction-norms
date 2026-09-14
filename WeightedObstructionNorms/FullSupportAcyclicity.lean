import WeightedObstructionNorms.InteractionCoordinates
import WeightedObstructionNorms.SimplexContraction

noncomputable section
open scoped BigOperators
namespace WeightedObstructionNorms
namespace FullSupportAcyclicity
open FiniteObservations CechAllDegrees InteractionCoordinates
section General
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [PartialOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (o : State E) (M : K → Finset I)

abbrev Vertex (y : State E) := {k : K // ∀ j, y j ≠ o j → j ∈ M k}

abbrev Raw (n : ℕ) := ∀ t : Tuple (K := K) n, LocalState E (observation M t) → ℝ

def forget {y : State E} {n : ℕ} (t : Tuple (K := Vertex E o M y) n) : Tuple (K := K) n :=
  OrderEmbedding.ofStrictMono (fun i => (t i).val) t.strictMono

lemma supported {y : State E} {n : ℕ} (t : Tuple (K := Vertex E o M y) n) :
    ∀ j, j ∉ observation M (forget E o M t) → y j = o j := by
  intro j hj
  by_contra h
  apply hj
  exact (mem_observation M _ j).2 (fun i => (t i).property j h)

def eligible {n : ℕ} (t : Tuple (K := K) n) (y : State E)
    (hy : ∀ j, j ∉ observation M t → y j = o j) : Tuple (K := Vertex E o M y) n :=
  OrderEmbedding.ofStrictMono (fun i => ⟨t i, fun j hj => by
    have hm : j ∈ observation M t := by by_contra hn; exact hj (hy j hn)
    exact (mem_observation M t j).1 hm i⟩) t.strictMono

lemma forget_eligible {n : ℕ} (t : Tuple (K := K) n) (y : State E)
    (hy : ∀ j, j ∉ observation M t → y j = o j) :
    forget E o M (eligible E o M t y hy) = t := by ext i; rfl

lemma eligible_forget {y : State E} {n : ℕ} (t : Tuple (K := Vertex E o M y) n) :
    eligible E o M (forget E o M t) y (supported E o M t) = t := by ext i; rfl

lemma forget_face {y : State E} {n : ℕ} (t : Tuple (K := Vertex E o M y) (n + 1)) (i : Fin (n + 1)) :
    forget E o M (face i t) = face i (forget E o M t) := rfl

def component (n : ℕ) (x : Raw E M n) (y : State E)
    (t : Tuple (K := Vertex E o M y) n) : ℝ :=
  forward (fun i : observation M (forget E o M t) => E i.val)
    (project E _ o) (x (forget E o M t)) (project E _ y)

def assemble (n : ℕ) (a : ∀ y : State E, Tuple (K := Vertex E o M y) n → ℝ) : Raw E M n :=
  fun t => inverse (fun i : observation M t => E i.val) (project E _ o)
    (fun z => a (complete E o _ z)
      (eligible E o M t _ (complete_supported E o _ z)))

lemma evaluation_congr (n : ℕ) (a : ∀ y : State E, Tuple (K := Vertex E o M y) n → ℝ)
    (y z : State E) (h : y = z) (t : Tuple (K := Vertex E o M y) n)
    (u : Tuple (K := Vertex E o M z) n) (htu : ∀ i, (t i).val = (u i).val) :
    a y t = a z u := by
  subst z
  have he : t = u := by ext i; exact htu i
  rw [he]

lemma component_assemble (n : ℕ) (a : ∀ y : State E, Tuple (K := Vertex E o M y) n → ℝ)
    (y : State E) (t : Tuple (K := Vertex E o M y) n) :
    component E o M n (assemble E o M n a) y t = a y t := by
  unfold component assemble
  rw [forward_inverse_apply]
  have hy := complete_project E o y _ (supported E o M t)
  exact evaluation_congr E o M n a _ y hy _ t (fun _ => rfl)

lemma component_injective (n : ℕ) (x z : Raw E M n)
    (h : ∀ y t, component E o M n x y t = component E o M n z y t) : x = z := by
  funext t
  apply forward_injective (fun i : observation M t => E i.val) (project E _ o)
  funext a
  have hh := h (complete E o _ a) (eligible E o M t _ (complete_supported E o _ a))
  change forward (fun i : observation M t => E i.val) (project E _ o) (x t)
      (project E _ (complete E o _ a)) =
    forward (fun i : observation M t => E i.val) (project E _ o) (z t)
      (project E _ (complete E o _ a)) at hh
  simpa only [project_complete] using hh

def differential (n : ℕ) (x : Raw E M n) : Raw E M (n + 1) :=
  fun t => ∑ i : Fin (n + 1), ((-1 : ℝ) ^ i.val) •
    Marginal.push (restrict E (observation_face M i t)) (x (face i t))

lemma component_differential (n : ℕ) (x : Raw E M n) (y : State E)
    (t : Tuple (K := Vertex E o M y) (n + 1)) :
    component E o M (n + 1) (differential E M n x) y t =
      SimplexContraction.differential n (component E o M n x y) t := by
  unfold component differential
  change (forwardLinear _ _ (∑ i : Fin (n + 1), _)) _ = _
  rw [map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, SimplexContraction.differential]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact forward_restrict E o y (observation_face M i (forget E o M t))
    (supported E o M t) (x (face i (forget E o M t)))

def ComponentExact : Prop := ∀ (y : State E) (n : ℕ)
    (x : Tuple (K := Vertex E o M y) (n + 1) → ℝ),
    SimplexContraction.differential (n + 1) x = 0 →
      ∃ u, SimplexContraction.differential n u = x

include o in
/-- Full local signed-measure cochains are exact in every nonnegative paper
 degree. The proof splits them into the simplex components above. -/
theorem raw_exists_primitive_of_components (hcomp : ComponentExact E o M) (n : ℕ) (x : Raw E M (n + 1))
    (hx : differential E M (n + 1) x = 0) : ∃ u, differential E M n u = x := by
  classical
  have hc (y : State E) :
      SimplexContraction.differential (n + 1) (component E o M (n + 1) x y) = 0 := by
    funext t
    rw [← component_differential, hx]
    simp [component, forward]
  have hp (y : State E) : ∃ u, SimplexContraction.differential n u =
      component E o M (n + 1) x y := by
    letI : Fintype (Vertex E o M y) := Fintype.ofFinite _
    exact hcomp y n _ (hc y)
  choose u hu using hp
  refine ⟨assemble E o M n u, component_injective E o M (n + 1) _ x ?_⟩
  intro y t
  rw [component_differential]
  have he : component E o M n (assemble E o M n u) y = u y := by
    funext s
    exact component_assemble E o M n u y s
  rw [he]
  exact congrFun (hu y) t

def fullPoint (A : Finset I) (z : LocalState E A) : SupportState E Finset.univ A :=
  ⟨z, (projected_mem E Finset.univ A z).2
    ⟨complete E o A z, Finset.mem_univ _, project_complete E o A z⟩⟩

lemma fullPoint_val (A : Finset I) (z : LocalState E A) : (fullPoint E o A z).val = z := rfl

lemma fullPoint_coe (A : Finset I) (z : SupportState E Finset.univ A) :
    fullPoint E o A z.val = z := Subtype.ext rfl

def toRaw (n : ℕ) (x : CechAllDegrees.Cochain E Finset.univ M n) : Raw E M n :=
  fun t z => x t (fullPoint E o _ z)

def ofRaw (n : ℕ) (x : Raw E M n) : CechAllDegrees.Cochain E Finset.univ M n :=
  fun t z => x t z.val

lemma toRaw_ofRaw (n : ℕ) (x : Raw E M n) : toRaw E o M n (ofRaw E M n x) = x := rfl

lemma ofRaw_toRaw (n : ℕ) (x : CechAllDegrees.Cochain E Finset.univ M n) :
    ofRaw E M n (toRaw E o M n x) = x := by
  funext t z
  exact congrArg (x t) (fullPoint_coe E o _ z)

lemma full_push (A : Finset I) (x : SupportState E Finset.univ A → ℝ) :
    Marginal.push Subtype.val x = fun z => x (fullPoint E o A z) := by
  classical
  funext z
  exact Marginal.push_injective_apply Subtype.val Subtype.val_injective x (fullPoint E o A z)

lemma marginal_toRaw {A B : Finset I} (hAB : A ⊆ B)
    (x : SupportState E Finset.univ B → ℝ) :
    (fun z => marginal E Finset.univ hAB x (fullPoint E o A z)) =
      Marginal.push (restrict E hAB) (fun z => x (fullPoint E o B z)) := by
  rw [← full_push E o A, ← full_push E o B]
  change Marginal.push Subtype.val (Marginal.push _ x) = Marginal.push _ (Marginal.push _ x)
  rw [Marginal.push_comp, Marginal.push_comp]
  rfl

lemma toRaw_differential (n : ℕ) (x : CechAllDegrees.Cochain E Finset.univ M n) :
    toRaw E o M (n + 1) (CechAllDegrees.differential E Finset.univ M n x) =
      differential E M n (toRaw E o M n x) := by
  funext t z
  simp only [toRaw, CechAllDegrees.differential, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, coface,
    LinearMap.coe_mk, AddHom.coe_mk, differential]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact congrFun (marginal_toRaw E o (observation_face M i t) (x (face i t))) z

include o in
/-- Lemma 2.1 of the paper, on the same projected-support increasing-tuple
complex used throughout the formalization. -/
theorem full_exists_primitive_of_components (hcomp : ComponentExact E o M) (n : ℕ) (x : CechAllDegrees.Cochain E Finset.univ M (n + 1))
    (hx : CechAllDegrees.differential E Finset.univ M (n + 1) x = 0) :
    ∃ u, CechAllDegrees.differential E Finset.univ M n u = x := by
  have hr : differential E M (n + 1) (toRaw E o M (n + 1) x) = 0 := by
    rw [← toRaw_differential, hx]
    rfl
  obtain ⟨u, hu⟩ := raw_exists_primitive_of_components E o M hcomp n _ hr
  refine ⟨ofRaw E M n u, ?_⟩
  have he : toRaw E o M (n + 1)
      (CechAllDegrees.differential E Finset.univ M n (ofRaw E M n u)) =
      toRaw E o M (n + 1) x := by
    rw [toRaw_differential, toRaw_ofRaw, hu]
  have hf := congrArg (ofRaw E M (n + 1)) he
  simpa only [ofRaw_toRaw] using hf

end General
section Linear
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [LinearOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (o : State E) (M : K → Finset I)

lemma componentExact : ComponentExact E o M := by
  intro y n x hx
  letI : Fintype (Vertex E o M y) := Fintype.ofFinite _
  exact SimplexContraction.exists_primitive n x hx

include o in
lemma raw_exists_primitive (n : ℕ) (x : Raw E M (n + 1))
    (hx : differential E M (n + 1) x = 0) : ∃ u, differential E M n u = x :=
  raw_exists_primitive_of_components E o M (componentExact E o M) n x hx

include o in
lemma full_exists_primitive (n : ℕ) (x : CechAllDegrees.Cochain E Finset.univ M (n + 1))
    (hx : CechAllDegrees.differential E Finset.univ M (n + 1) x = 0) :
    ∃ u, CechAllDegrees.differential E Finset.univ M n u = x :=
  full_exists_primitive_of_components E o M (componentExact E o M) n x hx

include o in
theorem full_cohomology_eq_zero (p : ℕ) (α : CechAllDegrees.Cohomology E Finset.univ M p) :
    α = 0 := by
  induction α using Submodule.Quotient.induction_on with
  | H c =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    obtain ⟨u, hu⟩ := full_exists_primitive E o M p c.val c.property
    exact ⟨u, Subtype.ext hu⟩

include o in
theorem full_cohomology_subsingleton (p : ℕ) :
    Subsingleton (CechAllDegrees.Cohomology E Finset.univ M p) :=
  ⟨fun a b => (full_cohomology_eq_zero E o M p a).trans
    (full_cohomology_eq_zero E o M p b).symm⟩

end Linear
end FullSupportAcyclicity
end WeightedObstructionNorms
