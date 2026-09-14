import WeightedObstructionNorms.CechLowComparison
import WeightedObstructionNorms.FullSupportAcyclicity
import WeightedObstructionNorms.BinaryExamples

noncomputable section
open scoped BigOperators
namespace WeightedObstructionNorms
namespace BinaryMarginals
open FiniteObservations
abbrev Bit := Fin 2
abbrev Outcomes (I : Type*) : I → Type := fun _ => Bit
variable {I : Type*} [Fintype I] [DecidableEq I]

def diagonal (b : Bit) : State (Outcomes I) := fun _ => b
def support : Finset (State (Outcomes I)) := Finset.univ.image diagonal

def supportConst (A : Finset I) (b : Bit) : SupportState (Outcomes I) support A :=
  ⟨fun _ => b, (projected_mem _ _ _ _).2
    ⟨diagonal b, Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩, rfl⟩⟩

def supportEquiv (A : Finset I) (a₀ : A) : SupportState (Outcomes I) support A ≃ Bit where
  toFun z := z.val a₀
  invFun := supportConst A
  left_inv x := by
    obtain ⟨z, hz, he⟩ := (projected_mem (Outcomes I) support A x.val).1 x.property
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hz
    apply Subtype.ext
    funext a
    exact (congrFun he a₀).symm.trans (congrFun he a)
  right_inv _ := rfl

lemma supportRestrict_const {A B : Finset I} (h : A ⊆ B) (b : Bit) :
    supportRestrict (Outcomes I) support h (supportConst B b) = supportConst A b := rfl

lemma marginal_supported {A B : Finset I} (h : A ⊆ B) (a₀ : A) (b₀ : B)
    (x : SupportState (Outcomes I) support B → ℝ) (b : Bit) :
    marginal (Outcomes I) support h x (supportConst A b) = x (supportConst B b) := by
  have hi : Function.Injective (supportRestrict (Outcomes I) support h) := by
    intro z w he
    obtain ⟨c, rfl⟩ := (supportEquiv B b₀).symm.surjective z
    obtain ⟨d, rfl⟩ := (supportEquiv B b₀).symm.surjective w
    have hh : c = d := congrArg (fun z : SupportState (Outcomes I) support A => z.val a₀) he
    subst d
    rfl
  exact Marginal.push_injective_apply _ hi x (supportConst B b)

def fullEquiv (A : Finset I) : SupportState (Outcomes I) Finset.univ A ≃ LocalState (Outcomes I) A where
  toFun := Subtype.val
  invFun := FullSupportAcyclicity.fullPoint (Outcomes I) (diagonal 0) A
  left_inv z := Subtype.ext rfl
  right_inv _ := rfl

def singletonLocalEquiv (i : I) : LocalState (Outcomes I) {i} ≃ Bit where
  toFun z := z ⟨i, Finset.mem_singleton_self i⟩
  invFun b := fun _ => b
  left_inv z := by
    funext a
    have ha : a = ⟨i, Finset.mem_singleton_self i⟩ := Subtype.ext (Finset.mem_singleton.mp a.property)
    rw [ha]
  right_inv _ := rfl

def pairLocalEquiv (i j : I) (hij : i ≠ j) : LocalState (Outcomes I) {i, j} ≃ Bit × Bit where
  toFun z := (z ⟨i, by simp⟩, z ⟨j, by simp⟩)
  invFun b := fun a => if a.val = i then b.1 else b.2
  left_inv z := by
    funext a
    rcases Finset.mem_insert.mp a.property with ha | ha
    · have he : a = ⟨i, by simp⟩ := Subtype.ext ha
      subst a
      simp
    · have he : a = ⟨j, by simp⟩ := Subtype.ext (Finset.mem_singleton.mp ha)
      subst a
      simp [hij.symm]
  right_inv b := by simp [hij.symm]

def fullSingletonEquiv (i : I) : SupportState (Outcomes I) Finset.univ {i} ≃ Bit :=
  (fullEquiv {i}).trans (singletonLocalEquiv i)
def fullPairEquiv (i j : I) (hij : i ≠ j) : SupportState (Outcomes I) Finset.univ {i, j} ≃ Bit × Bit :=
  (fullEquiv {i, j}).trans (pairLocalEquiv i j hij)

lemma project_pair_eq (i j : I) (hij : i ≠ j) (z : State (Outcomes I)) (b : Bit × Bit) :
    project (Outcomes I) {i, j} z = (pairLocalEquiv i j hij).symm b ↔ (z i, z j) = b := by
  exact (pairLocalEquiv i j hij).apply_eq_iff_eq_symm_apply.symm

lemma push_reindex {A B C : Type*} [Fintype A] [Fintype B] (e : A ≃ B)
    (f : A → C) (x : A → ℝ) (c : C) :
    Marginal.push f x c = Marginal.push (f ∘ e.symm) (x ∘ e.symm) c := by
  classical
  unfold Marginal.push
  exact Fintype.sum_equiv e _ _ (fun a => by simp)

lemma full_pair_first (i j : I) (hij : i ≠ j)
    (x : SupportState (Outcomes I) Finset.univ {i, j} → ℝ) (a : Bit) :
    marginal (Outcomes I) Finset.univ (show {i} ⊆ {i, j} by simp) x ((fullSingletonEquiv i).symm a) =
      x ((fullPairEquiv i j hij).symm (a, 0)) + x ((fullPairEquiv i j hij).symm (a, 1)) := by
  classical
  change Marginal.push _ x _ = _
  rw [push_reindex (fullPairEquiv i j hij)]
  have he (b : Bit × Bit) : supportRestrict (Outcomes I) Finset.univ (show {i} ⊆ {i, j} by simp)
      ((fullPairEquiv i j hij).symm b) = (fullSingletonEquiv i).symm b.1 := by
    apply (fullSingletonEquiv i).injective
    simp [fullSingletonEquiv, fullPairEquiv, fullEquiv, singletonLocalEquiv, pairLocalEquiv, supportRestrict, restrict, FullSupportAcyclicity.fullPoint]
  simp only [Marginal.push, Function.comp_apply, he, (fullSingletonEquiv i).symm.injective.eq_iff, Fintype.sum_prod_type]
  fin_cases a <;> simp [Fin.sum_univ_two]

lemma full_pair_second (i j : I) (hij : i ≠ j)
    (x : SupportState (Outcomes I) Finset.univ {i, j} → ℝ) (a : Bit) :
    marginal (Outcomes I) Finset.univ (show {j} ⊆ {i, j} by simp) x ((fullSingletonEquiv j).symm a) =
      x ((fullPairEquiv i j hij).symm (0, a)) + x ((fullPairEquiv i j hij).symm (1, a)) := by
  classical
  change Marginal.push _ x _ = _
  rw [push_reindex (fullPairEquiv i j hij)]
  have he (b : Bit × Bit) : supportRestrict (Outcomes I) Finset.univ (show {j} ⊆ {i, j} by simp)
      ((fullPairEquiv i j hij).symm b) = (fullSingletonEquiv j).symm b.2 := by
    apply (fullSingletonEquiv j).injective
    simp [fullSingletonEquiv, fullPairEquiv, fullEquiv, singletonLocalEquiv, pairLocalEquiv, supportRestrict, restrict, FullSupportAcyclicity.fullPoint, hij.symm]
  simp only [Marginal.push, Function.comp_apply, he, (fullSingletonEquiv j).symm.injective.eq_iff, Fintype.sum_prod_type]
  fin_cases a <;> simp [Fin.sum_univ_two]

lemma cast_marginal {A B A' : Finset I} (hA : A = A')
    (h : A ⊆ B) (h' : A' ⊆ B) (x : SupportState (Outcomes I) Finset.univ B → ℝ) :
    CechLowComparison.coefficientCongr (Outcomes I) Finset.univ hA
      (marginal (Outcomes I) Finset.univ h x) = marginal (Outcomes I) Finset.univ h' x := by
  subst A'
  rfl

end BinaryMarginals
end WeightedObstructionNorms
