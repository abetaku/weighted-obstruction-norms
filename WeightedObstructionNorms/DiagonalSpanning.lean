import WeightedObstructionNorms.DiagonalNorm
import WeightedObstructionNorms.CechAugmentationExtension

noncomputable section
namespace WeightedObstructionNorms
namespace DiagonalSpanning
open FiniteObservations BinaryMarginals DiagonalSetup CechAllDegrees CechLowComparison
open DiagonalCoordinates DiagonalCocycle CechAugmentationExtension

lemma globalExtend_values (r : {z : State E // z ∈ S} → ℝ) (b : Bit × Bit) :
    globalExtend E S Finset.univ (Finset.subset_univ S) r (globalEquiv.symm b) =
      if b.1 = b.2 then r (supportedGlobalEquiv.symm b.1) else 0 := by
  change Marginal.push _ r _ = _
  rw [push_reindex supportedGlobalEquiv]
  have he (a : Bit) : globalInclude E S Finset.univ (Finset.subset_univ S) (supportedGlobalEquiv.symm a) =
      globalEquiv.symm (a,a) := by apply globalEquiv.injective; rfl
  simp only [Marginal.push,Function.comp_apply,he,globalEquiv.symm.injective.eq_iff,Fin.sum_univ_two]
  rcases b with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> simp [Prod.ext_iff]

def correction (u : Global) (z : {z : State E // z ∈ S}) : ℝ :=
  if supportedGlobalEquiv z = 1 then (encode u).pp + (encode u).mp
    else (encode u).pm + (encode u).mm

def coefficient (u : Global) : ℝ := (encode u).pm - (encode u).mp

lemma differential_correction (u : Global) :
    differential E Finset.univ M 0
      (augmentationEquiv E Finset.univ M (globalExtend E S Finset.univ (Finset.subset_univ S) (correction u))) =
    differential E Finset.univ M 0 (augmentationEquiv E Finset.univ M u) -
      coefficient u • differential E Finset.univ M 0 witness := by
  apply (degreeZero E Finset.univ M).injective
  simp only [map_sub,map_smul]
  change degreeZero E Finset.univ M (differential E Finset.univ M 0
    (augmentationEquiv E Finset.univ M _)) =
    degreeZero E Finset.univ M (differential E Finset.univ M 0 (augmentationEquiv E Finset.univ M u)) -
      coefficient u • degreeZero E Finset.univ M (differential E Finset.univ M 0
        (augmentationEquiv E Finset.univ M (decode primitiveMeasure)))
  simp only [CechLowComparison.augmentation]
  apply eval_injective
  funext i a
  change eval (CechLowDegrees.augmentation E Finset.univ M _) i a =
    eval (CechLowDegrees.augmentation E Finset.univ M u) i a -
      coefficient u * eval (CechLowDegrees.augmentation E Finset.univ M (decode primitiveMeasure)) i a
  fin_cases i
  · refine (augmentation_first (globalExtend E S Finset.univ (Finset.subset_univ S) (correction u)) a).trans ?_
    have hr := congrArg₂ (fun v w : ℝ => v - coefficient u * w)
      (augmentation_first u a) (augmentation_first (decode primitiveMeasure) a)
    apply Eq.trans ?_ hr.symm
    fin_cases a <;> simp [globalExtend_values,correction,coefficient,primitiveMeasure,encode] <;> ring
  · refine (augmentation_second (globalExtend E S Finset.univ (Finset.subset_univ S) (correction u)) a).trans ?_
    have hr := congrArg₂ (fun v w : ℝ => v - coefficient u * w)
      (augmentation_second u a) (augmentation_second (decode primitiveMeasure) a)
    apply Eq.trans ?_ hr.symm
    fin_cases a <;> simp [globalExtend_values,correction,coefficient,primitiveMeasure,encode] <;> ring

lemma supported_boundary (x : LinearMap.ker (differential E S M 1)) :
    ∃ a : ℝ, ∃ r : {z : State E // z ∈ S} → ℝ,
      differential E S M 0 (augmentationEquiv E S M r) = x.val - a • c := by
  have hc : differential E Finset.univ M 1 (extension E S M (Finset.subset_univ S) 1 x.val) = 0 := by
    rw [extension_differential,x.property,map_zero]
  obtain ⟨v,hv⟩ := FullSupportAcyclicity.full_exists_primitive E (diagonal 0) M 0 _ hc
  obtain ⟨u,rfl⟩ := (augmentationEquiv E Finset.univ M).surjective v
  refine ⟨coefficient u, correction u, ?_⟩
  apply extension_injective E S M (Finset.subset_univ S) 1
  rw [← extension_differential, extension_augmentation, map_sub, map_smul]
  rw [differential_correction, hv, extension_c]

lemma class_spanning (α : Cohomology E S M 0) : ∃ a : ℝ, α = a • obstructionClass := by
  induction α using Submodule.Quotient.induction_on with
  | H x =>
    obtain ⟨a,r,hr⟩ := supported_boundary x
    refine ⟨a, ?_⟩
    apply sub_eq_zero.mp
    change (LinearMap.range (boundaries E S M 0)).mkQ x -
      a • (LinearMap.range (boundaries E S M 0)).mkQ cycle = 0
    rw [← map_smul, ← map_sub]
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact ⟨augmentationEquiv E S M r, Subtype.ext hr⟩

def generatorEquiv : ℝ ≃ₗ[ℝ] Cohomology E S M 0 :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℝ _ obstructionClass)
    ⟨smul_left_injective ℝ DiagonalNorm.obstruction_nonzero,
      fun α => by obtain ⟨a,ha⟩ := class_spanning α; exact ⟨a,ha.symm⟩⟩

lemma generatorEquiv_apply (a : ℝ) : generatorEquiv a = a • obstructionClass := rfl
lemma cohomology_dimension : Module.finrank ℝ (Cohomology E S M 0) = 1 := by
  rw [← generatorEquiv.finrank_eq]
  exact Module.finrank_self ℝ
lemma norm_coordinate (α : Cohomology E S M 0) :
    CechObstruction.norm E S M (diagonal 0) q₁ 0 α = 2 * |generatorEquiv.symm α| := by
  have h := DiagonalNorm.norm_multiple (generatorEquiv.symm α)
  change CechObstruction.norm E S M (diagonal 0) q₁ 0 (generatorEquiv (generatorEquiv.symm α)) = _ at h
  simpa only [LinearEquiv.apply_symm_apply] using h
lemma unit_ball (α : Cohomology E S M 0) :
    CechObstruction.norm E S M (diagonal 0) q₁ 0 α ≤ 1 ↔
      ∃ a : ℝ, |a| ≤ 1/2 ∧ α = a • obstructionClass := by
  constructor
  · intro h
    refine ⟨generatorEquiv.symm α, ?_, (generatorEquiv.apply_symm_apply α).symm⟩
    rw [norm_coordinate] at h
    linarith
  · rintro ⟨a,ha,rfl⟩
    exact (DiagonalNorm.unit_ball_multiple a).2 ha

end DiagonalSpanning
end WeightedObstructionNorms
