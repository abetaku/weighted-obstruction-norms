import WeightedObstructionNorms.DiagonalConnecting

noncomputable section
namespace WeightedObstructionNorms
namespace DiagonalRelativeCoordinates
open FiniteObservations BinaryMarginals DiagonalSetup CechAllDegrees CechSplitting
open DiagonalCoordinates DiagonalCocycle DiagonalConnecting CechLowComparison

def newGlobalPoint (z : {z : State E // z ∈ (Finset.univ : Finset (State E))}) (hz : z.val ∉ S) :
    NewCoordinate E S M 0 :=
  ⟨emptyTuple,⟨globalProject E Finset.univ M emptyTuple z,by
    intro h
    obtain ⟨w,hw,he⟩ := (projected_mem E S _ _).1 h
    have hh : (⟨w,Finset.mem_univ _⟩ : {z : State E // z ∈ (Finset.univ : Finset (State E))}) = z :=
      globalProject_zero_injective E Finset.univ M emptyTuple (Subtype.ext he)
    exact hz (congrArg Subtype.val hh ▸ hw)⟩⟩

lemma newGlobalPoint_eval (u : Global) (z : {z : State E // z ∈ (Finset.univ : Finset (State E))}) (hz : z.val ∉ S) :
    takeNew E S M 0 (augmentationEquiv E Finset.univ M u) (newGlobalPoint z hz) = u z := by
  exact congrArg u ((globalPointEquiv E Finset.univ M emptyTuple).symm_apply_apply z)

lemma off_not_supported (a b : Bit) (hab : a ≠ b) : (globalEquiv.symm (a,b)).val ∉ S := by
  intro h
  exact hab ((mem_support _).1 h)

lemma coordinates_first (s t : ℝ) : (coordinates s t).val
    (newGlobalPoint (globalEquiv.symm (1,0)) (off_not_supported 1 0 (by decide))) = s := by
  change takeNew E S M 0 (augmentationEquiv E Finset.univ M (decode (offMeasure s t))) _ = s
  rw [newGlobalPoint_eval]
  simp [offMeasure]
lemma coordinates_second (s t : ℝ) : (coordinates s t).val
    (newGlobalPoint (globalEquiv.symm (0,1)) (off_not_supported 0 1 (by decide))) = t := by
  change takeNew E S M 0 (augmentationEquiv E Finset.univ M (decode (offMeasure s t))) _ = t
  rw [newGlobalPoint_eval]
  simp [offMeasure]

lemma coordinates_injective {s t s' t' : ℝ} (h : coordinates s t = coordinates s' t') : s = s' ∧ t = t' := by
  constructor
  · have hh := congrArg (fun v : LinearMap.ker W.relativeD => v.val
      (newGlobalPoint (globalEquiv.symm (1,0)) (off_not_supported 1 0 (by decide)))) h
    simpa only [coordinates_first] using hh
  · have hh := congrArg (fun v : LinearMap.ker W.relativeD => v.val
      (newGlobalPoint (globalEquiv.symm (0,1)) (off_not_supported 0 1 (by decide)))) h
    simpa only [coordinates_second] using hh

lemma reference_weight (j : NewCoordinate E S M 0) : CechObstruction.newWeight E S M q₁ 0 j = 1/4 := by
  obtain ⟨z,hz⟩ := globalProject_surjective E Finset.univ M j.1 j.2.val
  have he := congrArg Subtype.val hz
  change weight E q₁ (observation M j.1) j.2.val.val = 1/4
  rw [← he]
  exact CechAugmentationNorm.global_weight E M q₁ j.1 z.val

def zeroMarginalMeasure (t : ℝ) : BinaryExamples.PairMeasure := ⟨-t,t,t,-t⟩
lemma zero_marginals (t : ℝ) :
    differential E Finset.univ M 0 (augmentationEquiv E Finset.univ M (decode (zeroMarginalMeasure t))) = 0 := by
  apply (degreeZero E Finset.univ M).injective
  rw [map_zero,CechLowComparison.augmentation]
  apply DiagonalCoordinates.eval_injective
  funext i a
  change DiagonalCoordinates.eval (CechLowDegrees.augmentation E Finset.univ M (decode (zeroMarginalMeasure t))) i a = 0
  fin_cases i
  · refine (augmentation_first (decode (zeroMarginalMeasure t)) a).trans ?_
    fin_cases a <;> simp [zeroMarginalMeasure]
  · refine (augmentation_second (decode (zeroMarginalMeasure t)) a).trans ?_
    fin_cases a <;> simp [zeroMarginalMeasure]

lemma kernel_witness (t : ℝ) : relativeCycle (decode (zeroMarginalMeasure t)) = coordinates t t := by
  have h := relativeCycle_coordinates (decode (zeroMarginalMeasure t))
  simpa only [encode_decode,zeroMarginalMeasure] using h

lemma projected_subsingleton (A : Finset (Fin 2)) (i : Fin 2) (hA : A ⊆ {i}) :
    projected E S A = projected E Finset.univ A := by
  ext x
  constructor
  · intro hx
    obtain ⟨z,hz,rfl⟩ := (projected_mem E S A x).1 hx
    exact (projected_mem E Finset.univ A _).2 ⟨z,Finset.mem_univ _,rfl⟩
  · intro _
    classical
    by_cases hne : A.Nonempty
    · obtain ⟨a,ha⟩ := hne
      refine (projected_mem E S A x).2 ⟨diagonal (x ⟨a,ha⟩),Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,?_⟩
      funext b
      have hb : b = ⟨a,ha⟩ := Subtype.ext ((Finset.mem_singleton.mp (hA b.property)).trans
        (Finset.mem_singleton.mp (hA ha)).symm)
      subst b
      rfl
    · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst A
      refine (projected_mem E S ∅ x).2 ⟨diagonal 0,Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩,?_⟩
      funext a
      exact False.elim (Finset.not_mem_empty _ a.property)

/-- The actual relative complex is concentrated in augmented degree minus one. -/
lemma no_positive_relative_coordinates (n : ℕ) : IsEmpty (NewCoordinate E S M (n+1)) := by
  refine ⟨fun j => ?_⟩
  have hA : observation M j.1 ⊆ {j.1 0} := by
    intro a ha
    exact (mem_observation M j.1 a).1 ha 0
  exact j.2.property ((Finset.ext_iff.mp (projected_subsingleton _ _ hA) j.2.val.val).2 j.2.val.property)

abbrev P := CechRelative.predecessorZero E S M (diagonal 0)

lemma cohomology_connecting_coordinates (s t : ℝ) :
    cohomologyEquiv E S M (diagonal 0) 0 (P.connecting (P.classOf (coordinates s t))) =
      (s-t) • obstructionClass := connecting_coordinates s t

lemma cohomology_connecting_kernel (β : P.Cohomology) :
    P.connecting β = 0 ↔ ∃ t, β = P.classOf (coordinates t t) := by
  obtain ⟨v,rfl⟩ := P.class_surjective β
  constructor
  · intro h
    have hc : DiagonalConnecting.connecting v = 0 := by
      change cohomologyEquiv E S M (diagonal 0) 0 (W.connecting v) = 0
      have hh : W.connecting v = 0 := h
      rw [hh,map_zero]
    obtain ⟨t,ht⟩ := (DiagonalConnecting.connecting_kernel v).1 hc
    exact ⟨t,congrArg P.classOf ht⟩
  · rintro ⟨t,ht⟩
    rw [ht]
    apply (cohomologyEquiv E S M (diagonal 0) 0).injective
    rw [map_zero,cohomology_connecting_coordinates,sub_self,zero_smul]

end DiagonalRelativeCoordinates
end WeightedObstructionNorms
