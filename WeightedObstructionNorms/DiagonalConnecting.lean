import WeightedObstructionNorms.DiagonalSpanning

noncomputable section
set_option maxHeartbeats 1000000
namespace WeightedObstructionNorms
namespace DiagonalConnecting
open FiniteObservations BinaryMarginals DiagonalSetup CechAllDegrees CechSplitting
open DiagonalCoordinates DiagonalCocycle DiagonalSpanning CechAugmentationExtension
abbrev W := window E S M (diagonal 0) 0

lemma takeNew_one_zero (x : Cochain E Finset.univ M 1) : takeNew E S M 1 x = 0 := by
  funext j
  exact False.elim (j.2.property ((Finset.ext_iff.mp (full_at_one j.1) j.2.val.val).2 j.2.val.property))

lemma primitive_closed (u : Global) : differential E S M 1
    (takeOld E S M 1 (differential E Finset.univ M 0 (augmentationEquiv E Finset.univ M u))) = 0 := by
  apply extension_injective E S M (Finset.subset_univ S) 2
  rw [map_zero, ← extension_differential, extension_takeOld, differential_squared]
def primitiveCycle (u : Global) : LinearMap.ker (differential E S M 1) := ⟨_,primitive_closed u⟩
def relativeCycle (u : Global) : LinearMap.ker W.relativeD :=
  ⟨takeNew E S M 0 (augmentationEquiv E Finset.univ M u),by
    exact takeNew_one_zero (differential E Finset.univ M 0
      (putNew E S M 0 (takeNew E S M 0 (augmentationEquiv E Finset.univ M u))))⟩

lemma primitive_boundary (u : Global) :
    differential E S M 0 (augmentationEquiv E S M (correction u)) =
      (primitiveCycle u).val - coefficient u • c := by
  apply extension_injective E S M (Finset.subset_univ S) 1
  rw [← extension_differential, extension_augmentation, map_sub, map_smul, extension_c]
  change _ = extension E S M (Finset.subset_univ S) 1 (takeOld E S M 1 _) - _
  rw [extension_takeOld, differential_correction]

lemma primitive_class (u : Global) :
    (Submodule.Quotient.mk (primitiveCycle u) : Cohomology E S M 0) = coefficient u • obstructionClass := by
  apply sub_eq_zero.mp
  change (LinearMap.range (boundaries E S M 0)).mkQ (primitiveCycle u) -
    coefficient u • (LinearMap.range (boundaries E S M 0)).mkQ cycle = 0
  rw [← map_smul, ← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact ⟨augmentationEquiv E S M (correction u),Subtype.ext (primitive_boundary u)⟩

lemma connecting_primitive (u : Global) :
    cohomologyEquiv E S M (diagonal 0) 0 (W.connecting (relativeCycle u)) =
      (Submodule.Quotient.mk (primitiveCycle u) : Cohomology E S M 0) := by
  have hh : W.connecting (relativeCycle u) = W.classOf ((cycleEquiv E S M (diagonal 0) 0).symm (primitiveCycle u)) := by
    apply (W.connecting_eq_iff _ _).2
    refine ⟨(pack E S M 0).symm (takeOld E S M 0 (augmentationEquiv E Finset.univ M u)), ?_⟩
    have hd := congrArg (pack E S M 1).symm
      (differential_takeOld E S M 0 (augmentationEquiv E Finset.univ M u))
    rw [map_add] at hd
    exact hd.symm
  rw [hh]
  rfl

def offMeasure (s t : ℝ) : BinaryExamples.PairMeasure := ⟨0,s,t,0⟩
def coordinates (s t : ℝ) : LinearMap.ker W.relativeD := relativeCycle (decode (offMeasure s t))
def connecting (v : LinearMap.ker W.relativeD) : Cohomology E S M 0 :=
  cohomologyEquiv E S M (diagonal 0) 0 (W.connecting v)

/-- The connecting homomorphism on the actual relative Cech coordinates (+-,-+). -/
theorem connecting_coordinates (s t : ℝ) : connecting (coordinates s t) = (s-t) • obstructionClass := by
  rw [connecting,coordinates,connecting_primitive,primitive_class]
  simp only [coefficient,encode_decode,offMeasure]

lemma connecting_kernel_coordinates (s t : ℝ) : connecting (coordinates s t) = 0 ↔ s = t := by
  rw [connecting_coordinates, smul_eq_zero]
  simp only [DiagonalNorm.obstruction_nonzero, or_false, sub_eq_zero]

lemma takeNew_augmentation_eq (u v : Global) (h : ∀ z, z.val ∉ S → u z = v z) :
    takeNew E S M 0 (augmentationEquiv E Finset.univ M u) =
      takeNew E S M 0 (augmentationEquiv E Finset.univ M v) := by
  funext j
  obtain ⟨z,hz⟩ := globalProject_surjective E Finset.univ M j.1 j.2.val
  have hn : z.val ∉ S := by
    intro hs
    apply j.2.property
    have he : project E (observation M j.1) z.val = j.2.val.val := congrArg Subtype.val hz
    exact (projected_mem E S _ _).2 ⟨z.val,hs,he⟩
  change augmentationEquiv E Finset.univ M u j.1 j.2.val = augmentationEquiv E Finset.univ M v j.1 j.2.val
  rw [← hz]
  change u ((globalPointEquiv E Finset.univ M j.1).symm (globalPointEquiv E Finset.univ M j.1 z)) =
    v ((globalPointEquiv E Finset.univ M j.1).symm (globalPointEquiv E Finset.univ M j.1 z))
  simpa only [Equiv.symm_apply_apply] using h z hn

lemma relativeCycle_coordinates (u : Global) : relativeCycle u = coordinates (encode u).pm (encode u).mp := by
  apply Subtype.ext
  apply takeNew_augmentation_eq
  intro z hz
  obtain ⟨⟨a,b⟩,rfl⟩ := globalEquiv.symm.surjective z
  have hn : a ≠ b := by
    intro hab
    apply hz
    apply (mem_support _).2
    exact hab
  fin_cases a <;> fin_cases b <;> try contradiction
  all_goals simp [encode,offMeasure]

lemma coordinates_surjective (v : LinearMap.ker W.relativeD) : ∃ s t, coordinates s t = v := by
  let u := (augmentationEquiv E Finset.univ M).symm (putNew E S M 0 v.val)
  have he : relativeCycle u = v := by
    apply Subtype.ext
    change takeNew E S M 0 (augmentationEquiv E Finset.univ M u) = v.val
    rw [show augmentationEquiv E Finset.univ M u = putNew E S M 0 v.val from LinearEquiv.apply_symm_apply _ _, takeNew_putNew]
  exact ⟨(encode u).pm,(encode u).mp,(relativeCycle_coordinates u).symm.trans he⟩

/-- Every relative cocycle in the connecting kernel is on the diagonal s=t. -/
theorem connecting_kernel (v : LinearMap.ker W.relativeD) :
    connecting v = 0 ↔ ∃ t, v = coordinates t t := by
  obtain ⟨s,t,rfl⟩ := coordinates_surjective v
  constructor
  · intro h
    have he := (connecting_kernel_coordinates s t).1 h
    subst s
    exact ⟨t,rfl⟩
  · rintro ⟨a,ha⟩
    rw [ha]
    exact (connecting_kernel_coordinates a a).2 rfl

end DiagonalConnecting
end WeightedObstructionNorms
