import WeightedObstructionNorms.TriangleCoordinates

noncomputable section
set_option maxHeartbeats 300000
namespace WeightedObstructionNorms
namespace TriangleCocycle
open FiniteObservations BinaryMarginals TriangleSetup CechAllDegrees CechSplitting
open CechLowComparison TriangleCoordinates

lemma singleton_support (i : Fin 3) : projected E S {i} = projected E Finset.univ {i} := by
  ext x
  constructor
  · intro hx
    obtain ⟨z,hz,rfl⟩ := (projected_mem E S {i} x).1 hx
    exact (projected_mem E Finset.univ {i} _).2 ⟨z, Finset.mem_univ _, rfl⟩
  · intro _
    apply (projected_mem E S {i} x).2
    refine ⟨diagonal (x ⟨i, by simp⟩), Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    funext a
    have ha : a = ⟨i, by simp⟩ := Subtype.ext (Finset.mem_singleton.mp a.property)
    subst a
    rfl

lemma full_at_two (t : Tuple (K := Fin 3) 2) :
    projected E S (observation M t) = projected E Finset.univ (observation M t) := by
  obtain ⟨p,rfl⟩ := (twoEquiv (K := Fin 3)).surjective t
  obtain ⟨k,rfl⟩ := edge_surjective p
  rw [show twoEquiv (edge k) = twoTuple (edge k) from rfl, two_observation, edge_observation]
  exact singleton_support (vertex k)

lemma extension_takeOld (x : Cochain E Finset.univ M 2) :
    extension E S M (Finset.subset_univ S) 2 (takeOld E S M 2 x) = x := by
  funext t z
  have hz : z.val ∈ projected E S (observation M t) := by rw [full_at_two]; exact z.property
  let w : SupportState E S (observation M t) := ⟨z.val,hz⟩
  have he : supportInclude E (Finset.subset_univ S) _ w = z := Subtype.ext rfl
  change Marginal.push (supportInclude E (Finset.subset_univ S) _) (takeOld E S M 2 x t) z = x t z
  rw [← he, Marginal.push_injective_apply _ (supportInclude_injective E (Finset.subset_univ S) _)]
  rfl

def witness : Cochain E Finset.univ M 1 :=
  (degreeZero E Finset.univ M).symm (decode (BinaryExamples.triangleFromMoments 0 0 0))
def c : Cochain E S M 2 := takeOld E S M 2 (differential E Finset.univ M 1 witness)
lemma extension_c : extension E S M (Finset.subset_univ S) 2 c =
    differential E Finset.univ M 1 witness := extension_takeOld _
lemma c_closed : differential E S M 2 c = 0 := by
  apply extension_injective E S M (Finset.subset_univ S) 3
  rw [map_zero, ← extension_differential, extension_c, differential_squared]

def cycle : LinearMap.ker (differential E S M 2) := ⟨c,c_closed⟩
def obstructionClass : Cohomology E S M 1 := Submodule.Quotient.mk cycle

lemma eval_extension_c (k : Fin 3) (a : Bit) :
    eval (degreeOne E Finset.univ M (extension E S M (Finset.subset_univ S) 2 c)) k a =
      if k = 0 then if a = 1 then 1 else -1 else 0 := by
  rw [extension_c, differential_zero]
  simp only [witness, LinearEquiv.apply_symm_apply]
  fin_cases k
  · refine (eval_d0_zero (decode (BinaryExamples.triangleFromMoments 0 0 0)) a).trans ?_
    fin_cases a <;> norm_num [
      BinaryExamples.triangleFromMoments, BinaryExamples.fromMoments]
  · refine (eval_d0_one (decode (BinaryExamples.triangleFromMoments 0 0 0)) a).trans ?_
    fin_cases a <;> norm_num [
      BinaryExamples.triangleFromMoments, BinaryExamples.fromMoments]
  · refine (eval_d0_two (decode (BinaryExamples.triangleFromMoments 0 0 0)) a).trans ?_
    fin_cases a <;> norm_num [
      BinaryExamples.triangleFromMoments, BinaryExamples.fromMoments]

lemma six_values (f g : Fin 3 → Bit → ℝ) : f = g ↔
    f 0 1 = g 0 1 ∧ f 0 0 = g 0 0 ∧ f 1 1 = g 1 1 ∧ f 1 0 = g 1 0 ∧
      f 2 1 = g 2 1 ∧ f 2 0 = g 2 0 := by
  constructor
  · intro h; subst g; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  · rintro ⟨h01,h00,h11,h10,h21,h20⟩
    funext k a
    fin_cases k <;> fin_cases a
    · exact h00
    · exact h01
    · exact h10
    · exact h11
    · exact h20
    · exact h21


def values (k : Fin 3) (a : Bit) : ℝ := if k = 0 then if a = 1 then 1 else -1 else 0

lemma low_feasible_iff (y : CechLowDegrees.C0 E Finset.univ M) :
    eval (CechLowDegrees.d0 E Finset.univ M y) = values ↔ BinaryExamples.TriangleFeasible (encode y) := by
  rw [six_values]
  rw [eval_d0_zero y 1, eval_d0_zero y 0, eval_d0_one y 1, eval_d0_one y 0,
    eval_d0_two y 1, eval_d0_two y 0]
  simp only [values, if_pos (show (0 : Fin 3) = 0 from rfl),
    if_neg (show (1 : Fin 3) ≠ 0 by decide), if_neg (show (2 : Fin 3) ≠ 0 by decide),
    if_pos (show (1 : Bit) = 1 from rfl), if_neg (show (0 : Bit) ≠ 1 by decide),
    ite_true, ite_false, BinaryExamples.TriangleFeasible, encode, BinaryPairCoordinates.encode]
  constructor <;> rintro ⟨h1,h2,h3,h4,h5,h6⟩ <;>
    refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith only [h1,h2,h3,h4,h5,h6]

lemma feasible_iff (x : Cochain E Finset.univ M 1) :
    differential E Finset.univ M 1 x = extension E S M (Finset.subset_univ S) 2 c ↔
      BinaryExamples.TriangleFeasible (encode (degreeZero E Finset.univ M x)) := by
  have hi : (differential E Finset.univ M 1 x = extension E S M (Finset.subset_univ S) 2 c) ↔
      eval (degreeOne E Finset.univ M (differential E Finset.univ M 1 x)) =
      eval (degreeOne E Finset.univ M (extension E S M (Finset.subset_univ S) 2 c)) :=
    ⟨fun h => congrArg (fun y => eval (degreeOne E Finset.univ M y)) h,
      fun h => (degreeOne E Finset.univ M).injective (eval_injective h)⟩
  have he : eval (degreeOne E Finset.univ M (extension E S M (Finset.subset_univ S) 2 c)) = values :=
    funext (fun k => funext (eval_extension_c k))
  apply hi.trans
  rw [differential_zero, he]
  exact low_feasible_iff _

end TriangleCocycle
end WeightedObstructionNorms
