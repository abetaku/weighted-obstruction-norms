import WeightedObstructionNorms.DiagonalSetup

noncomputable section
open scoped BigOperators
namespace WeightedObstructionNorms
namespace DiagonalCoordinates
open FiniteObservations BinaryMarginals DiagonalSetup CechLowDegrees
abbrev Global := {z : State E // z ∈ (Finset.univ : Finset (State E))} → ℝ

def encode (u : Global) : BinaryExamples.PairMeasure :=
  ⟨u (globalEquiv.symm (1,1)),u (globalEquiv.symm (1,0)),
   u (globalEquiv.symm (0,1)),u (globalEquiv.symm (0,0))⟩
def decode (x : BinaryExamples.PairMeasure) (z : {z : State E // z ∈ (Finset.univ : Finset (State E))}) : ℝ :=
  if (globalEquiv z).1 = 1 then if (globalEquiv z).2 = 1 then x.pp else x.pm
    else if (globalEquiv z).2 = 1 then x.mp else x.mm
@[simp] lemma decode_apply (x : BinaryExamples.PairMeasure) (b : Bit × Bit) :
    decode x (globalEquiv.symm b) =
      if b.1 = 1 then if b.2 = 1 then x.pp else x.pm else if b.2 = 1 then x.mp else x.mm := by
  simp only [decode, Equiv.apply_symm_apply]
lemma encode_decode (x : BinaryExamples.PairMeasure) : encode (decode x) = x := by
  cases x; simp [encode]
lemma decode_encode (u : Global) : decode (encode u) = u := by
  funext z
  obtain ⟨⟨a,b⟩,rfl⟩ := globalEquiv.symm.surjective z
  fin_cases a <;> fin_cases b <;> simp [encode]

def eval (x : C0 E Finset.univ M) (i a : Bit) : ℝ := x i ((fullSingletonEquiv i).symm a)
lemma eval_injective : Function.Injective eval := by
  intro x y h
  funext i z
  obtain ⟨a,rfl⟩ := (fullSingletonEquiv i).symm.surjective z
  exact congrFun (congrFun h i) a

lemma augmentation_first (u : Global) (a : Bit) :
    eval (augmentation E Finset.univ M u) 0 a =
      u (globalEquiv.symm (a,0)) + u (globalEquiv.symm (a,1)) := by
  change Marginal.push _ u _ = _
  rw [push_reindex globalEquiv]
  have he (b : Bit × Bit) : CechLowDegrees.globalProject E Finset.univ (M 0) (globalEquiv.symm b) =
      (fullSingletonEquiv 0).symm b.1 := by
    apply (fullSingletonEquiv 0).injective
    rfl
  simp only [Marginal.push, Function.comp_apply, he, (fullSingletonEquiv (0 : Fin 2)).symm.injective.eq_iff,
    Fintype.sum_prod_type]
  fin_cases a <;> simp [Fin.sum_univ_two]

lemma augmentation_second (u : Global) (a : Bit) :
    eval (augmentation E Finset.univ M u) 1 a =
      u (globalEquiv.symm (0,a)) + u (globalEquiv.symm (1,a)) := by
  change Marginal.push _ u _ = _
  rw [push_reindex globalEquiv]
  have he (b : Bit × Bit) : CechLowDegrees.globalProject E Finset.univ (M 1) (globalEquiv.symm b) =
      (fullSingletonEquiv 1).symm b.2 := by
    apply (fullSingletonEquiv 1).injective
    rfl
  simp only [Marginal.push, Function.comp_apply, he, (fullSingletonEquiv (1 : Fin 2)).symm.injective.eq_iff,
    Fintype.sum_prod_type]
  fin_cases a <;> simp [Fin.sum_univ_two]

lemma box_iff (ε L : ℝ) (u : Global) :
    (∀ z, |u z| ≤ L * q ε z.val) ↔ BinaryExamples.PairBox ε L (encode u) := by
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_⟩
    · simpa [encode,q_value,globalEquiv,stateEquiv,mul_div_assoc] using h (globalEquiv.symm (1,1))
    · simpa [encode,q_value,globalEquiv,stateEquiv,mul_div_assoc] using h (globalEquiv.symm (1,0))
    · simpa [encode,q_value,globalEquiv,stateEquiv,mul_div_assoc] using h (globalEquiv.symm (0,1))
    · simpa [encode,q_value,globalEquiv,stateEquiv,mul_div_assoc] using h (globalEquiv.symm (0,0))
  · rintro ⟨hpp,hpm,hmp,hmm⟩ z
    obtain ⟨⟨a,b⟩,rfl⟩ := globalEquiv.symm.surjective z
    fin_cases a <;> fin_cases b
    · simpa [encode,q_value,globalEquiv,stateEquiv,mul_div_assoc] using hmm
    · simpa [encode,q_value,globalEquiv,stateEquiv,mul_div_assoc] using hmp
    · simpa [encode,q_value,globalEquiv,stateEquiv,mul_div_assoc] using hpm
    · simpa [encode,q_value,globalEquiv,stateEquiv,mul_div_assoc] using hpp

end DiagonalCoordinates
end WeightedObstructionNorms
