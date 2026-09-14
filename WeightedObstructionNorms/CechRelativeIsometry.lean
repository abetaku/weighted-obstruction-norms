import WeightedObstructionNorms.CechRelative

noncomputable section
namespace WeightedObstructionNorms

/-- A type copy carrying the norm transported by a linear equivalence. -/
def TransportedNorm {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (_e : X ≃ₗ[ℝ] Y) := X

namespace TransportedNorm
variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (e : X ≃ₗ[ℝ] Y)
instance : AddCommGroup (TransportedNorm e) := inferInstanceAs (AddCommGroup X)
instance : Module ℝ (TransportedNorm e) := inferInstanceAs (Module ℝ X)
instance : NormedAddCommGroup (TransportedNorm e) := NormedAddCommGroup.induced _ Y e e.injective
instance : NormedSpace ℝ (TransportedNorm e) := NormedSpace.induced ℝ _ Y e

def isometry : TransportedNorm e ≃ₗᵢ[ℝ] Y where
  toLinearEquiv := e
  norm_map' _ := rfl

lemma norm_eq (x : TransportedNorm e) : ‖x‖ = ‖e x‖ := rfl
end TransportedNorm

namespace CechRelativeIsometry
open FiniteObservations CechAllDegrees CechRelative
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [LinearOrder K]
    (E : I → Type*) [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (S : Finset (State E)) (M : K → Finset I) (o : State E)
    (q : State E → ℝ) (hq : ∀ z, 0 < q z)

def connecting (n : ℕ) : (predecessor E S M o n).Cohomology ≃ₗ[ℝ]
    CechObstruction.Normed E S M o q hq (n + 1) := connectingEquiv E S M o n

abbrev RelativeNormed (n : ℕ) := TransportedNorm (connecting E S M o q hq n)

def connectingIsometry (n : ℕ) : RelativeNormed E S M o q hq n ≃ₗᵢ[ℝ]
    CechObstruction.Normed E S M o q hq (n + 1) := TransportedNorm.isometry _

/-- The transported norm equals the independently defined relative quotient norm. -/
theorem relative_norm_eq (n : ℕ) (β : RelativeNormed E S M o q hq n) :
    ‖β‖ = (predecessor E S M o n).relativeValue (CechObstruction.newWeight E S M q (n + 1)) β :=
  connecting_preserves_norm E S M o q n β

def connectingZero :
    ((predecessorZero E S M o).Cohomology ⧸ LinearMap.ker (predecessorZero E S M o).connecting) ≃ₗ[ℝ]
      CechObstruction.Normed E S M o q hq 0 := quotientConnectingEquivZero E S M o

abbrev QuotientNormedZero := TransportedNorm (connectingZero E S M o q hq)

def quotientConnectingIsometryZero : QuotientNormedZero E S M o q hq ≃ₗᵢ[ℝ]
    CechObstruction.Normed E S M o q hq 0 := TransportedNorm.isometry _

/-- In degree zero the extra quotient carries precisely the original quotient value. -/
theorem quotient_norm_eq_zero (γ : QuotientNormedZero E S M o q hq) :
    ‖γ‖ = (predecessorZero E S M o).quotientValue (CechObstruction.newWeight E S M q 0) γ :=
  quotientConnecting_preserves_norm_zero E S M o q γ

end CechRelativeIsometry
end WeightedObstructionNorms
