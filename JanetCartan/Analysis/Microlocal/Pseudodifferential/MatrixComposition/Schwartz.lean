module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.Basic

/-!
# Vector Schwartz coordinates

For `app:ch_regular_base:thm:actual-calculus`, coordinatewise matrix operators
act on genuine finite-dimensional vector-valued Schwartz data. Fourier
transformation of the coordinates agrees with the vector Bochner transform.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace SchwartzMap
namespace JanetCartan.Pseudodifferential
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {K : Type} [Fintype K]

/-- `app:ch_regular_base:thm:actual-calculus`: scalar Schwartz coordinates
of finite-dimensional vector data. -/
def matrixSchwartzCoordinates (u : 𝓢(V, K → ℂ)) (k : K) : 𝓢(V, ℂ) :=
  u.postcompCLM (ContinuousLinearMap.proj (R := ℂ) k)

/-- `app:ch_regular_base:thm:actual-calculus`: coordinatewise Fourier
transformation is the actual vector-valued Fourier integral. -/
theorem fourier_matrixSchwartzCoordinates (u : 𝓢(V, K → ℂ)) (η : V) (k : K) :
    (𝓕 (matrixSchwartzCoordinates u k) : 𝓢(V, ℂ)) η = (𝓕 u : 𝓢(V, K → ℂ)) η k := by
  change 𝓕 (fun y ↦ u y k) η = (𝓕 (u : V → K → ℂ) η) k
  simp only [Real.fourier_eq]
  symm
  apply eval_integral
  intro k
  exact (Real.fourierIntegral_convergent_iff η).2 (u.integrable.eval k)
end JanetCartan.Pseudodifferential
