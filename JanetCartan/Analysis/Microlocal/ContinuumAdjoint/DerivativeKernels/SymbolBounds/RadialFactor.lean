module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Expansion

/-!
# Frequency factors in the actual adjoint recursion

The radial factor in `app:ch_background:eq:bg-T` is untouched by the
initial/carrier trades of `app:ch_background:eq:bg-derivative-trade`.
The normalized amplitude retains its full angular and carrier dependence.
These identities concern the constructed recursion, independently of its
identification with derivatives of the integral.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels

open ContinuumRow NormalComparison

variable {n : ℕ}

/-- Multiply only by a frequency factor, for `app:ch_background:eq:bg-T`.
In particular this does not remove the carrier-dependent angular cutoff. -/
def frequencyScaleAmplitude (w : Euclidean (n - 1) → ℂ) (a : AdjointAmplitude n) :
    AdjointAmplitude n := fun z x η ↦ w η * a z x η

/-- Scale an actual expansion term, preserving its datum derivative word
(`app:ch_background:prop:bg-adjoint`). -/
def frequencyScaleTerm (w : Euclidean (n - 1) → ℂ) (t : AdjointDerivativeTerm n) :
    AdjointDerivativeTerm n := ⟨frequencyScaleAmplitude w t.amplitude, t.dataDerivatives⟩

private theorem fderiv_const_complex_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℂ) (f : E → ℂ) (x h : E) :
    fderiv ℝ (fun y ↦ c * f y) x h = c * fderiv ℝ f x h := by
  have he := congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := f) c) x
  exact congrArg (fun A : E →L[ℝ] ℂ ↦ A h) he

/-- A frequency-only factor passes through the zero branch without any
regularity premise (`app:ch_background:eq:bg-derivative-trade`). -/
theorem zeroBranchAmplitude_frequencyScale
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (d : InitialCarrierDerivative n) (w : Euclidean (n - 1) → ℂ)
    (a : AdjointAmplitude n) :
    zeroBranchAmplitude L V d (frequencyScaleAmplitude w a) =
      frequencyScaleAmplitude w (zeroBranchAmplitude L V d a) := by
  funext z x η
  have hs (b : Euclidean n → Euclidean n) (j : Fin n) :
      (fun y ↦ b y j • (w η * a z y η)) =
        (fun y ↦ w η * (b y j • a z y η)) := by
    funext y
    exact mul_smul_comm _ _ _ |>.symm
  cases d with
  | initial h =>
      simp only [zeroBranchAmplitude, frequencyScaleAmplitude, initialZeroAmplitude,
        hs, partialDeriv, fderiv_const_complex_mul, Finset.mul_sum]
  | carrier h =>
      simp only [zeroBranchAmplitude, frequencyScaleAmplitude, carrierZeroAmplitude,
        transportCoefficient, hs, partialDeriv, fderiv_const_complex_mul,
        Finset.mul_sum, mul_sub]

/-- A frequency-only factor passes through each first branch
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem firstBranchAmplitude_frequencyScale
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (d : InitialCarrierDerivative n) (w : Euclidean (n - 1) → ℂ)
    (a : AdjointAmplitude n) (j : Fin n) :
    firstBranchAmplitude L V d (frequencyScaleAmplitude w a) j =
      frequencyScaleAmplitude w (firstBranchAmplitude L V d a j) := by
  funext z x η
  cases d <;> simp [firstBranchAmplitude, frequencyScaleAmplitude,
    initialFirstAmplitude, carrierFirstAmplitude, mul_left_comm]

/-- Exact one-step scaling of the constructed list, including multiplicities
and datum derivative words (`app:ch_background:prop:bg-adjoint`). -/
theorem differentiateAdjointTerm_frequencyScale
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (d : InitialCarrierDerivative n) (w : Euclidean (n - 1) → ℂ)
    (t : AdjointDerivativeTerm n) :
    differentiateAdjointTerm L V d (frequencyScaleTerm w t) =
      (differentiateAdjointTerm L V d t).map (frequencyScaleTerm w) := by
  simp [differentiateAdjointTerm, frequencyScaleTerm,
    zeroBranchAmplitude_frequencyScale, firstBranchAmplitude_frequencyScale,
    List.map_ofFn, Function.comp_def]

/-- The actual expansion preserves an arbitrary frequency-only factor exactly
(`app:ch_background:prop:bg-adjoint`). No bound on generated symbols is assumed. -/
theorem adjointDerivativeExpansion_frequencyScale
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (ds : List (InitialCarrierDerivative n)) (w : Euclidean (n - 1) → ℂ)
    (a : AdjointAmplitude n) :
    adjointDerivativeExpansion L V ds (frequencyScaleAmplitude w a) =
      (adjointDerivativeExpansion L V ds a).map (frequencyScaleTerm w) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      simp only [adjointDerivativeExpansion, ih, List.flatMap_map, List.map_flatMap]
      congr 1
      funext t
      exact differentiateAdjointTerm_frequencyScale L V d w t

/-- The unchanged radial half-order factor in `app:ch_background:eq:bg-T`.
The angular mask is deliberately part of the normalized amplitude. -/
def halfOrderRadialFactor (χ : ℝ → ℝ) (η : Euclidean (n - 1)) : ℂ :=
  (χ ‖η‖ * Real.sqrt ‖η‖ : ℝ)

/-- Specialization of exact factor preservation to the manuscript's cutoff
times square root (`app:ch_background:prop:bg-adjoint`). -/
theorem adjointDerivativeExpansion_halfOrderRadialFactor
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (ds : List (InitialCarrierDerivative n)) (χ : ℝ → ℝ) (a : AdjointAmplitude n) :
    adjointDerivativeExpansion L V ds
        (frequencyScaleAmplitude (halfOrderRadialFactor χ) a) =
      (adjointDerivativeExpansion L V ds a).map
        (frequencyScaleTerm (halfOrderRadialFactor χ)) :=
  adjointDerivativeExpansion_frequencyScale L V ds _ a

end JanetCartan.ContinuumAdjoint.DerivativeKernels
