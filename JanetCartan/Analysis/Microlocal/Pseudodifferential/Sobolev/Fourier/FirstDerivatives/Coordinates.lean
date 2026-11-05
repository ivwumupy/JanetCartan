module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.FirstDerivatives.Representation

/-!
# Distributional coordinate derivatives of Euclidean L² functions

We use the standard orthonormal basis and Mathlib's distributional directional
derivative. The Fourier convention gives the multiplier `2π i ξⱼ`. At
nonnegative order, Bessel regularity proves existence of actual L² derivative
representatives, as required by the gain-one argument following
`app:ch_regular_base:eq:graph-derivative-transfer`. All statements allow
zero-dimensional Euclidean space.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap ContDiff LineDeriv

namespace JanetCartan.Pseudodifferential

variable {d : ℕ}

/-- The actual distributional coordinate derivative in the standard Euclidean
basis, for `app:ch_regular_base:eq:graph-derivative-transfer`. -/
def euclideanCoordinateDerivative (i : Fin d)
    (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    𝓢'(EuclideanSpace ℝ (Fin d), ℂ) :=
  ∂_{EuclideanSpace.basisFun (Fin d) ℝ i}
    (u : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))

/-- An L² class represents the coordinate derivative as a tempered distribution;
this is the derivative notion in
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
def HasEuclideanL2CoordinateDerivative (i : Fin d)
    (u v : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) : Prop :=
  euclideanCoordinateDerivative i u = (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))

/-- The multiplier `2π i ξⱼ` for the Fourier convention used in
`app:ch_regular_base:eq:fio-input`. -/
def euclideanCoordinateDerivativeSymbol (i : Fin d) (ξ : EuclideanSpace ℝ (Fin d)) : ℂ :=
  (2 * Real.pi * Complex.I) * (ξ i : ℂ)

/-- The coordinate symbol is a tempered multiplier, for
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem hasTemperateGrowth_euclideanCoordinateDerivativeSymbol (i : Fin d) :
    (euclideanCoordinateDerivativeSymbol i).HasTemperateGrowth := by
  have hg : (fun ξ : EuclideanSpace ℝ (Fin d) ↦
      (2 * Real.pi * Complex.I) *
        (inner ℝ ξ (EuclideanSpace.basisFun (Fin d) ℝ i) : ℂ)).HasTemperateGrowth := by
    fun_prop
  unfold euclideanCoordinateDerivativeSymbol
  simpa only [EuclideanSpace.inner_basisFun_real] using hg

/-- Fourier transform of the actual coordinate derivative, with the `2π i`
normalization required in `app:ch_regular_base:eq:fio-input`. -/
theorem fourier_euclideanCoordinateDerivative (i : Fin d)
    (u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    𝓕 (euclideanCoordinateDerivative i u) =
      TemperedDistribution.smulLeftCLM ℂ (euclideanCoordinateDerivativeSymbol i)
        ((𝓕 u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
          𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
  rw [euclideanCoordinateDerivative, TemperedDistribution.fourier_lineDerivOp_eq,
    Lp.fourier_toTemperedDistribution_eq]
  have hg : (fun ξ : EuclideanSpace ℝ (Fin d) ↦
    (inner ℝ ξ (EuclideanSpace.basisFun (Fin d) ℝ i) : ℂ)).HasTemperateGrowth := by fun_prop
  rw [← smul_apply, ← TemperedDistribution.smulLeftCLM_smul hg]
  congr 2
  funext ξ
  change (2 * Real.pi * Complex.I) *
    (inner ℝ ξ (EuclideanSpace.basisFun (Fin d) ℝ i) : ℂ) = _
  rw [EuclideanSpace.inner_basisFun_real]
  rfl

/-- Any L² derivative representative has the asserted Fourier multiplier almost
everywhere, as used after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem HasEuclideanL2CoordinateDerivative.fourier_ae_eq {i : Fin d}
    {u v : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (h : HasEuclideanL2CoordinateDerivative i u v) :
    (fun ξ ↦ euclideanCoordinateDerivativeSymbol i ξ *
      (𝓕 u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) ξ) =ᵐ[volume]
      (𝓕 v : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) := by
  have he := congrArg (fun T : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ) ↦ 𝓕 T) h
  rw [fourier_euclideanCoordinateDerivative, Lp.fourier_toTemperedDistribution_eq] at he
  exact ae_eq_pointwise_smul_of_toTemperedDistribution_eq _
    (hasTemperateGrowth_euclideanCoordinateDerivativeSymbol i) (𝓕 u) (𝓕 v) he

/-- Order `s + 1` supplies an actual L² coordinate derivative of order `s`, for
`s ≥ 0`. This proves the forward existence needed for the gain-one argument
after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem MemFourierSobolev.exists_coordinateDerivative {s : ℝ} (hs : 0 ≤ s)
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (hu : MemFourierSobolev (s + 1) u) (i : Fin d) :
    ∃ v : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2,
      HasEuclideanL2CoordinateDerivative i u v ∧ MemFourierSobolev s v := by
  have hd : TemperedDistribution.MemSobolev s 2 (euclideanCoordinateDerivative i u) := by
    simpa [euclideanCoordinateDerivative] using
      (hu.memSobolev.lineDerivOp (m := EuclideanSpace.basisFun (Fin d) ℝ i))
  obtain ⟨v, hv⟩ := TemperedDistribution.memSobolev_zero_iff.mp (hd.mono hs)
  refine ⟨v, hv, memFourierSobolev_iff_memSobolev.mpr ?_⟩
  rwa [← hv]

/-- The L² representative of a distributional coordinate derivative is unique,
for `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem HasEuclideanL2CoordinateDerivative.unique {i : Fin d}
    {u v w : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (hv : HasEuclideanL2CoordinateDerivative i u v)
    (hw : HasEuclideanL2CoordinateDerivative i u w) : v = w := by
  have h : (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) = w := hv.symm.trans hw
  have hmul : TemperedDistribution.smulLeftCLM ℂ (fun _ : EuclideanSpace ℝ (Fin d) ↦ 1)
      (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) = w := by
    simpa only [TemperedDistribution.smulLeftCLM_const, one_smul] using h
  apply Lp.ext
  simpa using ae_eq_pointwise_smul_of_toTemperedDistribution_eq _ (by fun_prop) v w hmul

/-- Simultaneous L² representatives of all first derivatives, including the
empty family in dimension zero, for
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem MemFourierSobolev.exists_coordinateDerivatives {s : ℝ} (hs : 0 ≤ s)
    {u : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (hu : MemFourierSobolev (s + 1) u) :
    ∃ v : Fin d → Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2,
      ∀ i, HasEuclideanL2CoordinateDerivative i u (v i) ∧ MemFourierSobolev s (v i) := by
  exact Classical.axiomOfChoice (fun i ↦ hu.exists_coordinateDerivative hs i)

/-- Bessel weighting commutes with the coordinate multiplier almost everywhere,
for the norm comparison after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem HasEuclideanL2CoordinateDerivative.weightedL2Fourier_ae_eq {i : Fin d}
    {u v : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2}
    (h : HasEuclideanL2CoordinateDerivative i u v) (s : ℝ) :
    (fun ξ ↦ euclideanCoordinateDerivativeSymbol i ξ * weightedL2Fourier s u ξ) =ᵐ[volume]
      weightedL2Fourier s v := by
  filter_upwards [h.fourier_ae_eq] with ξ hξ
  simp only [weightedL2Fourier, Complex.real_smul, ← hξ]
  ring

/-- Absolute size of the coordinate symbol, retaining the Fourier normalization
in `app:ch_regular_base:eq:fio-input`. -/
theorem norm_euclideanCoordinateDerivativeSymbol (i : Fin d)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖euclideanCoordinateDerivativeSymbol i ξ‖ = 2 * Real.pi * |ξ i| := by
  simp [euclideanCoordinateDerivativeSymbol, abs_of_pos Real.pi_pos]

end JanetCartan.Pseudodifferential
