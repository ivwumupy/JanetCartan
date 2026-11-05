module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Kernel
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.Symbol
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Realization

/-!
# Uncut initial density and its measured transported increment

Literal definitions for `app:ch_background:eq:bg-affine-mean` and
`app:ch_background:eq:bg-density-four`. The external carrier weight remains
in the mean. No initial spatial cutoff or upper frequency cutoff is inserted.
The actual geometry and angular support are inputs from the continuum row and
positive-background constructions; these definitions assert no existence result.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.UncutDensity

open ContinuumRow CarrierSobolev ContinuumAdjoint.DensityMultiplier

variable {n N : ℕ}

/-- The literal half-order symbol of the given carrier kernel, used by
`app:ch_background:eq:bg-density-four`. -/
def carrierDensitySymbol (d : CarrierData n N) : CarrierVariable n → ℂ :=
  densityFrequencySymbol (fun u ↦ (d.angularCutoff u.1 u.2 : ℂ)) d.highCutoff

/-- Unprefactored radian synthesis, with real coefficient `c`; the paper uses
`c = 4` in `bg-density-four` and `c = -2` in `mean-density-recursion`. -/
def initialDensity (d : CarrierData n N) (c : ℝ) (f : CarrierVariable n → ℂ)
    (p : CarrierVariable n) : ℝ :=
  c * (radianInverseIntegral (fun η ↦ carrierDensitySymbol d (p.1, η) * f (p.1, η))
    p.2).re

/-- The measured normal square and reduced stress contraction, retaining the
normal with its original initial scalar (`app:ch_background:eq:bg-affine-mean`). -/
def measuredStress (d : CarrierData n N) (x : Torus n) (z : CarrierParameter) :
    Euclidean n :=
  (d.measurementCutoff x * ‖d.normalField (d.chartPoint x) z‖ ^ 2) •
    reducedCovector d (d.chartPoint x) (d.covector (d.chartPoint x) z)

/-- Measured increment of the affine transported mean. The external measure
is `ψ dz`, and the initial density is evaluated at the actual footpoint `Y`
(`app:ch_background:eq:bg-affine-mean`, `app:ch_background:eq:bg-density-twice`). -/
def measuredIncrement (d : CarrierData n N) (ψ : CarrierParameter → ℝ)
    (v : CarrierVariable n → ℝ) (x : Torus n) : Euclidean n :=
  d.outputChart.indicator (fun x ↦
    ∫ z, (ψ z * v (z, d.transportedPosition (d.chartPoint x) z)) • measuredStress d x z
      ∂(volume.prod volume)) x

/-- Angular support of the actual symbol forces carrier support of the uncut
density, for the plateau step in `app:ch_background:eq:bg-density-twice`. -/
theorem initialDensity_eq_zero_of_angular (d : CarrierData n N) (c : ℝ)
    (f : CarrierVariable n → ℂ) (z : CarrierParameter)
    (hz : ∀ θ, d.angularCutoff z θ = 0) (y : Euclidean (n - 1)) :
    initialDensity d c f (z, y) = 0 := by
  simp [initialDensity, radianInverseIntegral, carrierDensitySymbol,
    densityFrequencySymbol, halfOrderCoefficient, angularHighMask, hz]

/-- The angular carrier support gives the exact external-weight product;
the desired product is proved, not postulated (`app:ch_background:eq:bg-density-twice`).
The positive-background owner supplies the geometric plateau hypothesis. -/
theorem externalWeight_mul_initialDensity (d : CarrierData n N)
    (χ : CarrierParameter → ℝ)
    (hχ : ∀ z θ, d.angularCutoff z θ ≠ 0 → χ z = 1)
    (c : ℝ) (f : CarrierVariable n → ℂ) (p : CarrierVariable n) :
    χ p.1 ^ 2 * initialDensity d c f p = initialDensity d c f p := by
  by_cases hp : χ p.1 = 1
  · simp [hp]
  · have hz : ∀ θ, d.angularCutoff p.1 θ = 0 := by
      intro θ
      by_contra h
      exact hp (hχ p.1 θ h)
    rw [show initialDensity d c f p = 0 from
      initialDensity_eq_zero_of_angular d c f p.1 hz p.2]
    simp

/-- The carrier support of the uncut synthesis is inside the plateau, uniformly
in the initial spatial variable (`app:ch_background:eq:bg-density-four`). -/
theorem initialDensity_support_subset (d : CarrierData n N)
    (χ : CarrierParameter → ℝ)
    (hχ : ∀ z θ, d.angularCutoff z θ ≠ 0 → χ z = 1)
    (c : ℝ) (f : CarrierVariable n → ℂ) :
    Function.support (initialDensity d c f) ⊆ {p | χ p.1 = 1} := by
  intro p hp
  by_contra hn
  apply hp
  exact initialDensity_eq_zero_of_angular d c f p.1
    (fun θ ↦ by by_contra h; exact hn (hχ p.1 θ h)) p.2

/-- The spatial L² synthesis uses the already constructed partial unitary
inverse and the exact radian conversion factor. Its input is the half-order
frequency output, not unmultiplied raw data (`app:ch_background:eq:bg-density-four`). -/
def realSynthesisL2 (c : ℝ) (g : CarrierL2 n) : Lp ℝ 2 (carrierMeasure n) :=
  (c * synthesisFactor n) •
    Complex.reCLM.compLpL 2 (carrierMeasure n) (partialUnitaryInverse n g)

/-- Strong convergence of the half-order frequency outputs gives strong
convergence of uncut density synthesis, with no spatial truncation
(`app:ch_background:eq:bg-density-four`). -/
theorem continuous_realSynthesisL2 (c : ℝ) :
    Continuous (realSynthesisL2 (n := n) c) := by
  unfold realSynthesisL2
  exact (continuous_const : Continuous (fun _ : CarrierL2 n ↦ c * synthesisFactor n)).smul
    ((Complex.reCLM.compLpL 2 (carrierMeasure n)).continuous.comp
    (partialUnitaryInverse n).continuous)

/-- Exact norm control by the frequency output, including the radian synthesis
constant (`app:ch_background:eq:bg-density-four`). This does not assert a bound
for the unbounded half-order multiplier on unweighted raw L² data. -/
theorem norm_realSynthesisL2_le (c : ℝ) (g : CarrierL2 n) :
    ‖realSynthesisL2 c g‖ ≤ |c| * synthesisFactor n * ‖g‖ := by
  have hr : ‖Complex.reCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa using Complex.abs_re_le_norm z
  have hb : ‖Complex.reCLM.compLpL 2 (carrierMeasure n) (partialUnitaryInverse n g)‖ ≤
      ‖g‖ := by
    calc
      _ ≤ ‖Complex.reCLM‖ * ‖partialUnitaryInverse n g‖ :=
        Complex.reCLM.norm_compLp_le _
      _ ≤ 1 * ‖g‖ := by
        rw [partialUnitaryInverse_norm]
        exact mul_le_mul_of_nonneg_right hr (norm_nonneg _)
      _ = _ := one_mul _
  simpa only [realSynthesisL2, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (synthesisFactor_pos n)] using
    mul_le_mul_of_nonneg_left hb (abs_nonneg (c * synthesisFactor n))

/-- Exact identification with the literal uncut real density whenever its
frequency output has integrable slices. All hypotheses concern the multiplier
output; none is a transported mean identity (`app:ch_background:eq:bg-density-four`). -/
theorem realSynthesisL2_coeFn (d : CarrierData n N) (c : ℝ)
    (f : CarrierVariable n → ℂ)
    (hm : StronglyMeasurable (fun p ↦ carrierDensitySymbol d p * f p))
    (h₂ : MemLp (fun p ↦ carrierDensitySymbol d p * f p) 2 (carrierMeasure n))
    (h₁ : ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      Integrable (fun η ↦ carrierDensitySymbol d (z, η) * f (z, η))) :
    realSynthesisL2 c (h₂.toLp _) =ᵐ[carrierMeasure n] initialDensity d c f := by
  filter_upwards [Lp.coeFn_smul (c * synthesisFactor n)
      (Complex.reCLM.compLpL 2 (carrierMeasure n) (partialUnitaryInverse n (h₂.toLp _))),
    Complex.reCLM.coeFn_compLpL (p := 2) (partialUnitaryInverse n (h₂.toLp _)),
    partialUnitaryInverse_toLp_ae hm h₂ h₁] with p hp hq hr
  rw [realSynthesisL2, hp]
  simp only [Pi.smul_apply]
  rw [hq, hr]
  simp only [initialDensity, unitaryInverseIntegral, Complex.reCLM_apply,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, smul_eq_mul]
  field_simp [ne_of_gt (synthesisFactor_pos n)]

end JanetCartan.UncutDensity
