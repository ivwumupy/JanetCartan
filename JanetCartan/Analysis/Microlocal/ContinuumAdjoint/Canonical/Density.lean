module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.RawAssembly
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.Masks
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FrequencyCutoffs

/-!
# The canonical full-frequency density

Instantiate the multiplier in `app:ch_background:eq:bg-density-adjoint` with
the SAME angular masks and high-frequency cutoff as `CanonicalCarrier.data`.
All mask regularity, support, and size premises are discharged. The physical
cutoff is a fixed bump on the literal initial product space. Its plateau must
contain the core footpoints when the finite geometric family is selected.

The input is the existing full raw Sobolev domain. These results do not assert
that the actual carrier adjoint belongs to that domain; that is the separate
adjoint construction in `app:ch_background:prop:bg-adjoint`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace JanetCartan.ContinuumAdjoint.Canonical
open ContinuumRow CarrierSobolev DensityMultiplier

variable {n : ℕ} (z₀ : Euclidean 3) (θ₀ : Euclidean (n - 1))
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a)

/-- Complex form of the actual fixed angular mask, before restriction to unit
directions (`app:ch_background:eq:bg-density-adjoint`). -/
def densityAngular (p : CarrierVariable n) : ℂ :=
  CanonicalConic.angularMask z₀ θ₀ hr ha p.1 p.2

/-- Smoothness is supplied by the constructed angular bump
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem densityAngular_smooth : ContDiff ℝ ∞ (densityAngular z₀ θ₀ hr ha) :=
  Complex.ofRealCLM.contDiff.comp (CanonicalConic.angularMask_smooth z₀ θ₀ hr ha)

/-- The actual angular mask is compact in all carrier and direction variables
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem densityAngular_compact : HasCompactSupport (densityAngular z₀ θ₀ hr ha) :=
  (CanonicalConic.angularMask_compact z₀ θ₀ hr ha).comp_left (by simp)

/-- The fixed angular constant is one, independently of the phase, immersion,
initial scalar, and Sobolev order (`app:ch_background:eq:bg-density-adjoint`). -/
theorem densityAngular_norm_le (z : CarrierParameter) (θ : Euclidean (n - 1)) :
    ‖densityAngular z₀ θ₀ hr ha (z, θ)‖ ≤ 1 := by
  rw [densityAngular, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (CanonicalConic.angularMask_mem_Icc z₀ θ₀ hr ha z θ).1]
  exact (CanonicalConic.angularMask_mem_Icc z₀ θ₀ hr ha z θ).2

/-- The canonical high-frequency mask is a contraction
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem densityHigh_abs_le (t : ℝ) : |FixedCutoffs.highFrequency t| ≤ 1 := by
  rw [abs_of_nonneg (FixedCutoffs.highFrequency_mem_Icc t).1]
  exact (FixedCutoffs.highFrequency_mem_Icc t).2

/-- The literal, unbounded-frequency half-order symbol for the selected chart
(`app:ch_background:eq:bg-density-adjoint`). -/
def densitySymbol : CarrierVariable n → ℂ :=
  densityFrequencySymbol (densityAngular z₀ θ₀ hr ha) FixedCutoffs.highFrequency

/-- No frequencies above the fixed transition are removed, and the exponent
is exactly one half (`app:ch_background:eq:bg-density-adjoint`). -/
theorem densitySymbol_eq_of_high (p : CarrierVariable n) (hp : 2 ≤ ‖p.2‖) :
    densitySymbol z₀ θ₀ hr ha p = (Real.sqrt ‖p.2‖ : ℂ) *
      (CanonicalConic.angularMask z₀ θ₀ hr ha p.1 (‖p.2‖⁻¹ • p.2) : ℂ) :=
  densityFrequencySymbol_eq_of_high _ (fun _ h ↦ FixedCutoffs.highFrequency_one h) p hp

/-- Actual partial inverse Fourier synthesis, on the full raw order-one
domain. It uses the shared unitary radian normalization and literal Lebesgue
measure (`app:ch_background:eq:bg-density-adjoint`). -/
def densitySynthesis (u : CarrierL2 n) (hu : MemRawSobolev 1 u) : CarrierL2 n :=
  densitySynthesisL2 (densityAngular_smooth z₀ θ₀ hr ha).continuous.measurable
    FixedCutoffs.highFrequency_smooth.continuous.measurable (by norm_num : (0 : ℝ) ≤ 1)
    (fun z θ _ ↦ densityAngular_norm_le z₀ θ₀ hr ha z θ)
    densityHigh_abs_le (FixedCutoffs.highFrequency_zero (by norm_num)) u
    (carrierWeightedMem_etaBesselWeight_of_rawSobolev hu)

/-- The real density before the physical initial cutoff, with both complex
quadratures retained in its input (`app:ch_background:eq:bg-density-adjoint`). -/
def densityUncut (u : CarrierL2 n) (hu : MemRawSobolev 1 u) :
    Lp ℝ 2 (carrierMeasure n) := twoReL2 (densitySynthesis z₀ θ₀ hr ha u hu)

/-- The actual `D_a` with a fixed physical initial bump. Selection of its
plateau uses the core footpoint buffer in the final geometric assembly
(`app:ch_background:eq:bg-density-adjoint`). -/
def density (b : ContDiffBump (0 : CarrierVariable n))
    (u : CarrierL2 n) (hu : MemRawSobolev 1 u) : Lp ℝ 2 (carrierMeasure n) :=
  compactDensityPhysicalCutoffL2 (b.contDiff (n := ⊤)).continuous b.hasCompactSupport
    (densitySynthesis z₀ θ₀ hr ha u hu)

/-- The physical mask in `D_a` is the original bump on representatives
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem density_coeFn (b : ContDiffBump (0 : CarrierVariable n))
    (u : CarrierL2 n) (hu : MemRawSobolev 1 u) :
    density z₀ θ₀ hr ha b u hu =ᵐ[carrierMeasure n]
      fun p ↦ 2 * (b p • densitySynthesis z₀ θ₀ hr ha u hu p).re :=
  compactDensityPhysicalCutoffL2_coeFn (b.contDiff (n := ⊤)).continuous b.hasCompactSupport _

/-- The full initial-variable bound for the canonical density, both before
and after its physical cutoff. No multiplier estimate, approximation theorem,
or mask regularity is assumed. The only datum premise is membership in the
shared full `X^(s+1)` domain (`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_density_bounds (b : ContDiffBump (0 : CarrierVariable n)) (s : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (u : CarrierL2 n) (hu : MemRawSobolev (s + 1) u),
      let hu₁ := hu.mono (by omega : 1 ≤ s + 1)
      (MemPhysicalSobolev s (densitySynthesis z₀ θ₀ hr ha u hu₁) ∧
        physicalSobolevNorm s (densitySynthesis z₀ θ₀ hr ha u hu₁) ≤
          L * rawSobolevNorm (s + 1) u) ∧
      (MemPhysicalSobolev s (physicalComplexifyL2 (densityUncut z₀ θ₀ hr ha u hu₁)) ∧
        physicalSobolevNorm s (physicalComplexifyL2 (densityUncut z₀ θ₀ hr ha u hu₁)) ≤
          L * rawSobolevNorm (s + 1) u) ∧
      (MemPhysicalSobolev s (physicalComplexifyL2 (density z₀ θ₀ hr ha b u hu₁)) ∧
        physicalSobolevNorm s (physicalComplexifyL2 (density z₀ θ₀ hr ha b u hu₁)) ≤
          L * rawSobolevNorm (s + 1) u) :=
  exists_densityOutputs_rawSobolev_bound s
    (densityAngular_smooth z₀ θ₀ hr ha).continuous.measurable
    FixedCutoffs.highFrequency_smooth.continuous.measurable (by norm_num : (0 : ℝ) ≤ 1)
    (fun z θ _ ↦ densityAngular_norm_le z₀ θ₀ hr ha z θ)
    densityHigh_abs_le (FixedCutoffs.highFrequency_zero (by norm_num))
    (densityAngular_smooth z₀ θ₀ hr ha) (densityAngular_compact z₀ θ₀ hr ha)
    FixedCutoffs.highFrequency_smooth (fun _ h ↦ FixedCutoffs.highFrequency_zero h)
    b.contDiff b.hasCompactSupport

/-- On compact smooth tests, the canonical density is exactly the source
formula with the shared unitary inverse integral, including its normalization
and the factor two (`app:ch_background:eq:bg-density-adjoint`). -/
theorem density_test_coeFn (b : ContDiffBump (0 : CarrierVariable n))
    (f : carrierInitialTestSpace n) (hf : MemRawSobolev 1 (carrierInitialTestToLp f)) :
    density z₀ θ₀ hr ha b (carrierInitialTestToLp f) hf =ᵐ[carrierMeasure n]
      fun p ↦ 2 * (b p • unitaryInverseIntegral
        (fun η ↦ densitySymbol z₀ θ₀ hr ha (p.1, η) * f.val (p.1, η)) p.2).re := by
  filter_upwards [density_coeFn z₀ θ₀ hr ha b (carrierInitialTestToLp f) hf,
    densitySynthesisL2_test_coeFn
      (densityAngular_smooth z₀ θ₀ hr ha).continuous.measurable
      FixedCutoffs.highFrequency_smooth.continuous.measurable (by norm_num : (0 : ℝ) ≤ 1)
      (fun z θ _ ↦ densityAngular_norm_le z₀ θ₀ hr ha z θ)
      densityHigh_abs_le (FixedCutoffs.highFrequency_zero (by norm_num))
      (densityAngular_smooth z₀ θ₀ hr ha) FixedCutoffs.highFrequency_smooth
      (fun _ h ↦ FixedCutoffs.highFrequency_zero h) f
      (carrierWeightedMem_etaBesselWeight_of_rawSobolev hf)] with p hp hs
  exact hp.trans (by rw [show densitySynthesis z₀ θ₀ hr ha (carrierInitialTestToLp f) hf p =
    unitaryInverseIntegral (fun η ↦ densitySymbol z₀ θ₀ hr ha (p.1, η) * f.val (p.1, η))
      p.2 from hs])

end JanetCartan.ContinuumAdjoint.Canonical
