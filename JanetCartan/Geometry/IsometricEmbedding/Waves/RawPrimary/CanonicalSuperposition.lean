module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.CanonicalAtom
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.CompactSynthesis

/-!
# The canonical atom on the original Lebesgue input

The raw displacement is the integral of the actual canonical two-term atom.
Its differentiated representation is proved by differentiating that integral,
not by defining its derivative to be a proposed amplitude. The hypotheses here
are local smoothness of the atomic inputs on their common buffered domain.
The actual full-modulation family and its graded bounds still have to be
instantiated; no successful raw-family interface is assumed or constructed.

Sources: `app:ch_waves:eq:WKB-W`, `app:ch_waves:eq:individual-representation`.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open RawInputPartition

variable {n N J : ℕ}

/-- The literal raw displacement on the wide-band input. Both quadratures
use the same canonical reconstruction and shifted phase
(`app:ch_waves:eq:WKB-W`). -/
def canonicalWideWave (F : Euclidean n → Euclidean N) (τ : ℝ)
    (S : Euclidean n × Euclidean (n - 1) → ℝ)
    (b₀ b₁ : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin n))
    (ζ : Euclidean (n - 1)) (d : Euclidean (n - 1) → ℂ) (v : WideInput n J) :
    Euclidean n → EuclideanSpace ℂ (Fin N) :=
  wideSuperposition (fun p ↦ canonicalAtom F τ S b₀ b₁ (p.1, ζ + τ • p.2)) d v

/-- Smooth atomic inputs produce the SAME smooth raw displacement for every
Hilbert datum, without a smoothness assumption on that datum
(`app:ch_waves:thm:individual`). -/
theorem contDiffOn_canonicalWideWave (F : Euclidean n → Euclidean N) (τ : ℝ)
    (S : Euclidean n × Euclidean (n - 1) → ℝ)
    (b₀ b₁ : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin n))
    (ζ : Euclidean (n - 1)) {U : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hV : IsOpen V)
    (hVceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    (hAtom : ContDiffOn ℝ ∞
      (fun p ↦ canonicalAtom F τ S b₀ b₁ (p.1, ζ + τ • p.2)) (U ×ˢ V))
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) :
    ContDiffOn ℝ ∞ (canonicalWideWave F τ S b₀ b₁ ζ d v) U :=
  contDiffOn_wideSuperposition hU hV hVceil hAtom hd hM hb v

/-- Exact demodulated derivative of the actual canonical Fourier
superposition, evaluated in any physical direction. The derivative interchange
and integrability are derived from joint smoothness and the actual compactly
supported Lebesgue datum (`app:ch_waves:eq:individual-representation`). -/
theorem canonicalWideWave_derivative_representation
    (F : Euclidean n → Euclidean N) {τ : ℝ} (hτ : τ ≠ 0)
    (S : Euclidean n × Euclidean (n - 1) → ℝ)
    (b₀ b₁ : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin n))
    (ζ : Euclidean (n - 1)) {U : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hV : IsOpen V)
    (hVceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    (hAtom : ContDiffOn ℝ ∞
      (fun p ↦ canonicalAtom F τ S b₀ b₁ (p.1, ζ + τ • p.2)) (U ×ˢ V))
    (hS : ∀ η ∈ V, DifferentiableOn ℝ (fun y ↦ S (y, ζ + τ • η)) U)
    (hb₀ : ∀ η ∈ V, DifferentiableOn ℝ (fun y ↦ b₀ (y, ζ + τ • η)) U)
    (hb₁ : ∀ η ∈ V, DifferentiableOn ℝ (fun y ↦ b₁ (y, ζ + τ • η)) U)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J)
    {x : Euclidean n} (hx : x ∈ U)
    (hA : ∀ η ∈ V, DifferentiableAt ℝ
      (fun y ↦ canonicalDisplacementAmplitude F τ S b₀ b₁ (y, ζ + τ • η)) x)
    (w : Euclidean n) :
    Complex.exp (-Complex.I * (S (x, ζ) / τ : ℝ)) •
        fderiv ℝ (canonicalWideWave F τ S b₀ b₁ ζ d v) x w =
      rawPrimaryDemodulatedIntegral (fun y ξ ↦ S (y, ξ))
        (fun y ξ ↦ waveFirstAmplitude τ⁻¹ (fun t ↦ S (t, ξ))
          (fun t ↦ canonicalDisplacementAmplitude F τ S b₀ b₁ (t, ξ)) y w)
        ζ τ volume (weightedWideDensity d v) x := by
  have hi := integrable_wideSuperposition hVceil
    (contDiffOn_parameterFDeriv hU hV hAtom).continuousOn hd hM hb v hx
  rw [canonicalWideWave, (hasFDerivAt_wideSuperposition hU hV hVceil hAtom hd hM hb v hx).fderiv,
    wideSuperposition, ContinuousLinearMap.integral_apply hi, ← integral_smul,
    rawPrimaryDemodulatedIntegral]
  apply integral_congr_ae
  filter_upwards [] with η
  simp only [_root_.smul_apply]
  by_cases hη : η ∈ Metric.closedBall 0 ((2 : ℝ) ^ J)
  · have hηV := hVceil hη
    rw [fderiv_canonicalAtom F hτ hU hx _ (hS η hηV) (hb₀ η hηV)
      (hb₁ η hηV) (hA η hηV) w]
    rw [smul_comm (weightedWideDensity d v η), ← mul_smul, ← Complex.exp_add]
    congr 2
    simp only [rawPrimaryPhaseDifference, sub_div, Complex.ofReal_sub]
    ring
  · have hη' : (2 : ℝ) ^ J ≤ ‖η‖ := le_of_lt (by simpa using hη)
    rw [wideDensity_eq_zero_of_ceiling_le d v hη']
    simp

end JanetCartan.RawPrimary
