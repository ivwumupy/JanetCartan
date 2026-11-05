module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.ChartInput

/-!
# The literal raw integral on one smooth wide band

These formulas feed `exists_rawSliceBandOperator` and the differentiated
assembly of `app:ch_waves:eq:individual-raw-slice`. The physical cutoff occurs
only in the measured output. The amplitude retains the original shifted
covector; no homogeneity is used to change the phase quotient.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.RawPrimary.SliceBounds
open RawInputPartition RawInputDilation NormalComparison

variable {n : ℕ} {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- One original wide-band summand of the measured raw field
(`app:ch_waves:eq:individual-raw-slice`). The physical wave itself is not cut. -/
def rawSliceBandIntegral (S : X → Euclidean (n - 1) → ℝ)
    (A : X → Euclidean (n - 1) → E) (χ : X → ℝ) (ζ : Euclidean (n - 1))
    (τ : ℝ) (β : Euclidean (n - 1) → ℂ) (j : ℕ) (f : WideBandL2 n j) (x : X) : E :=
  (χ x : ℂ) • rawPrimaryDemodulatedIntegral S A ζ τ volume
    (fun η ↦ (Real.sqrt ‖η‖ : ℂ) * β η * f η) x

/-- The amplitude presented to the single-channel producer after the two
sharp pieces have been reassembled. The half derivative is part of this
smooth amplitude (`app:ch_waves:eq:individual-raw-slice`). -/
def rawSliceBandAmplitude (A : X → Euclidean (n - 1) → E) (χ : X → ℝ)
    (ζ : Euclidean (n - 1)) (τ : ℝ) (β : Euclidean (n - 1) → ℂ) (j : ℕ)
    (x : X) (θ : Euclidean (n - 1)) : E :=
  ((χ x : ℂ) * (Real.sqrt ‖θ‖ : ℂ) * β ((2 : ℝ) ^ j • θ)) •
    A x (ζ + (τ * (2 : ℝ) ^ j) • θ)

/-- Exact identification of the SAME raw integral with the normalized
single-channel integrand. All `2π` factors are explicit; the original raw
integral has not been redefined to have a convenient normalization
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem normalized_rawSliceBandIntegral (hn : 1 ≤ n)
    (S : X → Euclidean (n - 1) → ℝ) (A : X → Euclidean (n - 1) → E)
    (χ : X → ℝ) (ζ : Euclidean (n - 1)) {τ : ℝ} (hτ : τ ≠ 0)
    (β : Euclidean (n - 1) → ℂ) (j : ℕ)
    (hβ : ∀ η ∉ wideBand n j, β η = 0) (f : WideBandL2 n j) (x : X) :
    (2 * Real.pi) ^ (-(n : ℝ) / 2) • rawSliceBandIntegral S A χ ζ τ β j f x =
      normalOperatorScale n ((2 : ℝ) ^ j) •
        ∫ θ in wideBand n 0,
          (oscillatoryFactor ((2 : ℝ) ^ j)
            (rawPrimaryPhaseDifference S ζ (τ * (2 : ℝ) ^ j) x θ) *
              wideBandDilation n j f θ) • rawSliceBandAmplitude A χ ζ τ β j x θ := by
  calc
    _ = (2 * Real.pi) ^ (-(n : ℝ) / 2) •
        (∫ η in wideBand n j, ((Real.sqrt ‖η‖ : ℂ) *
          (Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℂ)) * β η) *
            f η) • ((χ x : ℂ) • A x (ζ + τ • η))) := by
      congr 1
      rw [rawSliceBandIntegral, rawPrimaryDemodulatedIntegral, ← integral_smul]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun η hη ↦ by simp [hβ η hη])]
      apply integral_congr_ae
      filter_upwards [] with η
      simp only [smul_smul]
      congr 1
      ring
    _ = _ := by
      rw [normalized_wideBand_rawPrimary_integral hn j hτ]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with θ
      simp only [rawSliceBandAmplitude, smul_smul, smul_smul]
      congr 1
      ring

/-- The original detector/high-pass and radial mask supply the exact support
premise of the normalization identity, retaining `1 < ‖η‖ < 2`
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem normalized_rawSliceBandIntegral_weighted (hn : 1 ≤ n)
    (S : X → Euclidean (n - 1) → ℝ) (A : X → Euclidean (n - 1) → E)
    (χ : X → ℝ) (ζ : Euclidean (n - 1)) {τ : ℝ} (hτ : τ ≠ 0)
    (d : Euclidean (n - 1) → ℂ) (j : ℕ) (f : WideBandL2 n j) (x : X) :
    (2 * Real.pi) ^ (-(n : ℝ) / 2) •
        rawSliceBandIntegral S A χ ζ τ (weightedRadialBand d j) j f x =
      normalOperatorScale n ((2 : ℝ) ^ j) •
        ∫ θ in wideBand n 0,
          (oscillatoryFactor ((2 : ℝ) ^ j)
            (rawPrimaryPhaseDifference S ζ (τ * (2 : ℝ) ^ j) x θ) *
              wideBandDilation n j f θ) •
                rawSliceBandAmplitude A χ ζ τ (weightedRadialBand d j) j x θ :=
  normalized_rawSliceBandIntegral hn S A χ ζ hτ _ j
    (fun _ hη ↦ weightedRadialBand_eq_zero_off_wideBand d hη) f x

end JanetCartan.RawPrimary.SliceBounds
