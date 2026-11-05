module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.NormalizedFullPhase.PhaseMatching

/-!
# The literal raw-wave sampling kernel

Construct `BandKernelData` from the measured raw amplitude, the original
detector/high-pass, and the existing smooth square partition. The same kernel
is used on both sharp refinements. The normalization identities discharge the
scalar matching obligations of `app:ch_waves:eq:sampling-operator-bounds`.

The actual coefficient producer must still supply a continuous extension of
the measured amplitude and its common bound. No operator or mean-normal bound
is an input here. The sharp band bound and the full-normal jet budgets remain
separate obligations of the actual family construction.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff

namespace JanetCartan.Sampling.RawKernel
open SamplingKernelBounds RawInputPartition NormalComparison
open MeanNormalBound.NormalizedFullPhase

variable {n J : ℕ} {P : Type*} [TopologicalSpace P]

/-- The physical Fourier scalar and ORIGINAL smooth radial band belong to
the measured amplitude; the detector/high-pass stays in `mask`
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def measuredBandAmplitude
    (A : P → Euclidean n → Euclidean (n - 1) → EuclideanSpace ℂ (Fin n))
    (ζ : P → Euclidean (n - 1)) (τ : P → ℝ)
    (q : ((Fin J × P) × Euclidean (n - 1)) × Euclidean n) :
    EuclideanSpace ℂ (Fin n) :=
  (((2 * Real.pi) ^ (-(n : ℝ) / 2) * radialBand n q.1.1.1.val q.1.2 : ℝ) : ℂ) •
    A q.1.1.2 q.2 (ζ q.1.1.2 + τ q.1.1.2 • q.1.2)

/-- Actual kernel construction from primitive continuous measured coefficients.
The constant and physical support do not depend on the ceiling `J`. The
amplitude bounds are scalar coefficient bounds, not the sought oscillatory
operator estimates (`app:ch_waves:eq:sampling-operator-bounds`). -/
def bandKernelData
    (S : P → Euclidean n → Euclidean (n - 1) → ℝ)
    (A : P → Euclidean n → Euclidean (n - 1) → EuclideanSpace ℂ (Fin n))
    (ζ : P → Euclidean (n - 1)) (τ : P → ℝ)
    (d : Euclidean (n - 1) → ℂ)
    (hS : Continuous (fun q : (P × Euclidean n) × Euclidean (n - 1) ↦
      S q.1.1 q.1.2 q.2))
    (hA : Continuous (fun q : (P × Euclidean n) × Euclidean (n - 1) ↦
      A q.1.1 q.1.2 q.2))
    (hζ : Continuous ζ) (hτ : Continuous τ) (hτ₀ : ∀ p, τ p ≠ 0)
    (hd : Continuous d) (K : Set (Euclidean n)) (hK : IsCompact K)
    (hAK : ∀ p x η, x ∉ K → A p x η = 0)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hAM : ∀ p x η, ‖A p x η‖ ≤ M) (hdB : ∀ η, ‖d η‖ ≤ B) :
    BandKernelData (Fin J × P) n where
  phase q := rawPrimaryPhaseDifference (S q.1.1.2) (ζ q.1.1.2)
    (τ q.1.1.2) q.2 q.1.2
  phase_continuous := by
    unfold rawPrimaryPhaseDifference
    have hleft : Continuous (fun q : ((Fin J × P) × Euclidean (n - 1)) × Euclidean n ↦
        S q.1.1.2 q.2 (ζ q.1.1.2 + τ q.1.1.2 • q.1.2)) :=
      hS.comp (f := fun q : ((Fin J × P) × Euclidean (n - 1)) × Euclidean n ↦
        ((q.1.1.2, q.2), ζ q.1.1.2 + τ q.1.1.2 • q.1.2))
        (by fun_prop)
    have hright : Continuous (fun q : ((Fin J × P) × Euclidean (n - 1)) × Euclidean n ↦
        S q.1.1.2 q.2 (ζ q.1.1.2)) :=
      hS.comp (f := fun q : ((Fin J × P) × Euclidean (n - 1)) × Euclidean n ↦
        ((q.1.1.2, q.2), ζ q.1.1.2)) (by fun_prop)
    exact (hleft.sub hright).div (by fun_prop) (fun q ↦ hτ₀ q.1.1.2)
  mask := d
  mask_continuous := hd
  amplitude := measuredBandAmplitude A ζ τ
  amplitude_continuous := by
    have hr : Continuous (fun q : ((Fin J × P) × Euclidean (n - 1)) × Euclidean n ↦
        radialBand n q.1.1.1.val q.1.2) := by
      have h : Continuous (fun q : Fin J × Euclidean (n - 1) ↦
          radialBand n q.1.val q.2) :=
        continuous_prod_of_discrete_left.mpr
          (fun j ↦ (contDiff_radialBand n j.val (r := 0)).continuous)
      exact h.comp (f := fun q : ((Fin J × P) × Euclidean (n - 1)) × Euclidean n ↦
        (q.1.1.1, q.1.2)) (by fun_prop)
    unfold measuredBandAmplitude
    have ha : Continuous (fun q : ((Fin J × P) × Euclidean (n - 1)) × Euclidean n ↦
        A q.1.1.2 q.2 (ζ q.1.1.2 + τ q.1.1.2 • q.1.2)) :=
      hA.comp (f := fun q : ((Fin J × P) × Euclidean (n - 1)) × Euclidean n ↦
        ((q.1.1.2, q.2), ζ q.1.1.2 + τ q.1.1.2 • q.1.2))
        (by fun_prop)
    exact (Complex.continuous_ofReal.comp (continuous_const.mul hr)).smul ha
  physicalSupport := K
  physicalSupport_compact := hK
  amplitude_eq_zero p η x hx := by
    simp only [measuredBandAmplitude, hAK p.2 x _ hx, smul_zero]
  amplitudeBound := (2 * Real.pi) ^ (-(n : ℝ) / 2) * M
  amplitudeBound_nonneg := mul_nonneg (Real.rpow_nonneg (by positivity) _) hM
  amplitude_le p η x := by
    have hb : |radialBand n p.1.val η| ≤ 1 := by
      have h := bandProfile_mem (‖η‖ / dyadicScale p.1.val)
      exact (abs_of_nonneg h.1).trans_le h.2
    simp only [measuredBandAmplitude, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 2 * Real.pi) _)]
    exact mul_le_mul
      ((mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (by positivity) _)).trans_eq
        (mul_one _)) (hAM _ _ _) (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
  maskBound := B
  maskBound_nonneg := hB
  mask_le := hdB

/-- Normalized amplitude in the ORIGINAL variables `(s,θ)`, before inserting
them into Euclidean full-input coordinates. The extra smooth majorant acts on
the carrier; it does not alter the original measurement or detector
(`app:ch_waves:eq:sampling-operator-bounds`). -/
def normalizedMeasuredAmplitude
    (A : P → Euclidean n → Euclidean (n - 1) → EuclideanSpace ℂ (Fin n))
    (ζ : P → Euclidean (n - 1)) (τ : P → ℝ)
    (d : Euclidean (n - 1) → ℂ) (j : ℕ) (p : P) (χ : ℝ)
    (x : Euclidean n) (θ : Euclidean (n - 1)) : EuclideanSpace ℂ (Fin n) :=
  ((χ : ℂ) * (Real.sqrt ‖θ‖ : ℂ) * weightedRadialBand d j ((2 : ℝ) ^ j • θ)) •
    A p x (ζ p + (τ p * (2 : ℝ) ^ j) • θ)

omit [TopologicalSpace P] in
/-- Exact amplitude matching, including the transverse square-root Jacobian,
half derivative, `2π` scalar and unchanged smooth band. This is the literal
`hamplitude` equation required by the full-phase normal identification
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem measuredBandAmplitude_normalization (hn : 1 ≤ n)
    (A : P → Euclidean n → Euclidean (n - 1) → EuclideanSpace ℂ (Fin n))
    (ζ : P → Euclidean (n - 1)) (τ : P → ℝ)
    (d : Euclidean (n - 1) → ℂ) (j : Fin J) (p : P) (χ : ℝ)
    (x : Euclidean n) (θ : Euclidean (n - 1)) (i : Fin n) :
    (Real.sqrt (((2 : ℝ) ^ j.val) ^ (n - 1)) : ℂ) * (χ : ℂ) *
      (Real.sqrt ‖(2 : ℝ) ^ j.val • θ‖ : ℂ) * d ((2 : ℝ) ^ j.val • θ) *
      measuredBandAmplitude A ζ τ (((j, p), (2 : ℝ) ^ j.val • θ), x) i =
    (normalOperatorScale n ((2 : ℝ) ^ j.val) : ℂ) *
      normalizedMeasuredAmplitude A ζ τ d j.val p χ x θ i := by
  have h := congrArg (fun t : ℝ ↦ (t : ℂ)) (fullPhase_fourier_normalization hn j.val θ)
  push_cast at h
  simp only [measuredBandAmplitude, normalizedMeasuredAmplitude, weightedRadialBand,
    PiLp.smul_apply, smul_eq_mul, smul_smul, Complex.ofReal_mul]
  linear_combination
    (χ : ℂ) * d ((2 : ℝ) ^ j.val • θ) *
      (radialBand n j.val ((2 : ℝ) ^ j.val • θ) : ℂ) *
      A p x (ζ p + (τ p * (2 : ℝ) ^ j.val) • θ) i * h

omit [TopologicalSpace P] in
/-- The constructed amplitude vanishes outside the original WIDE band.
This is an identity of smooth amplitudes, not a use of sharp indicators in
symbol calculus (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem measuredBandAmplitude_eq_zero_off_wideBand
    (A : P → Euclidean n → Euclidean (n - 1) → EuclideanSpace ℂ (Fin n))
    (ζ : P → Euclidean (n - 1)) (τ : P → ℝ)
    (j : Fin J) (p : P) (η : Euclidean (n - 1)) (x : Euclidean n)
    (hη : η ∉ wideBand n j.val) :
    measuredBandAmplitude A ζ τ (((j, p), η), x) = 0 := by
  simp [measuredBandAmplitude, radialBand_eq_zero_off_wideBand hη]

section Constructed

variable
    (S : P → Euclidean n → Euclidean (n - 1) → ℝ)
    (A : P → Euclidean n → Euclidean (n - 1) → EuclideanSpace ℂ (Fin n))
    (ζ : P → Euclidean (n - 1)) (τ : P → ℝ) (d : Euclidean (n - 1) → ℂ)
    (hS : Continuous (fun q : (P × Euclidean n) × Euclidean (n - 1) ↦
      S q.1.1 q.1.2 q.2))
    (hA : Continuous (fun q : (P × Euclidean n) × Euclidean (n - 1) ↦
      A q.1.1 q.1.2 q.2))
    (hζ : Continuous ζ) (hτ : Continuous τ) (hτ₀ : ∀ p, τ p ≠ 0)
    (hd : Continuous d) (K : Set (Euclidean n)) (hK : IsCompact K)
    (hAK : ∀ p x η, x ∉ K → A p x η = 0)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hAM : ∀ p x η, ‖A p x η‖ ≤ M) (hdB : ∀ η, ‖d η‖ ≤ B)

local notation "D" => bandKernelData (J := J) S A ζ τ d hS hA hζ hτ hτ₀ hd
  K hK hAK M B hM hB hAM hdB

/-- The squared-kernel constant of the CONSTRUCTED family depends only on
the common coefficient budget and support, not on `J`, shifts or frequency.
This closes `hkernel` once the actual coefficient producer supplies `hAM`
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem bandKernelData_squaredKernelConstant :
    (D).squaredKernelConstant = volume.real K * B ^ 2 *
      ((2 * Real.pi) ^ (-(n : ℝ) / 2) * M) ^ 2 * RawInputRealization.unitBallVolume n := rfl

/-- Exact nonzero phase matching for the constructed family. This uses the
literal quotient rescaling and makes no homogeneity assumption
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem bandKernelData_phase_dilate (j : Fin J) (p : P)
    (x : Euclidean n) (θ : Euclidean (n - 1)) :
    (D).phase (((j, p), (2 : ℝ) ^ j.val • θ), x) =
      (2 : ℝ) ^ j.val * rawPrimaryPhaseDifference (S p) (ζ p)
        (τ p * (2 : ℝ) ^ j.val) x θ :=
  RawInputDilation.rawPrimaryPhaseDifference_dilate _ _ (hτ₀ p) (by positivity) _ _

/-- The constructed family supplies the exact measured-amplitude equation
used by the normalized full-phase adapter
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem bandKernelData_amplitude_normalization (hn : 1 ≤ n)
    (j : Fin J) (p : P) (χ : ℝ) (x : Euclidean n) (θ : Euclidean (n - 1)) (i : Fin n) :
    (Real.sqrt (((2 : ℝ) ^ j.val) ^ (n - 1)) : ℂ) * (χ : ℂ) *
      (Real.sqrt ‖(2 : ℝ) ^ j.val • θ‖ : ℂ) * (D).mask ((2 : ℝ) ^ j.val • θ) *
      (D).amplitude (((j, p), (2 : ℝ) ^ j.val • θ), x) i =
    (normalOperatorScale n ((2 : ℝ) ^ j.val) : ℂ) *
      normalizedMeasuredAmplitude A ζ τ d j.val p χ x θ i :=
  measuredBandAmplitude_normalization hn A ζ τ d j p χ x θ i

variable [FirstCountableTopology P] [LocallyCompactSpace P]

/-- The SAME smooth kernel reassembles from the two sharp input pieces.
The resulting integral has no sharp indicator, before the full normal calculus
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem bandKernelData_wideOperator_apply (j : Fin J) (p : P) (f : WideBandL2 n j.val) :
    MeanNormalBound.wideBandKernelOperator D j.val (j, p) f =
      ∫ η, f η • (D).column (j, p) η := by
  apply MeanNormalBound.wideBandKernelOperator_apply_of_radialBand D j.val (j, p)
    (fun η x ↦ ((2 * Real.pi) ^ (-(n : ℝ) / 2) : ℝ) •
      A p x (ζ p + τ p • η))
  intro η x
  change measuredBandAmplitude A ζ τ (((j, p), η), x) = _
  simp only [measuredBandAmplitude, Complex.ofReal_mul, mul_smul]
  rw [smul_comm]
  rfl

end Constructed

end JanetCartan.Sampling.RawKernel
