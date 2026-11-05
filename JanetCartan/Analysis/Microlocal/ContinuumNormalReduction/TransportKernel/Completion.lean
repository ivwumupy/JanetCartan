module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Diagonal
import Mathlib.Algebra.Order.Star.Real
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.FrequencyBounds.Completion

/-!
# Smooth kernel of the reflected bounded-frequency correction

The completion following `app:ch_background:eq:bg-symbol` is applied to the
literal two-position spectator amplitude. Reflection retains both detector
weights and the normalization `2 (2π)^n`. Primitive smoothness and the two
support buffers produce a smooth correction, supported in a fixed frequency
ball. Its actual Lebesgue kernel and its conjugate transpose are smooth.
These assertions do not assume boundedness of an unregularized carrier, and
do not assert uniform tame Sobolev estimates for this correction.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius ComplexConjugate

namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction
variable {n N : ℕ}

local instance : TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

/-- Smooth completion of the normalized reflected full amplitude, retaining
both positions and the spectator integral (`app:ch_background:eq:bg-real-symbol`). -/
def completedReflectedAmplitude
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (p : TransportSymbol.Variables n) : Matrix (Fin n) (Fin n) ℝ :=
  (2 * (2 * Real.pi) ^ n) •
    (TransportSymbol.completedAmplitude a J u Ω K p +
      TransportSymbol.completedAmplitude a J u Ω K (p.1, p.2.1, -p.2.2))

/-- The actual discrepancy, without deleting the low-frequency region or
altering the angular mask (`app:ch_background:eq:bg-symbol`). -/
def reflectedCompletionError
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (p : TransportSymbol.Variables n) : Matrix (Fin n) (Fin n) ℝ :=
  reflectedSymbolAmplitude a J u Ω K p - completedReflectedAmplitude a J u Ω K p

section Completion
variable (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))

/-- Reflection preserves the fixed completion's smoothness. The input is
proved from primitive regularity in `completedAmplitude_contDiff`
(`app:ch_background:eq:bg-real-symbol`). -/
theorem completedReflectedAmplitude_contDiff
    (hh : ContDiffOn ℝ ∞
      (TransportSymbol.amplitude (TransportSymbol.homogeneousCoefficients a) J u Ω K)
      {p | p.2.2 ≠ 0}) :
    ContDiff ℝ ∞ (completedReflectedAmplitude a J u Ω K) := by
  have hc := TransportSymbol.completedAmplitude_contDiff a J u Ω K hh
  exact (hc.add (hc.comp
    (contDiff_fst.prodMk (contDiff_snd.fst.prodMk contDiff_snd.snd.neg)))).const_smul _

/-- The discrepancy is smooth, including at zero frequency. Both smoothness
inputs are consequences of primitive chart buffers in the assembly theorem below
(`app:ch_background:eq:bg-symbol`). -/
theorem reflectedCompletionError_contDiff
    (ha : ContDiff ℝ ∞ (TransportSymbol.amplitude a J u Ω K))
    (hh : ContDiffOn ℝ ∞
      (TransportSymbol.amplitude (TransportSymbol.homogeneousCoefficients a) J u Ω K)
      {p | p.2.2 ≠ 0}) :
    ContDiff ℝ ∞ (reflectedCompletionError a J u Ω K) := by
  exact ((ha.add (ha.comp
    (contDiff_fst.prodMk (contDiff_snd.fst.prodMk contDiff_snd.snd.neg)))).const_smul _).sub
      (completedReflectedAmplitude_contDiff a J u Ω K hh)

/-- The reflected discrepancy vanishes above the same fixed physical frequency
as the complex discrepancy; reflection requires no evenness of the mask
(`app:ch_background:eq:bg-symbol`). -/
theorem reflectedCompletionError_eq_zero_of_large_frequency
    (hhigh : ∀ r : ℝ, 2 ≤ r → a.high r = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (p : TransportSymbol.Variables n) (hp : max 2 (2 * C) ≤ ‖p.2.2‖) :
    reflectedCompletionError a J u Ω K p = 0 := by
  unfold reflectedCompletionError reflectedSymbolAmplitude completedReflectedAmplitude
  rw [TransportSymbol.amplitude_eq_completed_of_large_frequency a J u Ω K
      hhigh hC hcomparison p hp,
    TransportSymbol.amplitude_eq_completed_of_large_frequency a J u Ω K
      hhigh hC hcomparison (p.1, p.2.1, -p.2.2) (by simpa using hp), sub_self]

/-- All derivatives of the actual reflected correction retain the same bounded
frequency support (`app:ch_background:eq:bg-symbol`). -/
theorem tsupport_iteratedFDeriv_reflectedCompletionError_subset
    (hhigh : ∀ r : ℝ, 2 ≤ r → a.high r = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖) (r : ℕ) :
    tsupport (iteratedFDeriv ℝ r (reflectedCompletionError a J u Ω K)) ⊆
      {p | ‖p.2.2‖ ≤ max 2 (2 * C)} := by
  apply (tsupport_iteratedFDeriv_subset r).trans
  apply closure_minimal _ (isClosed_le continuous_snd.snd.norm continuous_const)
  intro p hp
  by_contra hn
  exact hp (reflectedCompletionError_eq_zero_of_large_frequency a J u Ω K
    hhigh hC hcomparison p (not_le.mp hn).le)

/-- The literal bounded-frequency kernel with the physical Lebesgue measure
and normalized PDO prefactor (`app:ch_background:eq:bg-symbol`). -/
def completionErrorKernel (i j : Fin n) (x y : Euclidean n) : ℂ :=
  ((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ k,
    NormalComparison.oscillatoryFactor 1 (inner ℝ (x - y) k) *
      (reflectedCompletionError a J u Ω K (x, y, k) i j : ℂ)

private theorem errorIntegrand_contDiff (i j : Fin n)
    (he : ContDiff ℝ ∞ (reflectedCompletionError a J u Ω K)) :
    ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ (p.1.1 - p.1.2) p.2) *
        (reflectedCompletionError a J u Ω K (p.1.1, p.1.2, p.2) i j : ℂ)) := by
  have hphase : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      NormalComparison.oscillatoryFactor 1 (inner ℝ (p.1.1 - p.1.2) p.2)) := by
    unfold NormalComparison.oscillatoryFactor
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul ((contDiff_fst.fst.sub contDiff_fst.snd).inner ℝ contDiff_snd)))).cexp
  exact hphase.mul (Complex.ofRealCLM.contDiff.comp (((realMatrixEntry i j).contDiff.comp he).comp
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))))

/-- Absolute frequency integrability of the actual correction follows from
its smoothness and the fixed geometric frequency comparison. No integrability
of the homogeneous amplitude at infinity is assumed
(`app:ch_background:eq:bg-symbol`). -/
theorem integrable_completionErrorKernel_integrand
    (he : ContDiff ℝ ∞ (reflectedCompletionError a J u Ω K))
    (hhigh : ∀ r : ℝ, 2 ≤ r → a.high r = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (i j : Fin n) (x y : Euclidean n) :
    Integrable (fun k ↦ NormalComparison.oscillatoryFactor 1 (inner ℝ (x - y) k) *
      (reflectedCompletionError a J u Ω K (x, y, k) i j : ℂ)) := by
  apply ((errorIntegrand_contDiff a J u Ω K i j he).continuous.comp
    (show Continuous (fun k : Euclidean n ↦ ((x, y), k)) from
      continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean n) (max 2 (2 * C)))
  intro k hk
  have hk' : max 2 (2 * C) ≤ ‖k‖ := (not_le.mp (by simpa using hk)).le
  simp [reflectedCompletionError_eq_zero_of_large_frequency a J u Ω K hhigh hC
    hcomparison (x, y, k) hk']

/-- The actual correction kernel is jointly smooth in its two physical
positions. Domination and differentiation of the integral follow from the
fixed compact frequency ball (`app:ch_background:eq:bg-symbol`). -/
theorem completionErrorKernel_contDiff
    (he : ContDiff ℝ ∞ (reflectedCompletionError a J u Ω K))
    (hhigh : ∀ r : ℝ, 2 ≤ r → a.high r = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖) (i j : Fin n) :
    ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦
      completionErrorKernel a J u Ω K i j p.1 p.2) := by
  let B := Metric.closedBall (0 : Euclidean n) (max 2 (2 * C))
  have hB : IsCompact B := isCompact_closedBall _ _
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hB.measure_lt_top.ne
  have hid := errorIntegrand_contDiff a J u Ω K i j he
  have hc := contDiffOn_compactParameterIntegral (μ := (volume : Measure (Euclidean n)))
    (K := B) isOpen_univ isOpen_univ hB (subset_univ B) hid.contDiffOn
  have heq (x y : Euclidean n) :
      (∫ k in B, NormalComparison.oscillatoryFactor 1 (inner ℝ (x - y) k) *
        (reflectedCompletionError a J u Ω K (x, y, k) i j : ℂ)) =
      ∫ k, NormalComparison.oscillatoryFactor 1 (inner ℝ (x - y) k) *
        (reflectedCompletionError a J u Ω K (x, y, k) i j : ℂ) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro k hk
    have hk' : max 2 (2 * C) ≤ ‖k‖ := (not_le.mp (by simpa [B] using hk)).le
    simp [reflectedCompletionError_eq_zero_of_large_frequency a J u Ω K hhigh hC
      hcomparison (x, y, k) hk']
  have hc' := contDiffOn_univ.mp hc
  simp_rw [heq] at hc'
  exact contDiff_const.mul hc'

/-- The literal conjugate-transpose correction kernel has the same qualitative
smoothness. This is the adjoint kernel, not an assumed Sobolev estimate
(`app:ch_background:eq:bg-real-symbol`). -/
theorem completionErrorKernel_adjoint_contDiff
    (he : ContDiff ℝ ∞ (reflectedCompletionError a J u Ω K))
    (hhigh : ∀ r : ℝ, 2 ≤ r → a.high r = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖) (i j : Fin n) :
    ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦
      conj (completionErrorKernel a J u Ω K j i p.2 p.1)) := by
  have hswap : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦
      completionErrorKernel a J u Ω K j i p.2 p.1) := by
    exact (completionErrorKernel_contDiff a J u Ω K he hhigh hC hcomparison j i).comp
      (f := fun p : Euclidean n × Euclidean n ↦ (p.2, p.1))
      (contDiff_snd.prodMk contDiff_fst)
  exact (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp hswap

/-- The completed principal diagonal is exactly the fixed cutoff times the
reflected homogeneous diagonal. This identity retains both angular weights
(`app:ch_background:eq:bg-real-symbol`). -/
theorem completedReflectedAmplitude_diagonal (x k : Euclidean n) :
    completedReflectedAmplitude a J u Ω K (x, x, k) =
      TransportSymbol.completionCutoff k • reflectedDiagonalMatrix
        (TransportSymbol.homogeneousDiagonal a J u Ω K x) k := by
  ext i j
  simp only [completedReflectedAmplitude, TransportSymbol.completedAmplitude,
    reflectedDiagonalMatrix, TransportSymbol.homogeneousDiagonal,
    TransportSymbol.completionCutoff, norm_neg, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul]
  ring

/-- Completion preserves the positive comparison, including at zero where the
completion cutoff vanishes (`app:ch_background:eq:bg-real-symbol`). -/
theorem completedReflectedAmplitude_diagonal_comparison (x k : Euclidean n)
    (hpos : (TransportSymbol.homogeneousDiagonal a J u Ω K x (-k)).PosSemidef) :
    (completedReflectedAmplitude a J u Ω K (x, x, k) -
      TransportSymbol.completionCutoff k • ((2 * (2 * Real.pi) ^ n) •
        TransportSymbol.homogeneousDiagonal a J u Ω K x k)).PosSemidef := by
  rw [completedReflectedAmplitude_diagonal, ← smul_sub]
  exact (reflectedDiagonalMatrix_sub_posSemidef _ k hpos).smul
    (Real.smoothTransition.nonneg _)

/-- The correction kernel agrees exactly with the Fourier convention of the
shared PDO calculus, not merely up to a normalization
(`app:ch_background:eq:bg-symbol`). -/
theorem completionErrorKernel_eq_amplitudeKernel (i j : Fin n) (x y : Euclidean n) :
    completionErrorKernel a J u Ω K i j x y =
      Pseudodifferential.amplitudeKernel (fun x y ξ ↦
        (reflectedCompletionError a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) x y :=
  (amplitudeKernel_eq_physicalFrequency_integral (fun x y k ↦
    (reflectedCompletionError a J u Ω K (x, y, k) i j : ℂ)) x y).symm

end Completion
/-- Primitive assembly of the reflected correction. The smoothness inputs to
`completionErrorKernel_contDiff` and its adjoint version are discharged using
primitive regularity and the high-cutoff and homogeneous conic support buffers.
The parent phase-chart construction supplies these buffers and frequency
comparison; none of the premises is a kernel regularity or symbol estimate.
Source: `app:ch_background:eq:bg-symbol` and `app:ch_background:eq:bg-real-symbol`. -/
theorem completionErrorKernel_of_primitive_inputs
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (F : TransportSymbol.InputVariables n → TransportSymbol.Variables n × Euclidean 2)
    {Ω : Set (TransportSymbol.Variables n × Euclidean 2)}
    {W Lhi Lhom : Set (TransportSymbol.InputVariables n)}
    (hΩ : IsOpen Ω) (h : TransportSymbol.PrimitiveRegularity a J W)
    (hu : ContDiffOn ℝ ∞ u Ω)
    (hmap : MapsTo (TransportSymbol.inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, F (TransportSymbol.inverseCoordinates u p) = p)
    (hshi : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ Lhi)
    (hclosed : IsClosed (F '' Lhi)) (hbufferhi : F '' Lhi ⊆ Ω)
    (hshom : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Lhom)
    (hbufferhom : closure (F '' Lhom) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω)
    {K : Set (Euclidean 2)} (hK : IsCompact K)
    (hhigh : ∀ r : ℝ, 2 ≤ r → a.high r = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖) :
    ContDiff ℝ ∞ (reflectedCompletionError a J u Ω K) ∧
    (∀ r : ℕ, tsupport (iteratedFDeriv ℝ r (reflectedCompletionError a J u Ω K)) ⊆
      {p | ‖p.2.2‖ ≤ max 2 (2 * C)}) ∧
    ∀ i j : Fin n,
      ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦
        completionErrorKernel a J u Ω K i j p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦
        conj (completionErrorKernel a J u Ω K j i p.2 p.1)) := by
  have ha := TransportSymbol.amplitude_contDiff a J u F hΩ h hu hmap hright
    hshi hclosed hbufferhi hK
  have hh := TransportSymbol.homogeneousAmplitude_contDiffOn_punctured a J u F hΩ h hu
    hmap hright hshom hbufferhom hK
  have he := reflectedCompletionError_contDiff a J u Ω K ha hh
  exact ⟨he, tsupport_iteratedFDeriv_reflectedCompletionError_subset a J u Ω K hhigh hC
    hcomparison, fun i j ↦
      ⟨completionErrorKernel_contDiff a J u Ω K he hhigh hC hcomparison i j,
       completionErrorKernel_adjoint_contDiff a J u Ω K he hhigh hC hcomparison i j⟩⟩

end JanetCartan.ContinuumRow.TransportKernel
