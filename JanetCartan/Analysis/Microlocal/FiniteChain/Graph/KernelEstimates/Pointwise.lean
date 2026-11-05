module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.Support
public import JanetCartan.Analysis.Microlocal.Localization.Vector
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.HalfSpace.Scaling

/-!
# Zeroth-order pointwise decay of the literal joint graph integral

This is the undifferentiated comparable-frequency step of
`app:ch_regular:eq:chain-tail`, conditional on the exact joint gradient gap
produced by the buffered-localizer construction. The formula includes both
physical bases, three frequency measures, and the full matrix amplitude.
Identification with an operator composition and regularization limits are
separate obligations. Output derivatives and noncomparable shells require
additional estimates.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelEstimates
open FourierIntegral JanetCartan.Localization Retarded.HalfSpace
variable {n r : ℕ}

/-- The two physical and three normalized frequency measures in
`app:ch_regular:eq:joint-kernel-phase`. -/
def jointMeasure (n : ℕ) : Measure (JointVariables (Euclidean n)) :=
  ((volume : Measure (Euclidean n)).prod volume).prod
    ((volume : Measure (Euclidean n)).prod (volume.prod volume))

/-- The product of all five Lebesgue measures is Haar, as needed for
`app:ch_regular:eq:chain-tail` integration by parts. -/
instance jointMeasure_isAddHaarMeasure : (jointMeasure n).IsAddHaarMeasure := by
  let : ((volume : Measure (Euclidean n)).prod (volume : Measure (Euclidean n))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  let : ((volume : Measure (Euclidean n)).prod
      ((volume : Measure (Euclidean n)).prod (volume : Measure (Euclidean n)))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure _ _

/-- The joint support volume counts each physical and frequency carrier once
(`app:ch_regular:eq:chain-tail`). -/
theorem jointMeasure_real_jointCarrier (Kb : Set (Euclidean n × Euclidean n))
    (Kξ Kη Kζ : Set (Euclidean n)) :
    (jointMeasure n).real (jointCarrier Kb Kξ Kη Kζ) =
      ((volume : Measure (Euclidean n)).prod volume).real Kb *
        volume.real Kξ * volume.real Kη * volume.real Kζ := by
  simp only [jointMeasure, jointCarrier, measureReal_prod_prod]
  ring

/-- The three Euclidean Fourier normalizations of the localized graph kernel
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
def jointNormalization (n : ℕ) : ℝ := (((2 * Real.pi) ^ n)⁻¹) ^ 3

/-- Positivity of the Fourier normalization used in the pointwise bound
(`app:ch_regular:eq:chain-tail`). -/
theorem jointNormalization_nonneg (n : ℕ) : 0 ≤ jointNormalization n := by
  unfold jointNormalization
  positivity

/-- Explicit normalized regularized joint integral. The Jacobian `ρ^(3*n)`
counts all three frequency measures. This definition does not assert a
regularization identity or limit (`app:ch_regular:eq:joint-kernel-phase`). -/
def regularizedJointKernel (backward : Bool) (ρ : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  (jointNormalization n * ρ ^ (3 * n)) •
    ∫ p, phaseOscillation (ρ • jointPhase backward φ x y) p •
      jointAmplitude ρ A mi mo χA χo x y p ∂jointMeasure n

/-- Vector-valued scaled integration by parts, with the amplitude profile
already proved from its primitive factors. The coefficient bounds are derived
from the phase gap by `norm_vector_oscillatory_integral_le`; the constant has
no hidden dependence on the frequency or the grade scale
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_scaled_vector_integral_le
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K)
    (e : ι → E) (Fphase : E → ℝ) (a : E → F)
    (hF : ContDiffOn ℝ ∞ Fphase U) (ha : ContDiffOn ℝ ∞ a U)
    (hsU : tsupport a ⊆ U) (hsK : tsupport a ⊆ K)
    {δ G S L R : ℝ} (hδ : 0 < δ) (hS : 0 ≤ S) (hL : 0 ≤ L) (hR : 0 < R)
    (hgap : ∀ p ∈ U, δ ≤ phaseGradientSquare e Fphase p)
    (hupper : ∀ p ∈ U, ‖fderiv ℝ Fphase p‖ ≤ G)
    {P C : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j) (b q : ℕ)
    (hp : ∀ p ∈ tsupport a, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) Fphase p‖ ≤ P j * L ^ j)
    (hab : ∀ p ∈ tsupport a, ∀ j,
      ‖iteratedFDeriv ℝ j a p‖ ≤ S * C j * L ^ (j + b)) :
    ‖∫ p, phaseOscillation (R • Fphase) p • a p ∂μ‖ ≤
      (decayConstant e δ G P C q * μ.real K) * S * L ^ b * (L / R) ^ q := by
  have hFd p (hp : p ∈ U) : DifferentiableAt ℝ Fphase p :=
    (hF.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hsg p (hp : p ∈ U) : δ * R ^ 2 ≤ phaseGradientSquare e (R • Fphase) p := by
    rw [phaseGradientSquare_frequency e Fphase (hFd p hp)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hgap p hp) (sq_nonneg R)
  have hsu p (hp : p ∈ U) : ‖fderiv ℝ (R • Fphase) p‖ ≤ G * R := by
    rw [fderiv_const_smul (hFd p hp), norm_smul, Real.norm_of_nonneg hR.le]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hupper p hp) hR.le
  have hsp p (hp' : p ∈ tsupport a) j (hj : 1 ≤ j) :
      ‖iteratedFDeriv ℝ (j + 1) (R • Fphase) p‖ ≤ P j * R * L ^ j := by
    rw [iteratedFDeriv_const_smul_apply
      ((hF.contDiffAt (hU.mem_nhds (hsU hp'))).of_le (by simp)), norm_smul,
      Real.norm_of_nonneg hR.le]
    exact (mul_le_mul_of_nonneg_left (hp p hp' j hj) hR.le).trans_eq (by ring)
  have hsa p (hp' : p ∈ tsupport a) j :
      ‖iteratedFDeriv ℝ j a p‖ ≤ C j * (S * L ^ b * L ^ j) := by
    exact (hab p hp' j).trans_eq (by rw [pow_add]; ring)
  have hc : HasCompactSupport a := hK.of_isClosed_subset (isClosed_tsupport _) hsK
  have h := norm_vector_oscillatory_integral_le (μ := μ) hU e (R • Fphase) a q
    (hF.const_smul R) ha hsU hc hδ (mul_nonneg hS (pow_nonneg hL _)) hL hR
    hsg hsu hC hsp hsa
  have hD := decayConstant_nonneg e δ G P C hC q
  change ‖∫ p, phaseOscillation (R • Fphase) p • a p ∂μ‖ ≤
    (decayConstant e δ G P C q * ((S * L ^ b) * (L / R) ^ q)) *
      μ.real (tsupport a) at h
  calc
    _ ≤ (decayConstant e δ G P C q * ((S * L ^ b) * (L / R) ^ q)) *
        μ.real (tsupport a) := h
    _ ≤ (decayConstant e δ G P C q * ((S * L ^ b) * (L / R) ^ q)) * μ.real K := by
      apply mul_le_mul_of_nonneg_left (measureReal_mono hsK hK.measure_lt_top.ne)
      positivity
    _ = _ := by ring

/-- Pointwise Frobenius decay from primitive factor grades and the exact joint
gradient gap, for either literal orientation. The full symbol has arbitrary
real order `s` (including fixed negative orders). The fixed losses are
`C_A = s + 3*n` and `b = D.offset`, independent of `q`. This is the `m = 0`
prerequisite for the parent's L²-to-Hᵐ assembly, not the full operator estimate
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_regularizedJointKernel_le_of_primitive_grades
    {ι : Type*} [Fintype ι] (backward : Bool) {ρ L : ℝ}
    (hρ : 0 < ρ) (hL : 1 ≤ L) (s : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    {U K : Set (JointVariables (Euclidean n))}
    (D : AmplitudeProfiles) (ha : HasAmplitudeGrades D ρ (ρ ^ s) L A mi mo χA χo x y K)
    (hU : IsOpen U) (hK : IsCompact K)
    (hsU : tsupport (jointAmplitude ρ A mi mo χA χo x y) ⊆ U)
    (hsK : tsupport (jointAmplitude ρ A mi mo χA χo x y) ⊆ K)
    (e : ι → JointVariables (Euclidean n))
    (hφ : ContDiffOn ℝ ∞ (jointPhase backward φ x y) U)
    {δ G : ℝ} (hδ : 0 < δ)
    (hgap : ∀ p ∈ U, δ ≤ phaseGradientSquare e (jointPhase backward φ x y) p)
    (hupper : ∀ p ∈ U, ‖fderiv ℝ (jointPhase backward φ x y) p‖ ≤ G)
    (P : ℕ → ℝ)
    (hp : ∀ p ∈ tsupport (jointAmplitude ρ A mi mo χA χo x y), ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (jointPhase backward φ x y) p‖ ≤ P j * L ^ j)
    (q : ℕ) :
    ‖regularizedJointKernel backward ρ φ A mi mo χA χo x y‖ ≤
      (jointNormalization n * decayConstant e δ G P D.productProfile q *
        (jointMeasure n).real K) * ρ ^ (s + (3 * n : ℕ)) * L ^ D.offset * (L / ρ) ^ q := by
  have h := norm_scaled_vector_integral_le (μ := jointMeasure n) hU hK e
    (jointPhase backward φ x y) (jointAmplitude ρ A mi mo χA χo x y)
    hφ ha.contDiff_jointAmplitude.contDiffOn hsU hsK hδ
    (Real.rpow_pos_of_pos hρ s).le (zero_le_one.trans hL) hρ hgap hupper
    D.productProfile_nonneg D.offset q hp
    (fun p hp' j => ha.norm_iteratedFDeriv_jointAmplitude_le hL p (hsK hp') j)
  unfold regularizedJointKernel
  rw [norm_smul, Real.norm_of_nonneg
    (mul_nonneg (jointNormalization_nonneg n) (pow_nonneg hρ.le _))]
  apply (mul_le_mul_of_nonneg_left h
    (mul_nonneg (jointNormalization_nonneg n) (pow_nonneg hρ.le _))).trans_eq
  rw [Real.rpow_add hρ, Real.rpow_natCast]
  ring

end JanetCartan.FiniteChain.Graph.KernelEstimates
