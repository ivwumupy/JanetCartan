module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.SymbolCancellation

/-!
# Physical Fourier identities for the scalar identity defect

The principal scalar symbols have the physical normalization already used by
`Graph.KernelLimits.channelFourierTransform`. The identities below retain the
source multiplication before Fourier transformation. In particular a physical
cutoff of an annular datum is not treated as band limited.

Consumers: the principal and terminal defect estimates in
`app:ch_regular:eq:chain-tail` and `app:ch_regular:eq:resolved-angular-tail`.
These are test-level identities; passage to the bounded physical PDO and the
quantitative estimates are separate obligations.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect

open FourierIntegral FiniteChain.Graph FiniteChain.Graph.KernelLimits

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => Fin r → ℂ
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The source mask stays inside the literal left-quantized scalar PDO.
No integrability assumption is needed to move the constant output and scalar
factors across the source-first Bochner integrals. Consumer: recovery of the
full identity subtraction in `app:ch_regular:eq:chain-tail`. -/
theorem graphOperator_masked_scalar_eq_leftLocalizer
    (a : LocalizerSymbol n) (χout χsource : E → ℝ) (g : E → V) (x : E) :
    graphOperator (fun x ξ ↦ inner ℝ x ξ)
      (fun x y ξ ↦ ((χout x * χsource y * a (x, ξ) : ℝ) : ℂ) • (1 : Mat)) g x =
        (χout x : ℂ) • leftLocalizer 1 a (fun y ↦ (χsource y : ℂ) • g y) x := by
  simp only [graphOperator, leftLocalizer, inv_one, one_smul,
    Matrix.smul_mulVec, Matrix.one_mulVec, Complex.ofReal_mul, smul_smul]
  have he (ξ y : E) :
      graphOscillation (fun a b : E ↦ inner ℝ a b) x y ξ *
        ((χout x : ℂ) * (χsource y : ℂ) * (a (x, ξ) : ℂ)) =
      (χout x : ℂ) * (graphOscillation (fun a b : E ↦ inner ℝ a b) x y ξ *
        ((a (x, ξ) : ℂ) * (χsource y : ℂ))) := by ring
  simp_rw [he, mul_smul, integral_smul]
  rw [smul_comm (((2 * Real.pi) ^ n : ℂ)⁻¹) (χout x : ℂ)]

/-- Literal reversal of a real scalar frequency symbol reverses both physical
masks. This is the test action of the Hilbert adjoint amplitude, not the
transpose of a left symbol with its masks left in place. Consumer: the adjoint
terminal defect in `app:ch_regular:lem:finite-chain`. -/
theorem reverseGraphOperator_masked_scalarFrequency_eq_leftLocalizer
    (b : E → ℝ) (χout χsource : E → ℝ) (g : E → V) (x : E) :
    reverseGraphOperator (fun x ξ ↦ inner ℝ x ξ)
      (fun y z ξ ↦ (((χout y * χsource z * b ξ : ℝ) : ℂ) • (1 : Mat)).conjTranspose)
      g x =
        (χsource x : ℂ) • leftLocalizer 1 (fun p ↦ b p.2)
          (fun y ↦ (χout y : ℂ) • g y) x := by
  rw [← graphOperator_masked_scalar_eq_leftLocalizer (fun p ↦ b p.2) χsource χout g x]
  unfold reverseGraphOperator graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [] with y
  have hp : star (graphOscillation (fun a b : E ↦ inner ℝ a b) y x ξ) =
      graphOscillation (fun a b : E ↦ inner ℝ a b) x y ξ := by
    simp only [graphOscillation, Complex.star_def, ← Complex.exp_conj,
      map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    push_cast
    ring
  simp only [hp, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Complex.star_def, Complex.conj_ofReal, mul_comm (χout y) (χsource x)]

/-- Fourier inversion identifies the scalar PDO minus the FULL identity.
The Fourier datum is the original source-multiplied test field. The physical
defect `χout * χsource - 1` remains explicitly, even when the frequency symbol
is one. The primitive inputs are the original smooth compact source mask and
the scalar order-zero bound, supplied by the actual finite masks and symbol
budgets. Consumer: the terminal estimate in
`app:ch_regular:eq:resolved-angular-tail`. -/
theorem masked_scalar_identity_defect_eq_fourier
    (a : LocalizerSymbol n) (χout χsource : E → ℝ)
    (hs : ContDiff ℝ ∞ χsource) (hsc : HasCompactSupport χsource)
    (g : SchwartzMap E V) (x : E)
    (ha : Continuous (fun ξ ↦ a (x, ξ))) (B : ℝ) (hB : ∀ ξ, |a (x, ξ)| ≤ B) :
    let gs := SchwartzMap.smulLeftCLM V (fun y ↦ (χsource y : ℂ)) g
    graphOperator (fun x ξ ↦ inner ℝ x ξ)
      (fun x y ξ ↦ ((χout x * χsource y * a (x, ξ) : ℝ) : ℂ) • (1 : Mat)) g x - g x =
      -(χout x : ℂ) • (∫ ξ,
        (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
          ((1 - a (x, ξ) : ℝ) : ℂ)) • channelFourierTransform gs ξ) +
        ((χout x * χsource x - 1 : ℝ) : ℂ) • g x := by
  intro gs
  have hst : (fun y ↦ (χsource y : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp (hsc.hasTemperateGrowth hs)
  have hgs (y : E) : gs y = (χsource y : ℂ) • g y :=
    SchwartzMap.smulLeftCLM_apply_apply hst g y
  have hgseq : (gs : E → V) = fun y ↦ (χsource y : ℂ) • g y := funext hgs
  rw [graphOperator_masked_scalar_eq_leftLocalizer, ← hgseq]
  have hid := complementary_channelFourierIntegral 1 a gs x
    (by simpa only [inv_one, one_smul] using ha) B
    (by simpa only [inv_one, one_smul] using hB)
  simp only [inv_one, one_smul] at hid
  rw [hid]
  simp only [smul_sub, neg_smul, hgs, smul_smul, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_one, sub_smul, one_smul, neg_mul]
  abel

/-- Forward and literal reverse terminal actions have the same Fourier
defect formula, with the physical masks in the correct reversed positions.
The source regularity here is regularity of the original output mask, exactly
as required for the adjoint. Consumer: the adjoint terminal estimate in
`app:ch_regular:eq:chain-tail`. -/
theorem reverse_masked_scalarFrequency_identity_defect_eq_fourier
    (b : E → ℝ) (χout χsource : E → ℝ)
    (ho : ContDiff ℝ ∞ χout) (hoc : HasCompactSupport χout)
    (g : SchwartzMap E V) (x : E) (hb : Continuous b)
    (B : ℝ) (hB : ∀ ξ, |b ξ| ≤ B) :
    let go := SchwartzMap.smulLeftCLM V (fun y ↦ (χout y : ℂ)) g
    reverseGraphOperator (fun x ξ ↦ inner ℝ x ξ)
      (fun y z ξ ↦ (((χout y * χsource z * b ξ : ℝ) : ℂ) • (1 : Mat)).conjTranspose)
      g x - g x =
      -(χsource x : ℂ) • (∫ ξ,
        (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
          ((1 - b ξ : ℝ) : ℂ)) • channelFourierTransform go ξ) +
        ((χsource x * χout x - 1 : ℝ) : ℂ) • g x := by
  intro go
  rw [reverseGraphOperator_masked_scalarFrequency_eq_leftLocalizer,
    ← graphOperator_masked_scalar_eq_leftLocalizer (fun p ↦ b p.2) χsource χout g x]
  exact masked_scalar_identity_defect_eq_fourier (fun p ↦ b p.2)
    χsource χout ho hoc g x hb B hB

open RegularSector.FiniteMasks FourierIntegral.LowBounds.FrequencyCutoff

/-- The concrete finite masks give the exact forward or literal reverse test
action of their full principal identity defect. The single fixed low bump and
the physical identity discrepancy are explicit summands. All regularity and
boundedness inputs of Fourier inversion are discharged from `ActualMaskFamily`.
This identifies the scalar finite-mask action, without silently identifying
an arbitrary sector operator with it. Consumer: the terminal construction in
`app:ch_regular:eq:resolved-angular-tail`. -/
theorem actualFamily_scalar_identity_defect_eq_fourier
    {d : ℕ} {Ω : Set (Euclidean (d + 1))} {center : Euclidean (d + 1)} {RQ M : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
    (f : ActualFamily.ActualMaskFamily Ω center RQ A₀ K M) (backward : Bool)
    (g : SchwartzMap (Euclidean (d + 1)) V) (x : Euclidean (d + 1)) :
    let χo := if backward then f.inputMask else f.outputMask
    let χs := if backward then f.outputMask else f.inputMask
    let gs := SchwartzMap.smulLeftCLM V (fun y ↦ (χs y : ℂ)) g
    let A := fun y z ξ ↦
      ((f.outputMask y * f.inputMask z *
        (∑ p, dilatedConicMask (f.angularMask p) f.radialThreshold ξ) : ℝ) : ℂ) •
          (1 : Mat)
    (if backward then reverseGraphOperator (fun y ξ ↦ inner ℝ y ξ)
      (fun y z ξ ↦ (A y z ξ).conjTranspose) g x
    else graphOperator (fun y ξ ↦ inner ℝ y ξ) A g x) - g x =
      -(χo x : ℂ) • (∫ ξ,
        (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
          ((dilatedConicMask (fun η ↦ 1 - ∑ p, f.angularMask p η) f.radialThreshold ξ +
            physicalCutoff 0 (f.radialThreshold⁻¹ • ξ) : ℝ) : ℂ)) •
              channelFourierTransform gs ξ) +
        ((χo x * χs x - 1 : ℝ) : ℂ) • g x := by
  intro χo χs gs A
  have hb : Continuous (fun ξ ↦ ∑ p, dilatedConicMask (f.angularMask p) f.radialThreshold ξ) :=
    continuous_finsetSum _ (fun p _ ↦
      (contDiff_dilatedConicMask (f.angularMask_smooth p) f.radialThreshold).continuous)
  have hB (ξ : Euclidean (d + 1)) :
      |∑ p, dilatedConicMask (f.angularMask p) f.radialThreshold ξ| ≤ 1 := by
    have h := actualFamily_sum_dilatedConicMask_mem_Icc f ξ
    simpa only [abs_of_nonneg h.1] using h.2
  have he (ξ : Euclidean (d + 1)) :
      1 - ∑ p, dilatedConicMask (f.angularMask p) f.radialThreshold ξ =
        dilatedConicMask (fun η ↦ 1 - ∑ p, f.angularMask p η) f.radialThreshold ξ +
          physicalCutoff 0 (f.radialThreshold⁻¹ • ξ) := by
    linarith [f.complete_partition ξ]
  cases backward
  · have h := masked_scalar_identity_defect_eq_fourier
      (fun p ↦ ∑ i, dilatedConicMask (f.angularMask i) f.radialThreshold p.2)
      f.outputMask f.inputMask f.inputMask_smooth f.inputMask_compact g x hb 1 hB
    simp only [he] at h
    simpa [χo, χs, gs, A] using h
  · have h := reverse_masked_scalarFrequency_identity_defect_eq_fourier
      (fun ξ ↦ ∑ i, dilatedConicMask (f.angularMask i) f.radialThreshold ξ)
      f.outputMask f.inputMask f.outputMask_smooth f.outputMask_compact g x hb 1 hB
    simp only [he] at h
    simpa [χo, χs, gs, A] using h

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
