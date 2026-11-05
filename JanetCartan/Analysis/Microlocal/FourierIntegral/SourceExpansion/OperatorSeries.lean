module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.JointJets
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.Modulation
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.OperatorSeries

/-!
# The bounded source expansion and its actual Hilbert adjoint

The operator-series step in `app:ch_regular_base:thm:actual-calculus`, Step 1.
The sole analytic operator input is the low graph estimate for the individual
source-independent coefficients, supplied by the phase/normal construction.
Coefficient decay and multiplier bounds are proved from the full amplitude.
This file does not assume a full-amplitude graph estimate.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SourceExpansion
open AmplitudeBound
variable {n r : ℕ} {R ℓ : ℝ}
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n))

/-- The bounded source series on the original Euclidean L² space, for
`app:ch_regular_base:thm:actual-calculus`, Step 1. Its identification with the
literal full graph is proved separately, after specifying coefficient realizations. -/
def sourceOperatorSeries (β : SourceCutoff n R ℓ) (C : (Fin n → ℤ) → H →L[ℂ] H) :
    H →L[ℂ] H :=
  amplitudeOperator (fun _ ↦ ContinuousLinearMap.id ℂ H) (sourceModulation β) C

/-- The low constant for the full source expansion. The reserve `n+2` and this
constant are independent of the requested joint order `μ`
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
def sourceOperatorConstant (n r : ℕ) (ℓ G : ℝ) : ℝ :=
  G * ((r : ℝ) ^ 2 * coefficientConstant n (lowReserve n) ℓ) *
    ∑' k : Fin n → ℤ, decayWeight (lowReserve n) k

section Bounds
variable (hn : 0 < n) (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
  (A : FullAmplitude n r)
  (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
  (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n × Euclidean n ↦
    A p.1 p.2.1 p.2.2))
  (μ : ℕ) {B : ℝ} (hb : HasFullSourceSymbolBound A (μ + lowReserve n) B)
  (β : SourceCutoff n R ℓ)
  (C : (Fin n → ℤ) →
    Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n)) →L[ℂ]
    Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n))) (G : ℝ)
  (hgraph : ∀ k b, HasCoefficientSymbolBound (matrixCoefficient ℓ A k) μ b →
    ‖C k‖ ≤ G * b)
include hn hℓ hR hs hA hb hgraph

/-- Source-independent low graph bounds applied to the actual coefficient jets;
consumer: the full low bound in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem norm_sourceCoefficientOperator_le (k : Fin n → ℤ) :
    ‖C k‖ ≤ G * ((r : ℝ) ^ 2 * coefficientConstant n (lowReserve n) ℓ * B *
      decayWeight (lowReserve n) k) :=
  hgraph k _ (hasCoefficientSymbolBound_matrixCoefficient_lowReserve hn hℓ hR A hs hA μ hb k)

/-- Absolute operator-norm convergence follows from the fixed total derivative
budget, not from a full graph bound (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem summable_norm_sourceOperatorTerm :
    Summable (fun k ↦ ‖(C k).comp (sourceModulation β k)‖) := by
  simpa only [modulatedTerm, ContinuousLinearMap.id_comp] using
    summable_norm_modulatedTerm (fun _ ↦ ContinuousLinearMap.id ℂ H) (sourceModulation β) C
      (fun k ↦ G * ((r : ℝ) ^ 2 * coefficientConstant n (lowReserve n) ℓ * B *
        decayWeight (lowReserve n) k))
      (fun _ ↦ ContinuousLinearMap.norm_id_le) (norm_sourceModulation_le β)
      (norm_sourceCoefficientOperator_le hn hℓ hR A hs hA μ hb C G hgraph)
      (((summable_decayWeight_lowReserve n).mul_left _).mul_left _)

/-- The exact bounded source series converges in operator norm
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem hasSum_sourceOperatorTerm :
    HasSum (fun k ↦ (C k).comp (sourceModulation β k)) (sourceOperatorSeries β C) := by
  simpa only [sourceOperatorSeries, amplitudeOperator, modulatedTerm,
    ContinuousLinearMap.id_comp] using
    (summable_norm_sourceOperatorTerm hn hℓ hR A hs hA μ hb β C G hgraph).of_norm.hasSum

/-- The full low bound from exactly `μ + (n+2)` full mixed derivatives;
all original cutoff derivatives remain in `A`
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem norm_sourceOperatorSeries_le :
    ‖sourceOperatorSeries β C‖ ≤ sourceOperatorConstant n r ℓ G * B := by
  have h := norm_amplitudeOperator_le (fun _ ↦ ContinuousLinearMap.id ℂ H)
    (sourceModulation β) C
    (fun k ↦ G * ((r : ℝ) ^ 2 * coefficientConstant n (lowReserve n) ℓ * B *
      decayWeight (lowReserve n) k))
    (fun _ ↦ ContinuousLinearMap.norm_id_le) (norm_sourceModulation_le β)
    (norm_sourceCoefficientOperator_le hn hℓ hR A hs hA μ hb C G hgraph)
    (((summable_decayWeight_lowReserve n).mul_left _).mul_left _)
  simp only [tsum_mul_left] at h
  change ‖sourceOperatorSeries β C‖ ≤ _ at h
  convert h using 1
  unfold sourceOperatorConstant
  ring

/-- Taking the actual Hilbert adjoint reverses the factors in every summand.
The adjoint series converges in operator norm, with no separately chosen reverse
operator (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem hasSum_sourceOperatorTerm_adjoint :
    HasSum (fun k ↦ (sourceModulation β k).adjoint.comp (C k).adjoint)
      (sourceOperatorSeries β C).adjoint := by
  simpa only [Function.comp_def, ContinuousLinearMap.adjoint_comp] using
    (hasSum_sourceOperatorTerm hn hℓ hR A hs hA μ hb β C G hgraph).map
      ContinuousLinearMap.adjoint ContinuousLinearMap.adjoint.continuous

/-- The literal Hilbert adjoint has the same low source-series estimate
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem norm_sourceOperatorSeries_adjoint_le :
    ‖(sourceOperatorSeries β C).adjoint‖ ≤ sourceOperatorConstant n r ℓ G * B := by
  rw [LinearIsometryEquiv.norm_map]
  exact norm_sourceOperatorSeries_le hn hℓ hR A hs hA μ hb β C G hgraph

/-- Removing the same frequency regularization in each source-independent graph
commutes with the full source sum. Only coefficient-wise strong convergence is
required; the full graph convergence is deduced
(`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem tendsto_sourceOperatorSeries_apply {α : Type*} {l : Filter α}
    (Creg : α → (Fin n → ℤ) → H →L[ℂ] H)
    (hreg : ∀ j k b, HasCoefficientSymbolBound (matrixCoefficient ℓ A k) μ b →
      ‖Creg j k‖ ≤ G * b)
    (hlim : ∀ k u, Tendsto (fun j ↦ Creg j k u) l (𝓝 (C k u))) (u : H) :
    Tendsto (fun j ↦ sourceOperatorSeries β (Creg j) u) l
      (𝓝 (sourceOperatorSeries β C u)) := by
  exact tendsto_amplitudeOperator_apply (fun _ ↦ ContinuousLinearMap.id ℂ H)
    (sourceModulation β) C Creg
    (fun k ↦ G * ((r : ℝ) ^ 2 * coefficientConstant n (lowReserve n) ℓ * B *
      decayWeight (lowReserve n) k))
    (fun _ ↦ ContinuousLinearMap.norm_id_le) (norm_sourceModulation_le β)
    (norm_sourceCoefficientOperator_le hn hℓ hR A hs hA μ hb C G hgraph)
    (((summable_decayWeight_lowReserve n).mul_left _).mul_left _)
    (fun j ↦ norm_sourceCoefficientOperator_le hn hℓ hR A hs hA μ hb (Creg j) G (hreg j))
    hlim u

end Bounds
end JanetCartan.FourierIntegral.SourceExpansion
