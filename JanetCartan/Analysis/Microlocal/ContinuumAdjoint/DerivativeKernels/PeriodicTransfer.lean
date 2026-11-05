module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.PeriodicTransfer.Localization
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SobolevExtension.Limits

/-!
# Periodic input transfer for the raw carrier adjoint

For `app:ch_background:prop:bg-adjoint`, transfer the Euclidean estimate supplied
by `exists_literalCarrierAdjoint_chart_raw_bound` to the actual periodic vector
Sobolev space. A fixed smooth extension handles smooth inputs; smooth Fourier
approximation and the physical Fourier Fatou theorem handle every input,
including order zero. The raw norm retains the actual partial radian inverse.

The two Euclidean premises must both be instantiated by the parent construction.
This module proves domain transfer, not unconditional existence of that
construction. Its constant is chosen from the buffered source box and order
before the operator, carrier data, or high budget.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow CarrierSobolev Pseudodifferential Pseudodifferential.DifferentialChart
variable {n N : ℕ}

private theorem periodicCarrierOperator_smooth_raw_bound
    {r : ℝ} (ψ : SourceCutoff n r) (s : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hext : ∀ (u : Torus n → EuclideanSpace ℂ (Fin n)) (hu : IsSmoothPeriodic u),
      vectorFourierSobolevNorm s (periodicVectorExtension ψ hu) ≤
        B * ‖PeriodicSobolevSpace.ofSmooth s u hu‖)
    (d : CarrierData n N) {K : Set (Euclidean n)} (hK : K ⊆ chartBox r)
    (hchart : d.outputChart = torusChart K)
    (U : EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ] CarrierL2 n)
    (hU : ∀ f, U f =ᵐ[carrierMeasure n] carrierAdjointIntegral d
      (fun x ↦ f (centeredTorusRepresentative x)))
    (C H : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hbound : ∀ f, MemVectorFourierSobolev s f → MemRawSobolev s (U f) ∧
      rawSobolevNorm s (U f) ≤ C * (vectorFourierSobolevNorm s f + H * ‖f‖))
    (u : Torus n → EuclideanSpace ℂ (Fin n)) (hu : IsSmoothPeriodic u) :
    MemRawSobolev s (periodicCarrierOperator U
      (PeriodicSobolevSpace.toL2 s (PeriodicSobolevSpace.ofSmooth s u hu))) ∧
    rawSobolevNorm s (periodicCarrierOperator U
      (PeriodicSobolevSpace.toL2 s (PeriodicSobolevSpace.ofSmooth s u hu))) ≤
      B * C * (‖PeriodicSobolevSpace.ofSmooth s u hu‖ +
        H * ‖PeriodicSobolevSpace.toL2 s (PeriodicSobolevSpace.ofSmooth s u hu)‖) := by
  rw [periodicCarrierOperator_eq_extension ψ d hK hchart U hU hu _
    (PeriodicSobolevSpace.toL2_ofSmooth_ae s u hu)]
  obtain ⟨hm, hb⟩ := hbound _ (periodicVectorExtension_mem ψ hu s)
  refine ⟨hm, hb.trans ?_⟩
  have hnorm := norm_periodicVectorExtension_le ψ hu _
    (PeriodicSobolevSpace.toL2_ofSmooth_ae s u hu)
  calc
    _ ≤ C * (B * ‖PeriodicSobolevSpace.ofSmooth s u hu‖ +
        H * ‖PeriodicSobolevSpace.toL2 s (PeriodicSobolevSpace.ofSmooth s u hu)‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (hext u hu) (mul_le_mul_of_nonneg_left hnorm hH)) hC
    _ ≤ C * (B * ‖PeriodicSobolevSpace.ofSmooth s u hu‖ +
        B * (H * ‖PeriodicSobolevSpace.toL2 s (PeriodicSobolevSpace.ofSmooth s u hu)‖)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (le_mul_of_one_le_left (mul_nonneg hH (norm_nonneg _)) hB)) hC
    _ = _ := by ring

/-- Periodic-input transfer of the concrete raw adjoint estimate
(`app:ch_background:prop:bg-adjoint`). The fixed constant is selected before
all carrier data and budgets. The operator is exactly `U.comp toEuclidean`,
represents the original adjoint integral on every periodic L² datum, and has
the asserted raw bound on every periodic Hˢ datum, also when `s = 0`.

The parent supplies the representative and Euclidean Sobolev premises from
`exists_literalCarrierAdjoint_chart_raw_bound`, retaining its chart-point and
measurement-cutoff hypotheses. No periodic estimate is assumed here. -/
theorem exists_periodicCarrierOperator_raw_bound {r : ℝ} (hr : r < 1 / 2) (s : ℕ) :
    ∃ K_s : ℝ, 1 ≤ K_s ∧
      ∀ {N : ℕ} (d : CarrierData n N) {K : Set (Euclidean n)},
        K ⊆ chartBox r → d.outputChart = torusChart K →
      ∀ (U : EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ] CarrierL2 n),
        (∀ f, U f =ᵐ[carrierMeasure n] carrierAdjointIntegral d
          (fun x ↦ f (centeredTorusRepresentative x))) →
      ∀ (C H : ℝ), 0 ≤ C → 0 ≤ H →
        (∀ f, MemVectorFourierSobolev s f → MemRawSobolev s (U f) ∧
          rawSobolevNorm s (U f) ≤ C * (vectorFourierSobolevNorm s f + H * ‖f‖)) →
        (∀ v : PeriodicL2 n (EuclideanSpace ℂ (Fin n)),
          periodicCarrierOperator U v =ᵐ[carrierMeasure n] carrierAdjointIntegral d v) ∧
        ∀ v : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
          MemRawSobolev s (periodicCarrierOperator U (PeriodicSobolevSpace.toL2 s v)) ∧
          rawSobolevNorm s (periodicCarrierOperator U (PeriodicSobolevSpace.toL2 s v)) ≤
            K_s * C * (‖v‖ + H * ‖PeriodicSobolevSpace.toL2 s v‖) := by
  obtain ⟨ψ⟩ := nonempty_sourceCutoff (d := n) hr
  obtain ⟨B, _hB, hb⟩ := exists_periodicVectorExtension_bound ψ s
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro N d K hK hchart U hU C H hC hH hbound
  refine ⟨periodicCarrierOperator_ae d U hU, ?_⟩
  intro v
  have hsmooth := periodicCarrierOperator_smooth_raw_bound ψ s (max 1 B)
    (le_max_left _ _) (fun u hu ↦ (hb u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))
    d hK hchart U hU C H hC hH hbound
  have ha := PeriodicSobolevSpace.tendsto_smoothApproximation s v
  have haL2 := (PeriodicSobolevSpace.toL2 s).continuous.continuousAt.tendsto.comp ha
  have hout := (periodicCarrierOperator U).continuous.continuousAt.tendsto.comp haL2
  have hphysical := (partialUnitaryInverse n).continuous.continuousAt.tendsto.comp hout
  apply memPhysicalSobolev_and_norm_le_of_tendsto s hphysical
    (fun j ↦ (hsmooth (periodicCutoff (j + 1) (PeriodicSobolevSpace.toL2 s v))
      (isSmoothPeriodic_periodicCutoff _ _)).1)
    (tendsto_const_nhds.mul (ha.norm.add (tendsto_const_nhds.mul haL2.norm)))
  intro j
  exact (hsmooth (periodicCutoff (j + 1) (PeriodicSobolevSpace.toL2 s v))
    (isSmoothPeriodic_periodicCutoff _ _)).2

end JanetCartan.ContinuumAdjoint.DerivativeKernels
