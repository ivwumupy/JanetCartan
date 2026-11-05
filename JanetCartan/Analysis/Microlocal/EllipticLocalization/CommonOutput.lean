module

public import JanetCartan.Analysis.Microlocal.EllipticLocalization.Regularizations

/-!
# Literal common-output identities for the elliptic factors

The supplied common multiplier is absorbed only by the original output-mask
plateau. Both input masks and physical-frequency normalization stay inside
the same PDO. Consumers: the normalized solver and the common-output leakage
and polynomial costs (`app:ch_regular_base:eq:energy-complete-residual`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticLocalization
open FiniteMasks.ActualFamily EllipticComplement Characteristic.PdoRealization
open Characteristic.EvolutionIntegral CharacteristicTransport.CompleteResidual
open FourierIntegral FourierIntegral.LowBounds AmplitudeBound
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
local notation "H" => SpacetimeL2 d (d+1)
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
local notation "χo" => fun y ↦ (f.outputMask y : ℂ)
local notation "χs" => fun z ↦ (f.inputMask z : ℂ)

/-- The supplied output lies on the original plateau, hence literal output
multiplication preserves the original operator (`energy-complete-residual`). -/
theorem commonOutput_mul_elliptic_outputMask (output : E → ℝ)
    (hos : tsupport output ⊆ ball x f.physicalRadius) (y : E) :
    (output y : ℂ) * (f.outputMask y : ℂ) = (output y : ℂ) := by
  by_cases hy : y ∈ tsupport output
  · have he : f.outputMask y = 1 := interior_subset (s := {y | f.outputMask y = 1})
      (f.outputMask_plateau (ball_subset_closedBall (hos hy)))
    simp only [he, Complex.ofReal_one, mul_one]
  · simp only [image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_mul]

/-- The common output has the same fixed compact physical carrier required
by every actual elliptic grade; its support is inside the original doubled
physical ball (`app:ch_regular:lem:finite-chain`). -/
theorem commonOutput_elliptic_carrier (output : E → ℝ) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius) :
    IsCompact (tsupport (fun y ↦ (output y : ℂ)) ×ˢ tsupport (χs)) ∧
    tsupport (fun y ↦ (output y : ℂ)) ⊆ closedBall x (2*f.physicalRadius) := by
  refine ⟨(hoc.comp_left Complex.ofReal_zero).prod
    (f.inputMask_compact.comp_left Complex.ofReal_zero), ?_⟩
  exact (tsupport_comp_subset Complex.ofReal_zero output).trans
    (hos.trans (ball_subset_closedBall.trans (closedBall_subset_closedBall (by
      linarith [f.physicalRadius_pos]))))

/-- Apply the actual elliptic normal-amplitude producer to identify the
common-output PDO with the literal multiplier composition. No independently
chosen realization is identified (`energy-complete-residual`, `measured-adjoint`). -/
theorem commonOutput_ellipticPDO_eq_masked
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hos : tsupport output ⊆ ball x f.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    {threshold : ℝ} (ht : f.radialThreshold ≤ threshold)
    (Q : E → Coeff) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (hmap : MapsTo Q Ω (closedBall A₀ f.coefficientRadius))
    (hQl : cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M)
    (hBl : cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M) :
    ∀ s ∈ ({ellipticInverseSymbol f hK threshold Q,
      ellipticResidualSymbol f hK threshold Q B, ellipticSourceSymbol f hK threshold} :
      Set (E → E → CMat)),
      (sourceCutMultiplier output ho.continuous hob : H →L[ℂ] H).comp
        (maskedPhysicalPDO (χo) (χs) s) =
          maskedPhysicalPDO (fun y ↦ (output y : ℂ)) (χs) s := by
  obtain ⟨R, _, N, _, _, _, hb⟩ := exists_ellipticSymbols_pdo_budgets f hK hΩ hball
  obtain ⟨Rs, _, Cs, _, hsrc⟩ := exists_ellipticSourcePDO_budgets f hK
  intro s hs
  have hcert : ∃ R N, GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol (χo) (χs) s) R N := by
    simp only [mem_insert_iff, mem_singleton_iff] at hs
    rcases hs with h | h | rfl
    · exact ⟨R, N, (hb threshold ht Q B hQ hB hmap hQl hBl s (Or.inl h)).1⟩
    · exact ⟨R, N, (hb threshold ht Q B hQ hB hmap hQl hBl s (Or.inr h)).1⟩
    · exact ⟨Rs, Cs (2*(d+2)), (hsrc threshold).1⟩
  obtain ⟨R, N, hn⟩ := hcert
  exact FiniteResidual.SelectedChart.sourceCutMultiplier_maskedPhysicalPDO
    (χo) (χs) s R N hn output ho.continuous hob
    (commonOutput_mul_elliptic_outputMask f output hos)

/-- The source identity needs no coefficient hypothesis. The SAME source PDO
is multiplied on the output, with the original input still before Fourier
transformation (`app:ch_regular_base:eq:sector-theorem-identity`). -/
theorem commonOutput_ellipticSourcePDO_eq_masked
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hos : tsupport output ⊆ ball x f.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    (threshold : ℝ) :
    (sourceCutMultiplier output ho.continuous hob : H →L[ℂ] H).comp
      (ellipticSourcePDO f hK threshold) =
        maskedPhysicalPDO (fun y ↦ (output y : ℂ)) (χs) (ellipticSourceSymbol f hK threshold) := by
  obtain ⟨R, _, C, _, hb⟩ := exists_ellipticSourcePDO_budgets f hK
  exact FiniteResidual.SelectedChart.sourceCutMultiplier_maskedPhysicalPDO
    (χo) (χs) _ R (C (2*(d+2))) (hb threshold).1 output ho.continuous hob
    (commonOutput_mul_elliptic_outputMask f output hos)

end JanetCartan.RegularSector.EllipticLocalization
