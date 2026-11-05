module

public import JanetCartan.Analysis.Microlocal.EllipticLocalization.Support
public import JanetCartan.Analysis.Microlocal.EllipticComplement.SymbolBudgets
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Regularizations

/-!
# Actual elliptic PDO regularizations

Apply the elliptic budget producers to the original operators. Both orientations
use the same physical cutoff sequence and the literal adjoint order, as required
by `app:ch_regular_base:eq:energy-complete-residual` and the diagonal leakage
consumer in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticLocalization
open FiniteMasks.ActualFamily EllipticComplement Characteristic.PdoRealization
open Characteristic.EvolutionIntegral
open ArbitraryAccuracy.ResidualLocalization ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FullLowBounds LowBounds LowBounds.FrequencyCutoff
open CharacteristicTransport.CompleteResidual
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

/-- The actual inverse, full residual and source have joint smoothness and
literal forward/adjoint graph regularizations. Only the original coefficient
conditions occur; the normal-amplitude certificates are produced here, using
`exists_ellipticSymbols_pdo_budgets` and `exists_ellipticSourcePDO_budgets`
(`app:ch_regular:lem:finite-chain`, `measured-adjoint`). -/
theorem exists_ellipticPDO_oriented_regularizations
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    {threshold : ℝ} (ht : f.radialThreshold ≤ threshold)
    (Q : E → Coeff) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (hmap : MapsTo Q Ω (closedBall A₀ f.coefficientRadius))
    (hQl : cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M)
    (hBl : cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M) :
    ∀ s ∈ ({ellipticInverseSymbol f hK threshold Q,
      ellipticResidualSymbol f hK threshold Q B, ellipticSourceSymbol f hK threshold} :
      Set (E → E → CMat)),
    (∀ backward, ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      orientedMaskedPDOAmplitude backward (χo) (χs) s p.1.1 p.1.2 p.2)) ∧
    ∃ Preg : Bool → ℕ → H →L[ℂ] H,
      (∀ l, Preg true l = (Preg false l).adjoint) ∧
      (∀ backward l (u : graphTestSpace (d+1) (d+1)),
        Preg backward l (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (((if backward then reverseGraphOperator else graphOperator)
            (fun y ξ ↦ inner ℝ y ξ)
            (frequencyCutFullAmplitude (complexPhysicalCutoff l)
              (orientedMaskedPDOAmplitude backward (χo) (χs) s))
            (fun z ↦ (u.val z).ofLp)) y)) ∧
      (∀ backward u, Tendsto (fun l ↦ Preg backward l u) atTop
        (𝓝 ((if backward then (maskedPhysicalPDO (χo) (χs) s).adjoint
          else maskedPhysicalPDO (χo) (χs) s) u))) := by
  obtain ⟨R, _, N, _, _, _, hb⟩ := exists_ellipticSymbols_pdo_budgets f hK hΩ hRQΩ
  obtain ⟨Rs, _, Cs, _, hsrc⟩ := exists_ellipticSourcePDO_budgets f hK
  intro s hs
  have hcert : ∃ R N, GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol (χo) (χs) s) R N := by
    simp only [mem_insert_iff, mem_singleton_iff] at hs
    rcases hs with h | h | rfl
    · exact ⟨R, N, (hb threshold ht Q B hQ hB hmap hQl hBl s (Or.inl h)).1⟩
    · exact ⟨R, N, (hb threshold ht Q B hQ hB hmap hQl hBl s (Or.inr h)).1⟩
    · exact ⟨Rs, Cs (2*(d+2)), (hsrc threshold).1⟩
  obtain ⟨R, N, hn⟩ := hcert
  exact exists_maskedPDO_oriented_regularizations (χo) (χs) s
    (f.outputMask_compact.comp_left Complex.ofReal_zero)
    (f.inputMask_compact.comp_left Complex.ofReal_zero) hn

/-- The parent's supplied common output acts on the SAME elliptic PDOs.
Its strong limits identify literal left multiplication; the adjoint reverses
that order. The plateau follows from the original physical geometry, and all
normal-amplitude inputs are produced for these symbols
(`app:ch_regular_base:eq:energy-complete-residual`, `measured-adjoint`). -/
theorem exists_commonOutput_ellipticPDO_oriented_regularizations
    (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius) (hob : ∀ y, ‖output y‖ ≤ 1)
    {threshold : ℝ} (ht : f.radialThreshold ≤ threshold)
    (Q : E → Coeff) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (hmap : MapsTo Q Ω (closedBall A₀ f.coefficientRadius))
    (hQl : cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M)
    (hBl : cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M) :
    let O : H →L[ℂ] H := sourceCutMultiplier output ho.continuous hob
    ∀ s ∈ ({ellipticInverseSymbol f hK threshold Q,
      ellipticResidualSymbol f hK threshold Q B, ellipticSourceSymbol f hK threshold} :
      Set (E → E → CMat)),
    (∀ backward, ContDiff ℝ ∞ (fun p : (E × E) × E ↦
      orientedMaskedPDOAmplitude backward (fun y ↦ (output y : ℂ)) (χs) s p.1.1 p.1.2 p.2)) ∧
    ∃ Preg : Bool → ℕ → H →L[ℂ] H,
      (∀ l, Preg true l = (Preg false l).adjoint) ∧
      (∀ backward l (u : graphTestSpace (d+1) (d+1)),
        Preg backward l (graphTestToLp u) =ᵐ[volume] fun y ↦ WithLp.toLp 2
          (((if backward then reverseGraphOperator else graphOperator)
            (fun y ξ ↦ inner ℝ y ξ)
            (frequencyCutFullAmplitude (complexPhysicalCutoff l)
              (orientedMaskedPDOAmplitude backward (fun y ↦ (output y : ℂ)) (χs) s))
            (fun z ↦ (u.val z).ofLp)) y)) ∧
      (∀ backward u, Tendsto (fun l ↦ Preg backward l u) atTop
        (𝓝 ((if backward then (O.comp (maskedPhysicalPDO (χo) (χs) s)).adjoint
          else O.comp (maskedPhysicalPDO (χo) (χs) s)) u))) := by
  intro O
  obtain ⟨R, _, N, _, _, _, hb⟩ := exists_ellipticSymbols_pdo_budgets f hK hΩ hRQΩ
  obtain ⟨Rs, _, Cs, _, hsrc⟩ := exists_ellipticSourcePDO_budgets f hK
  have hp y : (output y : ℂ) * (f.outputMask y : ℂ) = (output y : ℂ) := by
    by_cases hy : y ∈ tsupport output
    · have he : f.outputMask y = 1 := interior_subset (s := {y | f.outputMask y = 1})
        (f.outputMask_plateau (ball_subset_closedBall (hos hy)))
      simp only [he, Complex.ofReal_one, mul_one]
    · simp only [image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_mul]
  intro s hs
  have hcert : ∃ R N, GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol (χo) (χs) s) R N := by
    simp only [mem_insert_iff, mem_singleton_iff] at hs
    rcases hs with h | h | rfl
    · exact ⟨R, N, (hb threshold ht Q B hQ hB hmap hQl hBl s (Or.inl h)).1⟩
    · exact ⟨R, N, (hb threshold ht Q B hQ hB hmap hQl hBl s (Or.inr h)).1⟩
    · exact ⟨Rs, Cs (2*(d+2)), (hsrc threshold).1⟩
  obtain ⟨R, N, hn⟩ := hcert
  have he : O.comp (maskedPhysicalPDO (χo) (χs) s) =
      maskedPhysicalPDO (fun y ↦ (output y : ℂ)) (χs) s :=
    FiniteResidual.SelectedChart.sourceCutMultiplier_maskedPhysicalPDO
      (χo) (χs) s R N hn output ho.continuous hob hp
  simpa only [he] using exists_commonOutputPDO_oriented_regularizations (χo) (χs) s
    (f.outputMask_compact.comp_left Complex.ofReal_zero)
    (f.inputMask_compact.comp_left Complex.ofReal_zero) hn output ho hoc hob hp

end JanetCartan.RegularSector.EllipticLocalization
