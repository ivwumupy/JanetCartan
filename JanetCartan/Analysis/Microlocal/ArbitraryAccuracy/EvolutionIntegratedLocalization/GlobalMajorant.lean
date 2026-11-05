module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.ShellSummation
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Summation
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Comparable.Estimates

/-!
# Global domination for identification of the elapsed shell series

The regularized identity contribution has noncompact output. A crude bound
on comparable shells, valid at every output base, and the separated per-time
bound give the global summable majorant required by `StrongIdentification`.
This does not impose a stationary gap at distant output bases. The sharper
joint stationary estimate is used only on the final compact output carrier
(`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph KernelEstimates PhysicalShells PhysicalShells.Noncomparable
open RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => ℝ × JointVariables (Euclidean (d + 1))

attribute [local instance] KernelLimits.matrixContinuousENorm KernelLimits.matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option maxHeartbeats 800000

/-- A global summable Frobenius majorant for the same literal elapsed kernels
used in `exists_localized_elapsedGraphIntegral_shell_identification`.
Comparable terms use only primitive full-amplitude grades and compact support;
separated terms use the allowed identified per-time graph estimate. There is
no integrated bound or uncut test action among the premises. Both physical
regularizations, the output ball, contracting graph shells and the full
complementary multiplier remain present (`app:ch_regular:eq:chain-tail`). -/
theorem exists_elapsedPhysicalShellKernel_global_majorant
    (backward : Bool) {ρ L : ℝ} (hρ : 1 ≤ ρ) (hL : 1 ≤ L) (s Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (θ : ℝ → ℂ) (hθ : ∀ r ∈ Icc 0 Δ, θ r = 1)
    (hΨ : ∀ r ∈ Icc 0 Δ, Continuous (Function.uncurry (elapsedPhase Ψ r)))
    (hb : ∀ r ∈ Icc 0 Δ, Continuous (fun p : (E × E) × E ↦
      orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2))
    (hi : Continuous mi) (ho : ContDiff ℝ ∞ mo) (horange : ∀ p, mo p ∈ Icc (0 : ℝ) 1)
    (carriers : ∀ j k r, r ∈ Icc 0 Δ →
      KernelLimits.RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
        mi (graphCutoff j) (outputCutoff k))
    (hF : ∀ y, ContDiff ℝ ∞
      (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) 0 y))
    (ha : ∀ y low j k, ContDiff ℝ ∞ (fun p : V ↦ θ p.1 •
      jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y p))
    (hcompact : ∀ y low j k, HasCompactSupport (fun p : V ↦ θ p.1 •
      jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y p))
    (c C b₀ : ℝ) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (D : AmplitudeProfiles) {K : Set (JointVariables E)} (hK : IsCompact K)
    (hgrades : ∀ low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      ∀ r ∈ Icc 0 Δ, ∀ y, HasAmplitudeGrades D ρ (ρ ^ s) L
        (orientedElapsedAmplitude backward b χout χsource β r) mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y K)
    (hs : ∀ low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      ∀ r ∈ Icc 0 Δ, ∀ y, tsupport (jointAmplitude ρ
        (orientedElapsedAmplitude backward b χout χsource β r) mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y) ⊆ K)
    {Dsep : ℝ} (hDsep : 0 ≤ Dsep) (bLoss : ℕ)
    (hper : ∀ low j k, SeparatedRanges c C (a₀ * ρ) (b₀ * ρ)
        (graphLower low j) (graphUpper low j) (outputLower k) (outputUpper k) →
      ∀ r ∈ Icc 0 Δ, ∀ x y,
        ‖KernelLimits.regularizedJointKernel backward (elapsedPhase Ψ r)
          (orientedElapsedAmplitude backward b χout χsource β r)
          (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
            (graphBranchCutoff low j) (outputCutoff k) x y‖ ≤
          Dsep * ρ ^ (d + 1) * L ^ bLoss * pairWeight low (d + 1) j k) :
    ∃ M : ℕ × ℕ → ℝ, (∀ p, 0 ≤ M p) ∧ Summable M ∧
      ∀ j k x y, ‖elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β
        mi mo (graphCutoff j) (outputCutoff k) x y‖ ≤ M (j, k) := by
  classical
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  let Bcomp := (jointNormalization (d + 1) * (jointMeasure (d + 1)).real K *
    D.productProfile 0) * ρ ^ (s + (3 * (d + 1) : ℕ)) * L ^ D.offset
  let Bsep := Dsep * ρ ^ (d + 1) * L ^ bLoss
  have hBc : 0 ≤ Bcomp := by
    dsimp [Bcomp]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (jointNormalization_nonneg _)
      measureReal_nonneg) (D.productProfile_nonneg 0)) (Real.rpow_nonneg hρ0.le _))
      (pow_nonneg (zero_le_one.trans hL) _)
  have hBs : 0 ≤ Bsep := by dsimp [Bsep]; positivity
  let B := (Bcomp + Bsep) * volume.real (Icc 0 Δ)
  have hB : 0 ≤ B := mul_nonneg (add_nonneg hBc hBs) measureReal_nonneg
  obtain ⟨mass, _, hm⟩ := exists_graphPairWeight_mass (n := d + 1) (by omega) c C b₀ ha₀
  have hw := (hm ρ hρ).1
  let cb (low : Bool) (j k : ℕ) (r : ℝ) (hr : r ∈ Icc 0 Δ) :
      KernelLimits.RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
        mi (graphBranchCutoff low j) (outputCutoff k) :=
    { carriers j k r hr with compact_graphCutoff := hasCompactSupport_graphBranchCutoff low j }
  have hbnd (low : Bool) (j k : ℕ) (x y : E) :
      ‖elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
        (graphBranchCutoff low j) (outputCutoff k) x y‖ ≤
      B * regimePairWeight (d + 1) c C a₀ b₀ ρ low (j, k) := by
    by_cases hc : IsComparablePair c C a₀ b₀ ρ low j k
    · have hr (r : ℝ) (hr : r ∈ Icc 0 Δ) :
          ‖KernelLimits.regularizedJointKernel backward (elapsedPhase Ψ r)
            (orientedElapsedAmplitude backward b χout χsource β r)
            (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2))
              (graphBranchCutoff low j) (outputCutoff k) x y‖ ≤ Bcomp := by
        rw [PhysicalShells.regularizedJointKernel_eq_normalized backward _
          (elapsedPhase (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) r) _ mi mo _ _ x y hρ0
          (fun u ξ ↦ by
            rw [← SymbolBudgets.normalizedPhase_elapsedPhase hρ0.ne' Ψ r]
            simp only [WholeImageGeometry.normalizedPhase, ← mul_assoc,
              mul_inv_cancel₀ hρ0.ne', one_mul])
          (hΨ r hr) (hb r hr) hi ho.continuous (contDiff_graphBranchCutoff low j).continuous
          (contDiff_outputCutoff k).continuous (cb low j k r hr)]
        exact Comparable.norm_normalizedJointKernel_le_crude backward hρ0 hL s _ _ mi mo
          _ _ x y horange hK (hgrades low j k hc r hr y) (hs low j k hc r hr y)
      have he := norm_setIntegral_le_of_norm_le_const (μ := volume) isCompact_Icc.measure_lt_top hr
      change ‖elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
        (graphBranchCutoff low j) (outputCutoff k) x y‖ ≤ Bcomp * volume.real (Icc 0 Δ) at he
      simp only [regimePairWeight, hc, ↓reduceIte, mul_one]
      exact he.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hBs) measureReal_nonneg)
    · have hsep : SeparatedRanges c C (a₀ * ρ) (b₀ * ρ)
          (graphLower low j) (graphUpper low j) (outputLower k) (outputUpper k) :=
        Classical.not_not.mp hc
      have he := norm_setIntegral_le_of_norm_le_const (μ := volume) isCompact_Icc.measure_lt_top
        (fun r hr ↦ hper low j k hsep r hr x y)
      change ‖elapsedPhysicalShellKernel backward ρ Δ Ψ b χout χsource β mi mo
        (graphBranchCutoff low j) (outputCutoff k) x y‖ ≤
          (Bsep * pairWeight low (d + 1) j k) * volume.real (Icc 0 Δ) at he
      simp only [regimePairWeight, hc, ↓reduceIte]
      apply he.trans
      have hle := mul_le_mul_of_nonneg_right
        (show Bsep ≤ Bcomp + Bsep from le_add_of_nonneg_left hBc)
        (mul_nonneg (pairWeight_nonneg low (d + 1) j k)
          (show 0 ≤ volume.real (Icc 0 Δ) from measureReal_nonneg))
      dsimp only [B]
      convert hle using 1 <;> ring
  refine ⟨fun p ↦ B * graphPairWeight (d + 1) c C a₀ b₀ ρ p,
    fun p ↦ mul_nonneg hB (graphPairWeight_nonneg _ _ _ _ _ _ p), hw.mul_left B, ?_⟩
  intro j k x y
  rw [elapsedPhysicalShellKernel_graphCutoff_split backward hρ0 Δ Ψ b χout χsource β
    mi mo j k θ y hθ hΨ hb hi ho (carriers j k) (hF y) (ha y · j k)
    (fun low ↦ tsupport (fun p : V ↦ θ p.1 •
      jointElapsedAmplitude backward ρ b χout χsource β mi (fun _ ↦ 0)
        (graphBranchCutoff low j) (outputCutoff k) 0 y p))
    (hcompact y · j k) (fun _ ↦ Subset.rfl) x]
  exact (norm_add_le _ _).trans ((add_le_add (hbnd false j k x y) (hbnd true j k x y))
    |>.trans_eq (by dsimp [graphPairWeight]; ring))

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
