module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.ScalarCommutator
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.PrimitiveBudget.Operators

/-!
# Subtraction of the all-data full matrix PDOs

The carrier-normal comparison in `paper-v2.tex`,
`app:ch_osc:prop:osc-normal`, Step 4', uses the difference of the full
amplitudes with the same physical Fourier phase. Compact-frequency kernel
linearity and strong exhaustion prove subtraction on every L² input.
Consumer: the real and complex normal estimates in `OperatorDifference`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.CarrierVariation
open AmplitudeBound Pseudodifferential PeriodicLocalL2 ContinuumCommutator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "P" => EuclideanSpace ℝ (Fin (2 * n))

/-- Subtraction of the actual scalar L² realizations follows from their
finite kernels and strong limits. The budgets of the three amplitudes may
differ (`app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem twoPositionL2Operator_sub
    (hn : 0 < n) (R : ℝ) (b c : E → P → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hc : ContDiff ℝ ∞ (Function.uncurry c))
    (hbc : ContDiff ℝ ∞ (Function.uncurry (b - c)))
    (hbs : ∀ ξ, SupportedInCenteredBox R (b ξ))
    (hcs : ∀ ξ, SupportedInCenteredBox R (c ξ))
    (hbcs : ∀ ξ, SupportedInCenteredBox R ((b - c) ξ))
    (B C D : ℝ)
    (hB : HasAmplitudeDerivativeBound b (2 * (n + 1)) B)
    (hC : HasAmplitudeDerivativeBound c (2 * (n + 1)) C)
    (hD : HasAmplitudeDerivativeBound (b - c) (2 * (n + 1)) D) :
    twoPositionL2Operator hn R (b - c) hbc hbcs D hD =
      twoPositionL2Operator hn R b hb hbs B hB -
        twoPositionL2Operator hn R c hc hcs C hC := by
  apply ContinuousLinearMap.ext
  intro f
  have he (ρ : ℝ) :
      twoPositionCompactFrequencyL2Operator hn R (b - c) hbc hbcs D hD ρ f =
        twoPositionCompactFrequencyL2Operator hn R b hb hbs B hB ρ f -
          twoPositionCompactFrequencyL2Operator hn R c hc hcs C hC ρ f := by
    apply Lp.ext
    filter_upwards [twoPositionCompactFrequencyL2Operator_ae_kernel
      hn R (b - c) hbc hbcs D hD ρ f,
      twoPositionCompactFrequencyL2Operator_ae_kernel hn R b hb hbs B hB ρ f,
      twoPositionCompactFrequencyL2Operator_ae_kernel hn R c hc hcs C hC ρ f,
      Lp.coeFn_sub
        (twoPositionCompactFrequencyL2Operator hn R b hb hbs B hB ρ f)
        (twoPositionCompactFrequencyL2Operator hn R c hc hcs C hC ρ f)]
      with x hdiff hleft hright hsub
    rw [hdiff, hsub, Pi.sub_apply, hleft, hright]
    simpa only [one_smul, Pi.sub_def] using
      integral_compactFrequencyAmplitudeKernel_smul_sub b c hb.continuous hc.continuous
        R R hbs hcs 1 ρ f x
  exact tendsto_nhds_unique
    (tendsto_twoPositionCompactFrequencyL2Operator hn R (b - c) hbc hbcs D hD f)
    (((tendsto_twoPositionCompactFrequencyL2Operator hn R b hb hbs B hB f).sub
      (tendsto_twoPositionCompactFrequencyL2Operator hn R c hc hcs C hC f)).congr
        (fun ρ ↦ (he ρ).symm))

/-- The finite coordinate isometries preserve subtraction of scalar blocks.
Consumer: full matrix amplitude differences in Step 4' of
`app:ch_osc:prop:osc-normal`. -/
theorem vectorMatrixL2Operator_sub {I J : Type*} [Fintype I] [Fintype J]
    (B C : I → J → Lp ℂ 2 (volume : Measure E) →L[ℂ]
      Lp ℂ 2 (volume : Measure E)) :
    vectorMatrixL2Operator (fun i j ↦ B i j - C i j) =
      vectorMatrixL2Operator B - vectorMatrixL2Operator C := by
  apply ContinuousLinearMap.ext
  intro f
  apply (finiteL2CoordinateIsometry volume).injective
  apply PiLp.ext
  intro i
  simp only [sub_apply, map_sub,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator, matrixOperator_apply,
    Finset.sum_sub_distrib, PiLp.sub_apply]

/-- Subtraction compatibility of the actual full vector PDO, with reserve
`2 * (n + 1)` on each entry (`app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem vectorTwoPositionL2Operator_sub {I J : Type} [Fintype I] [Fintype J]
    (hn : 0 < n) (R : ℝ) (b c : E → P → Matrix I J ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hc : ContDiff ℝ ∞ (Function.uncurry c))
    (hbc : ContDiff ℝ ∞ (Function.uncurry (b - c)))
    (hbs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j))
    (hcs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ c ξ z i j))
    (hbcs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ (b - c) ξ z i j))
    (B C D : ℝ)
    (hB : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (n + 1)) B)
    (hC : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ c ξ z i j) (2 * (n + 1)) C)
    (hD : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ (b - c) ξ z i j) (2 * (n + 1)) D) :
    vectorTwoPositionL2Operator hn R (b - c) hbc hbcs D hD =
      vectorTwoPositionL2Operator hn R b hb hbs B hB -
        vectorTwoPositionL2Operator hn R c hc hcs C hC := by
  unfold vectorTwoPositionL2Operator
  rw [← vectorMatrixL2Operator_sub]
  congr 1
  funext i j
  exact twoPositionL2Operator_sub hn R _ _ _ _ _ _ _ _ B C D (hB i j) (hC i j) (hD i j)

/-- Periodic chart transfer preserves subtraction on all output data.
Consumer: the same uncut normal comparison in
`app:ch_background:prop:bg-frame`. -/
theorem transferOperator_sub
    (A B : EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
      EuclideanL2 n (EuclideanSpace ℂ (Fin n))) :
    transferOperator (A - B) = transferOperator A - transferOperator B := by
  simp only [transferOperator, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

/-- Full matrix amplitude differences bound both the complex transferred
PDO difference and its real compression, with the original finite matrix
factor and no additional quadrature factor. The amplitude-difference producer
must supply `hD` (`app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem vectorTwoPositionL2Operator_sub_bounds
    (hn : 0 < n) (R : ℝ) (b c : E → P → Matrix (Fin n) (Fin n) ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hc : ContDiff ℝ ∞ (Function.uncurry c))
    (hbc : ContDiff ℝ ∞ (Function.uncurry (b - c)))
    (hbs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j))
    (hcs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ c ξ z i j))
    (hbcs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ (b - c) ξ z i j))
    (B C D : ℝ)
    (hB : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (n + 1)) B)
    (hC : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ c ξ z i j) (2 * (n + 1)) C)
    (s : ℕ) (hreserve : 2 * (n + 1) ≤ s)
    (hD : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ (b - c) ξ z i j) s D) :
    let T := vectorTwoPositionL2Operator hn R b hb hbs B hB
    let T' := vectorTwoPositionL2Operator hn R c hc hcs C hC
    ‖T - T'‖ ≤ (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n R * D) ∧
      ‖transferOperator T - transferOperator T'‖ ≤
        (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n R * D) ∧
      ‖realOutputCompression (transferOperator T) -
          realOutputCompression (transferOperator T')‖ ≤
        (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n R * D) := by
  dsimp only
  let hD' : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ (b - c) ξ z i j) (2 * (n + 1)) D :=
    fun i j ξ is his ↦ hD i j ξ is (his.trans hreserve)
  have hbound : ‖vectorTwoPositionL2Operator hn R b hb hbs B hB -
      vectorTwoPositionL2Operator hn R c hc hcs C hC‖ ≤
      (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n R * D) := by
    rw [← vectorTwoPositionL2Operator_sub hn R b c hb hc hbc hbs hcs hbcs B C D hB hC hD']
    unfold vectorTwoPositionL2Operator
    simpa only [Fintype.card_fin, pow_two] using
      norm_vectorMatrixL2Operator_le_of_entry_bound _ _
        (fun i j ↦ norm_twoPositionL2Operator_le hn R _ _ _ D (hD' i j))
  refine ⟨hbound, ?_, ?_⟩
  · rw [← transferOperator_sub]
    exact (norm_transferOperator_le _).trans hbound
  · rw [← realOutputCompression_sub, ← transferOperator_sub]
    exact (realOutputCompression_norm_le _).trans ((norm_transferOperator_le _).trans hbound)

end JanetCartan.ContinuumNormal.CarrierVariation
