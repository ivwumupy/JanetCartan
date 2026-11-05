module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.FiniteAction
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.VectorKernel
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.Chart.Support

/-!
# Locality on the full normal measurement support

For `app:ch_background:prop:bg-frame`, Step 1, retain the actual measurement
support when replacing the cell lift by the compact physical test profile.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open AmplitudeBound Pseudodifferential PeriodicLocalL2 ContinuumNormalReduction TransportKernel TestChartTransfer
variable {n N : ℕ}
private theorem scalar_eq_of_source_support
    (hn : 0 < n) (R : ℝ) (b : Euclidean n → Euclidean (2 * n) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (B : ℝ)
    (hB : HasAmplitudeDerivativeBound b (2 * (n + 1)) B)
    (f g : EuclideanL2 n ℂ)
    (hfg : ∀ᵐ y ∂volume, ∀ x ξ, b ξ (pairedPosition x y) ≠ 0 → f y = g y) :
    twoPositionL2Operator hn R b hb hs B hB f = twoPositionL2Operator hn R b hb hs B hB g := by
  let A := boxCompactFrequencyAmplitudeOperator b hb.continuous.stronglyMeasurable hn
    (amplitudeBoxScale_pos R) (div_amplitudeBoxScale_lt R) hs
    (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) B hB.norm_le hB.pure_le
  have hlim (v : EuclideanL2 n ℂ) : Tendsto (fun ρ ↦ A ρ v) atTop
      (𝓝 (twoPositionL2Operator hn R b hb hs B hB v)) :=
    tendsto_boxCompactFrequencyAmplitudeOperator ..
  have he (ρ : ℝ) : A ρ f = A ρ g := by
    apply Lp.ext
    have hf : A ρ f =ᵐ[volume] boxScalarAmplitudeKernel b ρ f :=
      boxCompactFrequencyAmplitudeOperator_ae_kernel ..
    have hg : A ρ g =ᵐ[volume] boxScalarAmplitudeKernel b ρ g :=
      boxCompactFrequencyAmplitudeOperator_ae_kernel ..
    filter_upwards [hf, hg] with x hx hx'
    rw [hx, hx']
    unfold boxScalarAmplitudeKernel
    apply integral_congr_ae
    filter_upwards [] with ξ
    apply integral_congr_ae
    filter_upwards [hfg] with y hy
    by_cases hz : b ξ (pairedPosition x y) = 0
    · simp [hz]
    · rw [hy x ξ hz]
  exact tendsto_nhds_unique (hlim f) ((hlim g).congr (fun ρ ↦ (he ρ).symm))

/-- Source locality on the actual measurement support, for the full reflected
normal in `app:ch_background:eq:bg-full-complex-amplitude`. Consumer: the
smooth-test action and the global finite PDO identification. -/
theorem fullReflectedMatrixOperator_congr_on_measurement
    (hn : 0 < n) (R : ℝ)
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S)))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j))
    (B : ℝ) (hB : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j) (2 * (n + 1)) B)
    (f g : EuclideanL2 n (EuclideanSpace ℂ (Fin n)))
    (hfg : ∀ᵐ y ∂volume, a.measurement y ≠ 0 → f y = g y) :
    vectorTwoPositionL2Operator hn R (fullReflectedMatrixAmplitude a J u Ω S) hb hs B hB f =
      vectorTwoPositionL2Operator hn R (fullReflectedMatrixAmplitude a J u Ω S) hb hs B hB g := by
  apply (finiteL2CoordinateIsometry volume).injective
  apply PiLp.ext
  intro i
  simp only [vectorTwoPositionL2Operator,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator, matrixOperator_apply]
  apply Finset.sum_congr rfl
  intro j _
  apply scalar_eq_of_source_support
  filter_upwards [hfg, finiteL2Coordinates_apply_ae volume f j,
    finiteL2Coordinates_apply_ae volume g j] with y hy hf hg x ξ hne
  have hm : a.measurement y ≠ 0 := by
    intro he
    simp [fullReflectedMatrixAmplitude_pairedPosition,
      reflectedAmplitude_eq_zero_of_source_measurement a J u Ω S x y _ he] at hne
  exact hf.trans ((congrArg (fun v : EuclideanSpace ℂ (Fin n) ↦ v j) (hy hm)).trans hg.symm)
end JanetCartan.ContinuumRow.CarrierNormalRealization
