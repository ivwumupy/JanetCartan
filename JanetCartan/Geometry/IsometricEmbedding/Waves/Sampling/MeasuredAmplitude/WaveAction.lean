module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.BandAction
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.WaveIntegral

/-!
# Every retained sampling prefix acts on the same actual raw waves

The wide-band integral identification and the proved raw differential formula
are combined before applying the original two-shell Hilbert isometry. Thus
arbitrary data in every unchanged grouped prefix synthesize the SAME measured
full primary wave. Both complex quadratures, original input/output Lebesgue
measures and the physical Fourier scalar are preserved.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling
open SamplingKernelBounds RawInputPartition RawInputRealization MeanNormalBound

/-- Every grouped prefix is the original wide row on its original projected
datum, under the SAME fixed two-shell isometry. No new row or ceiling is
selected when a prefix is changed (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem refinedKernelPrefix_eq_wideRow_projected
    {n J : ℕ} {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] [LocallyCompactSpace P]
    (D : BandKernelData (Fin J × P) n) (L : ℕ) (z : P) :
    refinedKernelPrefix D L z =
      wideBandKernelRow D z ∘L widePrefix n J L ∘L
        (wideRefinement n J).symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  have hfull : refinedKernelPrefix D J z =
      annularRow (fun i : RefinedIndex J ↦ D.operator (refinedRadius i) (i.1, z)) := by
    simp only [refinedKernelPrefix, Fin.is_lt, Finset.filter_true, prefixRow_univ]
  rw [wideBandKernelRow_eq_refined, hfull]
  ext1 f
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, wideRefinement_prefix,
    LinearIsometryEquiv.apply_symm_apply]
  exact congrArg (fun R ↦ R f) (refinedKernelPrefix_eq_comp D L z)

namespace MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation RawKernel
open RawPrimary RawPrimary.MaskProfiles RawPrimary.AmplitudeGrades.Polynomial

variable {m N J p : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
    Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)
  (measurement : Euclidean (m + 1) →
    Matrix (Fin N) (Fin (m + 1)) ℂ →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
  (χ : Euclidean (m + 1) → ℝ)
  (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  {ρ : ℝ} (hρ : 0 < ρ)
  {c C : ℝ} (hP : P.IsValid c C)
  (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  (hs : ContDiff ℝ ∞ (fun q : ℝ × (Euclidean (m + 1) ×
    (Euclidean 3 × Euclidean (m + 1 - 1))) ↦
      supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ
        q.1 q.2.2.1 q.2.1 q.2.2.2))
  (M : ℝ) (hM : 0 ≤ M)
  (hb : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x ξ,
    ‖supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ
      τ z x ξ‖ ≤ M)
  (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
  (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
  (hH : ContDiff ℝ ∞ highPass) (hH₀ : ∀ η, ‖η‖ ≤ 1 → highPass η = 0)
  (B : ℝ) (hB : 0 ≤ B) (hdB : ∀ η, ‖detectorMask angular highPass η‖ ≤ B)
  (τ : (Fin 3 → Fin (p + 1)) → ℝ)
  (hτ : ∀ color, τ color ∈ Icc (-1 : ℝ) 1) (hτ₀ : ∀ color, τ color ≠ 0)

local notation "D" => retainedMeasuredKernelData (J := J) T Q F row col Φ Y r measurement χ
  a hρ hP hcarrier hs M hM hb angular highPass ha hH hH₀ B hB hdB τ hτ hτ₀

variable (hphase : closedBall a (2 * ρ) ⊆ domain T)
  (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
  (color : Fin 3 → Fin (p + 1)) (z : SeparatedSampling.Point)
  (hz : (WithLp.toLp 2 z, T.reference.spatialPatch (WithLp.toLp 2 z)) ∈
    closedBall a.2 (ρ / 4))

variable
  {Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))}
  (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
  (hphaseΩ : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
  (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
  (hrank : HasFullNormalRankOn F U)
  (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
  (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
  (hν₀ : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω)
  (hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω)
  (hV₀ : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω)
  (hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω)
  {X : Set (Euclidean (m + 1))} {V : Set (Euclidean (m + 1 - 1))}
  (hX : IsOpen X) (hV : IsOpen V)
  (hζ : T.reference.spatialPatch (WithLp.toLp 2 z) ∈ V)
  (hproduct : ∀ q ∈ X ×ˢ V, (q.1, (WithLp.toLp 2 z, q.2)) ∈ Ω)
  (hshift : ∀ η ∈ closedBall 0 ((2 : ℝ) ^ J),
    T.reference.spatialPatch (WithLp.toLp 2 z) + τ color • η ∈ V)
  (hχX : Function.support χ ⊆ X)
  (hscale : ∀ j : Fin J, |τ color| * (2 : ℝ) ^ j.val ≤ ρ / 8)

include hphase hχ hz hΩ hspace hphaseΩ hF hi hrank hα hnonzero hν₀ hν₁ hV₀ hV₁
  hX hV hζ hproduct hshift hχX hscale in
/-- The literal constructed wide row is the measured differential of the
original full primary wave on arbitrary original Hilbert data. The geometric
regularity inputs are retained leading/reconstruction outputs; all kernel,
polynomial, integration and differentiation equalities are proved
(`app:ch_waves:eq:individual-representation`). -/
theorem retainedMeasuredKernelData_row_ae_wave_derivative
    (v : WideInput (m + 1) J) :
    wideBandKernelRow D (color, z) v =ᵐ[volume] fun x ↦
      (2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) •
        ((χ x : ℂ) • measurement x
          (Complex.exp (-Complex.I * (T.carrier Q x (WithLp.toLp 2 z) / τ color : ℝ)) •
            RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix (m + 1) N
              (fderiv ℝ (fullPrimaryWave T Q F row col Φ Y (τ color) r (WithLp.toLp 2 z)
                (detectorMask angular highPass) v) x))) := by
  refine (retainedMeasuredKernelData_row_ae_polynomial
    T Q F row col Φ Y r measurement χ a hρ hP hcarrier hs M hM hb angular highPass
    ha hH hH₀ B hB hdB τ hτ hτ₀ hphase hχ color z hz hscale v).trans
      (Filter.Eventually.of_forall fun x ↦ ?_)
  exact congrArg (fun w : EuclideanSpace ℂ (Fin (m + 1)) ↦
    (2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) • w)
    (sum_measuredPolynomial_bandIntegral_eq_wave_derivative
    T Q F row col Φ Y r measurement χ hΩ hphaseΩ hν₀ hν₁ hV₀ hV₁ (hτ₀ color)
    (WithLp.toLp 2 z) hζ hproduct hshift
    (contDiff_detectorMask angular highPass ha hH hH₀).continuous.measurable hdB
    hspace hF hi hrank hα hnonzero hX hV v hχX x)

include hphase hχ hz hΩ hspace hphaseΩ hF hi hrank hα hnonzero hν₀ hν₁ hV₀ hV₁
  hX hV hζ hproduct hshift hχX hscale in
/-- The SAME actual wave represents every grouped sampling prefix on the
original fixed refined input. Only `widePrefix` changes its datum; neither
phase, amplitude, detector, labels, measurement nor samples change. This is
the exact physical representative required by the sharp sampling-band and
current-row consumers (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem retainedMeasuredKernelData_prefix_ae_wave_derivative
    (L : ℕ) (v : RefinedInput (m + 1) J) :
    refinedKernelPrefix D L (color, z) v =ᵐ[volume] fun x ↦
      (2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) •
        ((χ x : ℂ) • measurement x
          (Complex.exp (-Complex.I * (T.carrier Q x (WithLp.toLp 2 z) / τ color : ℝ)) •
            RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix (m + 1) N
              (fderiv ℝ (fullPrimaryWave T Q F row col Φ Y (τ color) r (WithLp.toLp 2 z)
                (detectorMask angular highPass)
                (widePrefix (m + 1) J L ((wideRefinement (m + 1) J).symm v))) x))) := by
  rw [refinedKernelPrefix_eq_wideRow_projected]
  exact retainedMeasuredKernelData_row_ae_wave_derivative
    T Q F row col Φ Y r measurement χ a hρ hP hcarrier hs M hM hb angular highPass
    ha hH hH₀ B hB hdB τ hτ hτ₀ hphase hχ color z hz hΩ hspace hphaseΩ hF hi hrank
    hα hnonzero hν₀ hν₁ hV₀ hV₁ hX hV hζ hproduct hshift hχX hscale _

include hphase hχ hz hΩ hspace hphaseΩ hF hi hrank hα hnonzero hν₀ hν₁ hV₀ hV₁
  hX hV hζ hproduct hshift hχX hscale in
/-- The physical real prefix is twice the real part of the SAME measured
raw derivative. Its datum remains the whole complex Hilbert input, so neither
quadrature is discarded (`app:ch_waves:eq:real-normal`). -/
theorem retainedMeasuredKernelData_realPrefix_ae_wave_derivative
    (L : ℕ) (v : RefinedInput (m + 1) J) :
    realQuadratureChannel (refinedKernelPrefix D L (color, z)) v =ᵐ[volume] fun x ↦
      (2 : ℝ) • euclideanRealPart
        ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) •
          ((χ x : ℂ) • measurement x
            (Complex.exp (-Complex.I * (T.carrier Q x (WithLp.toLp 2 z) / τ color : ℝ)) •
              RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix (m + 1) N
                (fderiv ℝ (fullPrimaryWave T Q F row col Φ Y (τ color) r (WithLp.toLp 2 z)
                  (detectorMask angular highPass)
                  (widePrefix (m + 1) J L ((wideRefinement (m + 1) J).symm v))) x)))) := by
  have hraw := retainedMeasuredKernelData_prefix_ae_wave_derivative
    T Q F row col Φ Y r measurement χ a hρ hP hcarrier hs M hM hb angular highPass
    ha hH hH₀ B hB hdB τ hτ hτ₀ hphase hχ color z hz hΩ hspace hphaseΩ hF hi hrank
    hα hnonzero hν₀ hν₁ hV₀ hV₁ hX hV hζ hproduct hshift hχX hscale L v
  simp only [realQuadratureChannel_apply]
  filter_upwards [Lp.coeFn_smul (2 : ℝ)
      (l2RealPart volume (refinedKernelPrefix D L (color, z) v)),
    (euclideanRealPart (ι := Fin (m + 1))).coeFn_compLpL
      (refinedKernelPrefix D L (color, z) v), hraw] with x h₂ hre hp
  rw [h₂]
  change (2 : ℝ) • ((euclideanRealPart.compLpL 2 volume)
    (refinedKernelPrefix D L (color, z) v)) x = _
  rw [hre, hp]

end MeasuredAmplitude
end JanetCartan.Sampling
