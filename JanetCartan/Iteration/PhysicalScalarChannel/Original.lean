module

public import JanetCartan.Iteration.PhysicalScalarChannel.Kernel

/-!
# The original bare physical scalar operator on the entire wide input

The full dyadic normal bound is integrated once in time, and the literal
bounded inverse-half input map is applied once to the complete Hilbert sum.
The original finite-parameter phase and physical Fourier scalar are retained.
There is no sum of individual band norms and no sampling weight.
Consumers: the individual `q - 1/2` moment following
`app:ch_mean_pairs:eq:raw-adjoint-moments`, and the fixed-carrier forward
estimate in `app:ch_mean_pairs:eq:block-fields`. Aggregate adjoint moments use
the distinct half-weighted same-event scalar row in `PhysicalSampling`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric MeasureTheory
open scoped BigOperators ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalScalarChannel

open NormalComparison SingleChannel ActualCarriers FrozenMenu CurrentFullPhase
open RawPrimary RawPrimary.SliceBounds RawPrimary.SliceGeometry RawPrimary.MaskProfiles RawInputPartition
open FullPhaseCharts FullPhaseCharts.ActualPhase PhysicalSampling PhysicalMean Sampling.MeasuredAmplitude
open LeadingWave.FullModulation ProjectedStressFrame

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})

/-- The SAME original physical phase and smooth masks with no half derivative
and no sample weight. The scalar coordinate is embedded only to use the already
proved vector normal theorem. -/
def retainedBareScalarVectorKernel
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ)
    (z₀ z : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ) (τ : ℝ) (j : ℕ)
    (x : Euclidean (m + 1)) (η : Euclidean (m + 1 - 1)) : EuclideanSpace ℂ (Fin (m + 1)) :=
  (2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) •
    ((Complex.exp (Complex.I * (rawPrimaryPhaseDifference (extendedRetainedPhase T Q)
      (extendedRetainedCarrier T z₀ hρ z) τ x η : ℂ)) *
      weightedRadialBand (detectorMask angular H) j η) •
        scalarAuxiliaryAmplitude (Nat.succ_le_succ (Nat.zero_le m)) χ () x 0)

/-- Exact physical normalization and retained phase identification for every
original wide-band datum. Unlike the scalar sampling row there is no half
frequency factor in either side. -/
theorem bareChannelIntegral_eq_retained
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ)
    (center : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) (hphase : closedBall center (2 * ρ) ⊆ domain T)
    {a e b : ℝ} (ha : 0 < a) (haR : 4 * a < T.family.radius)
    (he : 0 < e) (heb : 16 * e < b)
    (hχa : tsupport (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall 0 (a / 4))
    (hχρ : Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall center.1 (ρ / 2))
    (z : Euclidean 3)
    (hb : ball (T.reference.spatialPatch z) b ⊆
      ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)))
    (hzg : (z, T.reference.spatialPatch z) ∈ closedBall center.2 (ρ / 4))
    {D : Set (Euclidean (m + 1 - 1))} (hD : D = sliceInputDomain (m + 1))
    {τ : ℝ} (hτ : τ ≠ 0) (j : ℕ)
    (hε : τ * (2 : ℝ) ^ j ∈ Icc 0 e) (hscale : |τ * (2 : ℝ) ^ j| ≤ ρ / 8)
    (f : WideBandL2 (m + 1) j) (q : ℝ × Euclidean (m + 1 - 1)) :
    (2 * Real.pi) ^ (-(1 : ℝ) / 2) •
      channelIntegral (scalarFullBandChannelKernel T Q (Nat.succ_le_succ (Nat.zero_le m))
        χ angular H z j (τ * (2 : ℝ) ^ j)) (bareChartInput (m + 1) j D f) q =
      ∫ η in wideBand (m + 1) j, f η •
        retainedBareScalarVectorKernel T Q χ angular H center.2.1 z hρ τ j
          (adaptedPhysicalCoordinates T.data.adapted q) η := by
  have hraw : (∫ η in wideBand (m + 1) j, f η •
      retainedBareScalarVectorKernel T Q χ angular H center.2.1 z hρ τ j
        (adaptedPhysicalCoordinates T.data.adapted q) η) =
      (2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) •
        ∫ η in wideBand (m + 1) j,
          ((Complex.exp (Complex.I * (rawPrimaryPhaseDifference
            (fun q η ↦ extendedRetainedPhase T Q (adaptedPhysicalCoordinates T.data.adapted q) η)
            (extendedRetainedCarrier T center.2.1 hρ z) τ q η : ℂ)) *
            weightedRadialBand (detectorMask angular H) j η) * f η) •
              scalarAuxiliaryAmplitude (Nat.succ_le_succ (Nat.zero_le m)) χ ()
                (adaptedPhysicalCoordinates T.data.adapted q) 0 := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with η
    simp only [retainedBareScalarVectorKernel, rawPrimaryPhaseDifference,
      ← Complex.coe_smul, smul_smul]
    congr 1
    ring
  rw [channelIntegral_bareChartInput T Q _ χ angular H z j _ hD, smul_smul,
    hraw, normalized_bare_wideBand_rawPhase_integral (Nat.succ_le_succ (Nat.zero_le m)) j hτ]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_wideBand (m + 1) 0)] with θ hθ
  by_cases hx : χ (adaptedPhysicalCoordinates T.data.adapted q) = 0
  · simp only [scalarAuxiliaryAmplitude, hx, Complex.ofReal_zero, zero_smul, smul_zero]
  have hθnorm : ‖θ‖ ≤ 2 := by
    have ht := mem_closedBall_zero_iff.mp hθ.1
    norm_num only [dyadicScale, pow_zero] at ht
    exact ht
  rw [scalarSlicePhase_eq_retained T Q center hρ hphase ha haR he heb z hb hzg hε
    (mul_ne_zero hτ (by positivity)) hscale q θ (hχa (subset_tsupport _ hx)) (hχρ hx) hθnorm]

/-- A single complete dyadic normal bound produces the actual whole physical
bare vector operator. Its norm constant has no ceiling, frequency or band-count
loss. `Family` supplies the displayed canonical phase/amplitude and full normal
bound from primitive current-map data. -/
theorem exists_retainedBareScalarWideOperator
    (G : UniformNormalGeometry ((m + 1) - 1) (m + 1)) (C : ℕ → ℝ)
    {a e b Csum : ℝ} (ha : 0 < a) (haR : 4 * a < T.family.radius)
    (he : 0 < e) (heb : 16 * e < b) (hGe : G.ε₀ = e)
    (hD : G.D = sliceInputDomain (m + 1)) (hCsum : 0 ≤ Csum)
    (χ : ContDiffBump (0 : Euclidean (m + 1)))
    (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ)
    (hang : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ) (hH : ContDiff ℝ ∞ H)
    (center : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) (hphase : closedBall center (2 * ρ) ⊆ domain T)
    (hχa : tsupport (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall 0 (a / 4))
    (hχρ : Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall center.1 (ρ / 2))
    (z : Euclidean 3)
    (hb : ball (T.reference.spatialPatch z) b ⊆
      ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)))
    (hzg : (z, T.reference.spatialPatch z) ∈ closedBall center.2 (ρ / 4))
    {J : ℕ} {τ : ℝ} (hτ : τ ≠ 0)
    (hε : ∀ j : Fin J, τ * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀)
    (hscale : ∀ j : Fin J, |τ * (2 : ℝ) ^ j.val| ≤ ρ / 8)
    (Ns : ℕ → (t : ℝ) → t ∈ Ioo (-a) a → UniformNormalData G C)
    (hNp : ∀ j t (ht : t ∈ Ioo (-a) a), (Ns j t ht).phase = canonicalSlicePhase T Q z t)
    (hNa : ∀ j t (ht : t ∈ Ioo (-a) a), (Ns j t ht).amplitude = fun _ y θ ↦
      scalarSliceAmplitude T.data.adapted χ angular H (Nat.succ_le_succ (Nat.zero_le m)) j (t, y, θ))
    (hbound : ∀ t (ht : t ∈ Ioo (-a) a),
      ‖∑ j : Fin J, (Ns j.val t ht).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (τ * (2 : ℝ) ^ j.val) ∘L
        ((Ns j.val t ht).uniformOscillatoryOperator ((2 : ℝ) ^ j.val) (τ * (2 : ℝ) ^ j.val)).adjoint‖ ≤ Csum) :
    ∃ L : WideInput (m + 1) J →L[ℂ]
        Lp (EuclideanSpace ℂ (Fin (m + 1))) 2 (volume : Measure (Euclidean (m + 1))),
      (∀ f, L f =ᵐ[volume] fun x ↦ ∑ j : Fin J,
        ∫ η in wideBand (m + 1) j.val, f j η •
          retainedBareScalarVectorKernel T Q χ angular H center.2.1 z hρ τ j.val x η) ∧
      ‖L‖ ^ 2 ≤ ((2 * Real.pi) ^ (-(1 : ℝ) / 2)) ^ 2 * (8 * a * Csum) := by
  classical
  let k := fun j : Fin J ↦ scalarFullBandChannelKernel T Q (Nat.succ_le_succ (Nat.zero_le m))
    χ angular H z j.val (τ * (2 : ℝ) ^ j.val)
  have hk (j : Fin J) := scalarFullBandChannelKernel_properties T Q
    (Nat.succ_le_succ (Nat.zero_le m)) ha haR he heb z hb χ angular H hang hH hχa j.val
    (by simpa only [hGe] using hε j)
  obtain ⟨L, hL, hLn⟩ := exists_fullBand_physical_slice_operator G C (by linarith : -a ≤ a)
    hCsum (fun j t ht ↦ Ns j.val t ht) (fun j ↦ (2 : ℝ) ^ j.val)
    (fun j ↦ τ * (2 : ℝ) ^ j.val) hε hbound k (fun j ↦ (hk j).1)
    (fun j ↦ (hk j).2.1) (fun j ↦ (hk j).2.2) (fun j t ht y θ i ↦ by
      rw [hNp j.val t ht, hNa j.val t ht]
      rfl)
  let c₀ := (2 * Real.pi) ^ (-(1 : ℝ) / 2)
  let Lbare := c₀ • L.comp (bareChartRow (m + 1) J G.D)
  have hLb (f) : Lbare f =ᵐ[volume] fun q ↦ ∑ j : Fin J,
      ∫ η in wideBand (m + 1) j.val, f j η •
        retainedBareScalarVectorKernel T Q χ angular H center.2.1 z hρ τ j.val
          (adaptedPhysicalCoordinates T.data.adapted q) η := by
    filter_upwards [Lp.coeFn_smul c₀ (L (bareChartRow (m + 1) J G.D f)),
      hL (bareChartRow (m + 1) J G.D f)] with q hs hl
    change (c₀ • L (bareChartRow (m + 1) J G.D f)) q = _
    rw [hs, Pi.smul_apply, hl, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact bareChannelIntegral_eq_retained T Q χ angular H center hρ hphase ha haR he heb
      hχa hχρ z hb hzg hD hτ j.val (by simpa only [hGe] using hε j) (hscale j) (f j) q
  have hLbn : ‖Lbare‖ ^ 2 ≤ c₀ ^ 2 * (8 * a * Csum) := by
    have hb := (ContinuousLinearMap.opNorm_comp_le L (bareChartRow (m + 1) J G.D)).trans
      (mul_le_mul_of_nonneg_left (norm_bareChartRow_le (m + 1) J G.D) (norm_nonneg L))
    have hb₂ := pow_le_pow_left₀ (norm_nonneg _) hb 2
    calc
      _ = c₀ ^ 2 * ‖L.comp (bareChartRow (m + 1) J G.D)‖ ^ 2 := by
        change ‖c₀ • L.comp (bareChartRow (m + 1) J G.D)‖ ^ 2 = _
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      _ ≤ c₀ ^ 2 * ((‖L‖ * 2) ^ 2) := mul_le_mul_of_nonneg_left hb₂ (sq_nonneg _)
      _ ≤ c₀ ^ 2 * (((a - -a) * Csum) * 4) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        nlinarith [hLn]
      _ = _ := by ring
  refine ⟨(adaptedL2Equiv T.data.adapted (EuclideanSpace ℂ (Fin (m + 1)))).toContinuousLinearEquiv.toContinuousLinearMap.comp Lbare,
    ?_, ?_⟩
  · intro f
    filter_upwards [adaptedL2Equiv_coeFn T.data.adapted (EuclideanSpace ℂ (Fin (m + 1))) (Lbare f),
      (adaptedPhysicalCoordinates_symm_measurePreserving T.data.adapted).quasiMeasurePreserving.ae (hLb f)]
      with x hx hy
    change adaptedL2Equiv T.data.adapted (EuclideanSpace ℂ (Fin (m + 1))) (Lbare f) x = _
    rw [hx, Function.comp_apply, hy]
    simp only [MeasurableEquiv.apply_symm_apply]
  · rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp]
    exact hLbn

/-- The bare physical scalar row is actually produced from the original current
immersion, not assumed as an operator input. The physical/parameter caps precede
the scalar cutoff, all primitive budgets precede the current map, and the final
constant precedes every inverse frequency and every band count. -/
theorem exists_original_bare_scalar_wide_family
    (hn : 2 ≤ m + 1) {c C₀ : ℝ} (hP : P.IsValid c C₀)
    {amax bmax emax : ℝ} (hamax : 0 < amax) (hbmax : 0 < bmax) (hemax : 0 < emax) :
    ∃ a > (0 : ℝ), 4 * a ≤ amax ∧
    ∃ e > (0 : ℝ), e ≤ emax ∧
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
    ∀ (χ : ContDiffBump (0 : Euclidean (m + 1))),
      tsupport (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall 0 (a / 4) →
    ∀ (angular : Euclidean (m + 1 - 1) → ℂ) (H : Euclidean (m + 1 - 1) → ℝ),
      (∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ) →
      (∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ) →
      ContDiff ℝ ∞ H → (∀ η, 2 ≤ ‖η‖ → H η = 1) →
    ∀ {K : Set (Euclidean (m + 1))}, IsCompact K → K ⊆ U →
      closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ K →
    ∀ (M : ℝ) {γ κ : ℝ}, 0 < γ → 0 < κ →
    ∃ Cbare > (0 : ℝ),
    ∀ (F : Euclidean (m + 1) → Euclidean (embeddingDimension (m + 1)))
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm K (20 * ((m + 1 - 1) + 1) + 5) F ≤ M →
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < δ →
    ∃ hlow : cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
    let Q := ⟨projectedStress F,
      contDiffOn_pi.mpr (ProjectedStressFrame.contDiffOn_projectedStress hU hF hi hrank), hlow⟩
    ∀ (center : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
      {ρ : ℝ} (hρ : 0 < ρ),
      closedBall center (2 * ρ) ⊆ domain T →
      Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall center.1 (ρ / 2) →
    ∀ z ∈ parameterCube P.radius,
      (z, T.reference.spatialPatch z) ∈ closedBall center.2 (ρ / 4) →
    ∀ (J : ℕ) {τ : ℝ}, τ ≠ 0 →
      (∀ j : Fin J, τ * (2 : ℝ) ^ j.val ∈ Icc 0 e) →
      (∀ j : Fin J, |τ * (2 : ℝ) ^ j.val| ≤ ρ / 8) →
    ∃ L : WideInput (m + 1) J →L[ℂ]
        Lp (EuclideanSpace ℂ (Fin (m + 1))) 2 (volume : Measure (Euclidean (m + 1))),
      (∀ f, L f =ᵐ[volume] fun x ↦ ∑ j : Fin J,
        ∫ η in wideBand (m + 1) j.val, f j η •
          retainedBareScalarVectorKernel T Q χ angular H center.2.1 z hρ τ j.val x η) ∧
      ‖L‖ ^ 2 ≤ Cbare := by
  obtain ⟨a, ha, hacap, haR, b, _hb, _hbcap, hbcov, e, he, hecap, heb,
    δ, hδ, hδcap, G, _hX, hD, _hX₀, _hD₀, hGe, hbuild⟩ :=
    exists_retained_scalar_full_band_slice_family T hn hP hamax hbmax hemax
  refine ⟨a, ha, hacap, e, he, hecap, δ, hδ, hδcap, ?_⟩
  intro χ hχ angular H hang hah hH hH₁ K hK hKU hball M γ κ hγ hκ
  obtain ⟨Cnormal, _hCnormal, Csum, hCsum, hcurrent⟩ :=
    hbuild χ hχ angular H hang hah hH hH₁ hK hKU hball M hγ hκ
  refine ⟨((2 * Real.pi) ^ (-(1 : ℝ) / 2)) ^ 2 * (8 * a * Csum), by positivity, ?_⟩
  intro F hF hi hrank hFM hmetric hnormal hsmall
  obtain ⟨hlow, hfamily⟩ := hcurrent F hF hi hrank hFM hmetric hnormal hsmall
  refine ⟨hlow, ?_⟩
  intro Q center ρ hρ hphase hχρ z hz hzg J τ hτ hε hscale
  obtain ⟨Ns, hNp, hNa, hsum⟩ := hfamily z hz
  apply exists_retainedBareScalarWideOperator T Q G Cnormal ha haR he heb hGe hD hCsum.le
    χ angular H hang hH center hρ hphase hχ hχρ z (hbcov z hz) hzg hτ
    (fun j ↦ by simpa only [hGe] using hε j) hscale Ns hNp hNa
  exact hsum J (fun j ↦ τ * (2 : ℝ) ^ j.val) (fun j ↦ by simpa only [hGe] using hε j)

end JanetCartan.PhysicalScalarChannel
