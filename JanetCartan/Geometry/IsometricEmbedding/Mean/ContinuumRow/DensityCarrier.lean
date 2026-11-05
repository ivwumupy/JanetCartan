module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ActualCarrier
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.InitialScalar

/-!
# Uniform local carriers for the original initial-density class

The prescribed scalar is literally `σ * sqrt (1 + v)`. Its smoothness,
positivity and low norm are derived on the SAME initial domain. Thus the local
carrier has a fixed operator bound throughout the manuscript's finite-low
density class; no initial-amplitude estimate or channel bound is assumed.
The fixed map order below is supplied along histories by
`HistoryGeometry.exists_initialScale_for_fixed_immersion_bound`.

The parent retains common reference/history choices, finite incidence coverage
and identification with the full leading family. This is the local operator
construction for `app:ch_background:defn:bg-row` and the density class of
`app:ch_background:prop:bg-frame`, not the coercivity or inverse theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.CanonicalCarrier
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open ActualFlow FlowAmplitude ProjectedStressFrame FullPhaseCharts.ActualComparison
open CanonicalConic ContinuumNormalReduction TransportSymbol TransportKernel
open CarrierNormalRealization Pseudodifferential AmplitudeBound PeriodicLocalL2

/-- The finite map/initial-density order needed for the L² carrier bound:
PDO source reserve `2(n+1)` plus the proved primitive reserve fourteen
(`app:ch_background:prop:bg-frame`, Step 1). -/
def canonicalCarrierLowOrder (n : ℕ) : ℕ := 2 * (n + 1) + 14

/-- Actual uncut carrier for the entire fixed-low density class. Both the
positive transport and its scalar budget are constructed; the bound is uniform
in the current immersion and density. The SAME operator has the literal
adjoint, supported global reflected normal and every smaller common-cutoff
restriction (`app:ch_background:defn:bg-row`, `bg-T`, `bg-realification`). -/
theorem exists_actual_density_carrier {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {M κmet κ σ : ℝ} (hM : 0 ≤ M) (hσ : 0 < σ)
    (hκmet : 0 < κmet) (hκ : 0 < κ) {cap : ℝ} (hcap : 0 < cap) :
    ∃ row col : Fin n, ∃ R τ : ℝ, 0 < R ∧ 0 < τ ∧ τ ≤ R / 16 ∧
    ∃ t > (0 : ℝ), ‖t • k‖ = 1 / 4 ∧
      NormedSpace.normalize (t • k) = NormedSpace.normalize k ∧
      NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)) =
        NormedSpace.normalize (T.data.adapted.embedding.toContinuousLinearMap.adjoint k) ∧
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint (t • k)
    ∃ (r a r' a' : ℝ) (hr : 0 < r) (ha : 0 < a) (hr' : 0 < r') (ha' : 0 < a')
      (hcell' : 4 * a' < 1 / 2) (hηb : ηb ≠ 0),
      6 * a < cap ∧ r' ≤ r ∧ a' ≤ a ∧ a' ≤ r' ∧
    ∃ δ > (0 : ℝ), ∃ Bop > (0 : ℝ), ∃ Cpdo > (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K (canonicalCarrierLowOrder n) F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
      ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      let Ccoord := coordinates (adaptedCoordinates T.data.adapted)
      let p₀ := ((0 : Euclidean (n - 1)), z₀)
      ∃ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
      ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
        IsOpen D ∧ Ioo (-τ) τ ×ˢ ball p₀ (R / 32) ⊆ D ∧
        D ⊆ Ioo (-τ) τ ×ˢ ball p₀ (R / 4) ∧
        (∀ p ∈ ball p₀ (R / 8), Φ (0, p) = p) ∧
        (∀ p ∈ ball p₀ (R / 8), ∀ t ∈ Ioo (-τ) τ, Y (t, Φ (t, p)) = p) ∧
        (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧ (∀ q ∈ D, (Y q).2 = q.2.2) ∧
        ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
          ContDiffOn ℝ ∞ v (ball p₀ (R / 4)) →
          (∀ p ∈ ball p₀ (R / 4), 0 < 1 + v p) →
          (∀ p ∈ closedBall p₀ (R / 8), 1 + v p ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
          cNorm (closedBall p₀ (R / 8)) (canonicalCarrierLowOrder n) v ≤ 1 →
        let initial := fun p ↦ positiveDensityAmplitude σ (v p)
        let α := carrierScalarAmplitude T Q F row col Φ Y initial
        let e := data T Q F row col Φ Y initial ha' hcell'
          (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
          FixedCutoffs.highFrequency
        let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
        let J := symbolJacobian T Q
        let u := symbolInverse T Q z₀ ηb r (6 * a)
        let Ω := symbolDomain T Q z₀ ηb r (6 * a)
        let S := closedBall (spectatorCenter z₀) (a' / 2)
        let H := 1 + cNorm K (canonicalCarrierLowOrder n) F +
          cNorm (closedBall p₀ (R / 8)) (canonicalCarrierLowOrder n) initial
        ContDiffOn ℝ ∞ α (Ccoord ⁻¹' D) ∧
        (∀ p ∈ ball p₀ (R / 8), α (T.data.adapted.embedding p.1, p.2) = initial p) ∧
        (∀ w ∈ Ccoord ⁻¹' D, 0 < α w) ∧
        (∀ w ∈ Ccoord ⁻¹' D,
          fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q row col w) +
            carrierTransportPotential T Q F row col w * α w = 0) ∧
      ∃ hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a',
      ∃ (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude d J u Ω S)))
        (hA : ∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ fullReflectedMatrixAmplitude d J u Ω S ξ z i j) (2 * (n + 1)) (Cpdo * H)),
      ∃ V : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        ‖V‖ ≤ Bop ∧
        ‖V.adjoint‖ ≤ Bop ∧
        (∀ v : carrierInitialTestSpace n,
          V (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) ∧
        (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → V f x = 0) ∧
        (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ v : carrierInitialTestSpace n,
            W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) → W = V) ∧
        (∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
          V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) ∧
        (realQuadratureChannel V).comp (realQuadratureChannel V).adjoint =
          realOutputCompression (transferOperator
            (vectorTwoPositionL2Operator (by omega) (4 * a')
              (fullReflectedMatrixAmplitude d J u Ω S) hb
              (fullReflectedMatrixAmplitude_supportedInCenteredBox
                d J u Ω S (4 * a') hsupport)
              (Cpdo * H) hA)) ∧
        ∀ {b : ℝ} (hb : 0 < b) (hbcell : 4 * b < 1 / 2), 6 * b < a' →
          let χ := FixedCutoffs.periodic (n := n) hb hbcell 1
          let Vb := CommonMeasurement.restrictCarrier χ V
          let eb := data T Q F row col Φ Y initial hb hbcell
            (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
            FixedCutoffs.highFrequency
          ‖Vb‖ ≤ Bop ∧
          (∀ v : carrierInitialTestSpace n,
            Vb (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral eb v.val) ∧
          (∀ w : ComplexOutputL2 n,
            MemLp (carrierAdjointIntegral eb w) 2 (carrierMeasure n) ∧
            Vb.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral eb w) ∧
          (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ eb.outputChart → Vb f x = 0) ∧
          carrierChannel Vb ∘L (carrierChannel Vb).adjoint =
            cutoffMultiplier χ ∘L
              (carrierChannel V ∘L (carrierChannel V).adjoint) ∘L cutoffMultiplier χ := by
  obtain ⟨C₁₅, hC₁₅, hscalar₁₅⟩ := exists_density_initial_scalar_bound n 15
  obtain ⟨Cd, hCd, hscalard⟩ := exists_density_initial_scalar_bound n (canonicalCarrierLowOrder n)
  have hlocal :=
    exists_actual_canonical_carrier (n := n) (N := N) (M₁₅ := M) (Mᵣ := σ * C₁₅) hn hP T hK hKU hball hz₀ hk hinc hd
      hM (mul_nonneg hσ.le hC₁₅.le) hκmet hκ hcap (2 * (n + 1)) le_rfl
  obtain ⟨row, col, R, τ, hR, hτ, hτR, hlocal⟩ := hlocal
  obtain ⟨t, ht, htnorm, hdir, hηdir, hlocal⟩ := hlocal
  obtain ⟨r, a, r', a', hlocal⟩ := hlocal
  obtain ⟨hr, ha, hr', ha', hcell', hηb, hlocal⟩ := hlocal
  obtain ⟨hacap, hrr, haa, har, hlocal⟩ := hlocal
  obtain ⟨δ, hδ, Cnorm, hCnorm, Cpdo, hCpdo, Cmask, hCmask, hcarrier⟩ := hlocal
  let Hmax := 1 + M + σ * Cd
  let Bop := Real.sqrt ((n : ℝ) ^ 2 *
    (fixedBoxAmplitudeConstant n (4 * a') * (Cnorm * Hmax))) + 1
  have hBop : 0 < Bop := by dsimp [Bop]; positivity
  refine ⟨row, col, R, τ, hR, hτ, hτR, t, ht, htnorm, hdir, hηdir,
    r, a, r', a', hr, ha, hr', ha', hcell', hηb, hacap, hrr, haa, har,
    δ, hδ, Bop, hBop, Cpdo, hCpdo, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  have hFM₁₅ : cNorm K 15 F ≤ M :=
    (cNorm_mono_order (by dsimp [canonicalCarrierLowOrder]; omega)).trans hFM
  obtain ⟨hlow, D, Φ, Y, hD, hsmall, hbig, hΦ₀, hYΦ, hΦY, hYcarrier, hscalar⟩ :=
    hcarrier F hF hi hrank hFM₁₅ hmet hnormal hclose
  refine ⟨hlow, D, Φ, Y, hD, hsmall, hbig, hΦ₀, hYΦ, hΦY, hYcarrier, ?_⟩
  intro v hv hpos hinterval hvnorm
  obtain ⟨hinitial, hpositive, _, hinitialBound⟩ :=
    hscalar₁₅ _ hR hσ v hv hpos hinterval
      ((cNorm_mono_order (by dsimp [canonicalCarrierLowOrder]; omega)).trans hvnorm)
  have hinitialHigh := (hscalard _ hR hσ v hv hpos hinterval hvnorm).2.2.2
  obtain ⟨hα, hα₀, hαpos, htransport, hsupport, Lmask, hLmask, Mmask, hMmask,
    hmask, hfinite, htestBound, hb, hA, V, hV, hVadj, hVtest, hVsupp,
    hVunique, hVliteral, hVlimit, hVnormal, hcommon⟩ :=
    hscalar (fun p ↦ positiveDensityAmplitude σ (v p)) hinitial hpositive hinitialBound
  have hH : 1 + cNorm K (canonicalCarrierLowOrder n) F +
      cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (canonicalCarrierLowOrder n)
        (fun p ↦ positiveDensityAmplitude σ (v p)) ≤ Hmax := by
    exact add_le_add (add_le_add le_rfl hFM) hinitialHigh
  have hbound : Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a') *
      (Cnorm * (1 + cNorm K (canonicalCarrierLowOrder n) F +
        cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (canonicalCarrierLowOrder n)
          (fun p ↦ positiveDensityAmplitude σ (v p)))))) ≤ Bop := by
    apply (Real.sqrt_le_sqrt ?_).trans (le_add_of_nonneg_right zero_le_one)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH hCnorm.le)
        (fixedBoxAmplitudeConstant_nonneg n (4 * a'))) (sq_nonneg _)
  refine ⟨hα, hα₀, hαpos, htransport, hsupport, hb, hA, V,
    hV.trans hbound, hVadj.trans hbound, hVtest, hVsupp, hVunique, hVliteral, hVnormal, ?_⟩
  intro b hb hbcell hba
  obtain ⟨hVb, hVbtest, hVbadj, hVbsupp, hVbnormal⟩ := hcommon hb hbcell hba
  exact ⟨hVb.trans hbound, hVbtest, hVbadj, hVbsupp, hVbnormal⟩

end JanetCartan.ContinuumRow.CanonicalCarrier
