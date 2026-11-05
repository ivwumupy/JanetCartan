module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.DensityFreezing.FixedMeasurement
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.Exterior
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.SeedGap

/-!
# Absorb the original-density spatial error on the initialized row

The frozen seed producer supplies its literal density-weighted row and local
gap. The full-amplitude spatial estimate compares it with the divided-footpoint
zero limit. Shrink only the inner support, before the density is chosen, and
complete the exterior with `(1-ψ)^2`. A uniform bound for the actual physical
row follows from its full reflected normals; it is not a further hypothesis.

The common retained inverse geometry and actual carrier-normal identities must
still be instantiated by normalized selection and normal variation. The
`μ+1` amplitude bounds used below are produced by `ZeroAmplitude` on that
geometry. This deduction does not assert the missing common-family construction.
Consumers: `NormalizedNormalLimit.exists_source_family_half_gap`,
`CoerciveNormal`, `NormalizedBackground` and `ContinuumInverse`.
Sources: `app:ch_background:prop:bg-frame`, `bg-local-bound`, `bg-global-bound`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace NNReal Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.ActualConstruction
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier CanonicalConic CommonMeasurement
open FullPhaseCharts ActualComparison
open FrozenModel RetainedFrozen FrozenImageComparison FrozenCoercivity
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open CarrierVariation.FamilyInputs.WideDensity Pseudodifferential AmplitudeBound PeriodicLocalL2

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The reflected normal budgets bound the same measured physical row, so
exterior completion has a density-independent constant
(`app:ch_background:prop:bg-frame`, Step 4). -/
private theorem measured_physicalRow_norm_le_of_normal_bounds
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (χ : C(Torus n, ℝ)) (hχ : ‖χ‖ ≤ 1)
    (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (D : ι → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hN : ∀ i, ‖carrierChannel (V i) ∘L (carrierChannel (V i)).adjoint‖ ≤ D i) :
    ‖physicalRow image (fun i ↦ restrictCarrier χ (V i))‖ ≤
      Real.sqrt (‖image‖ ^ 2 + ∑ i, D i) := by
  have hm : ‖cutoffMultiplier χ‖ ≤ 1 := (cutoffMultiplier_norm_le χ).trans hχ
  have hrestr (i : ι) : ‖carrierChannel (restrictCarrier χ (V i)) ∘L
      (carrierChannel (restrictCarrier χ (V i))).adjoint‖ ≤ D i := by
    rw [carrierChannel_restrictCarrier_normal]
    calc
      _ ≤ ‖cutoffMultiplier χ‖ *
          ‖carrierChannel (V i) ∘L (carrierChannel (V i)).adjoint‖ *
          ‖cutoffMultiplier χ‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * D i * 1 :=
        mul_le_mul (mul_le_mul hm (hN i) (norm_nonneg _) zero_le_one) hm
          (norm_nonneg _) (by simpa only [one_mul] using hD i)
      _ = D i := by ring
  apply (Real.le_sqrt (norm_nonneg _) (add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ ↦ hD i))).mpr
  rw [← NormalPerturbation.norm_normal]
  change ‖physicalRow image (fun i ↦ restrictCarrier χ (V i)) ∘L
    (physicalRow image (fun i ↦ restrictCarrier χ (V i))).adjoint‖ ≤ _
  rw [physicalRow_normal]
  apply (norm_add_le _ _).trans
  have hi : ‖image ∘L image.adjoint‖ = ‖image‖ ^ 2 := NormalPerturbation.norm_normal image
  rw [hi]
  exact add_le_add le_rfl ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ hrestr i))

/-- The initialized frozen local gap survives the actual divided-footpoint
density limit. The inner radius, both positive gaps and the physical-row bound
precede every allowed density and every realizing operator. The SAME frozen
row is selected from `InitializedFrozenSeedGap`, and its original measurement
and source masks remain fixed. The full-amplitude bounds and literal normal
identities are precisely the published primitive inputs; they must still be
instantiated on the common normalized family before actual construction is
complete. No weighted-limit gap or operator-continuity estimate is assumed.

Producer of the finite bounds: `exists_source_zero_density_reflected_bounds`.
Producer of matching realizations: normalized selection with normal variation.
Consumer: `NormalizedNormalLimit.exists_source_family_half_gap` and the actual
auxiliary inverse (`app:ch_background:eq:bg-local-bound`, `bg-global-bound`). -/
theorem exists_initialized_source_density_limit_coercivity
    (hn : 0 < n)
    {P : ι → Patch n} {U₀ : Set (Euclidean n)} {hU₀ : IsOpen U₀}
    (T : ∀ i, PatchQuantitativeFamily (P i) U₀ hU₀)
    (Q : ∀ i, {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U₀ ∧
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T i).family.threshold})
    (F : Euclidean n → Euclidean (embeddingDimension n)) (row col : ι → Fin n)
    (Φ Y : ι → ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z : ι → Euclidean 3) (ηb : ι → Euclidean (n - 1)) (r' a' : ι → ℝ)
    (hr' : ∀ i, 0 < r' i) (ha' : ∀ i, 0 < a' i) (hcell' : ∀ i, 4 * a' i < 1 / 2)
    (hηb : ∀ i, ηb i ≠ 0) (zc : ι → Euclidean 3) (L : ι → ℝ)
    (hseed : InitializedFrozenSeedGap T Q F row col Φ Y z ηb r' a' hr' ha' hcell' hηb zc L)
    {μ : ℝ} (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2) (hμa : ∀ i, 6 * μ < a' i)
    (J : ι → InputVariables n → ℝ)
    (u : ι → Variables n × Euclidean 2 → SliceVariable n)
    (Ω : ι → Set (Variables n × Euclidean 2)) (S : ι → Set (Euclidean 2))
    (B : ι → ℝ≥0) :
    let a := fun i ↦ TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData (T i) (Q i) F (row i) (col i) (Φ i) (Y i) (fun _ ↦ 1)
        (ha' i) (hcell' i)
        (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i)
          (angularWidth_spec (hηb i) (hr' i)).1) FixedCutoffs.highFrequency 0)
      (FixedCutoffs.physical (ha' i) 1)
    let weighted := fun (v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ) i (t : Bool) ↦
      {a i with normal := fun p ↦ Real.sqrt (1 + v i
        (if t then sourceDensityFootpointExtension (T i) (Y i) (0, p) else (0, parameter p.2))) •
          (a i).normal p}
    let b := fun v i t ↦ fullReflectedMatrixAmplitude (weighted v i t) (J i) (u i) (Ω i) (S i)
    let χ := FixedCutoffs.periodic (n := n) hμ hμcell 1
    let image := fixedPeriodicChannel hμ hμcell (frozenImageArrays (ProjectedStressFrame.projectedStress F 0))
    ∃ g > (0 : ℝ), ∃ (rInner : ℝ) (hrInner : 0 < rInner) (hInnerCell : rInner < 1 / 2),
    ∃ M ≥ (0 : ℝ), rInner ≤ μ ∧
      0 < NormalAugmentation.globalGap g M ∧
      ∀ v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (v i) (ball ((0 : Euclidean (n - 1)), zc i) (L i / 4))) →
      (∀ i q, q ∈ closedBall ((0 : Euclidean (n - 1)), zc i) (L i / 8) →
        1 + v i q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      ∃ Vfrozen : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ i,
          let ei := normalizedCarrierData (T i) (Q i) F (row i) (col i) (Φ i) (Y i)
            (fun q ↦ Real.sqrt (1 + v i q)) (ha' i) (hcell' i)
            (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i)
              (angularWidth_spec (hηb i) (hr' i)).1) FixedCutoffs.highFrequency 0
          (∀ f : carrierInitialTestSpace n,
            Vfrozen i (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral ei f.val) ∧
          (∀ w : ComplexOutputL2 n, MemLp (carrierAdjointIntegral ei w) 2 (carrierMeasure n) ∧
            (Vfrozen i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral ei w)) ∧
        ∀ (hb : ∀ i t, ContDiff ℝ ∞ (Function.uncurry (b v i t)))
          (hB : ∀ i t j k, HasAmplitudeDerivativeBound (fun ξ z ↦ b v i t ξ z j k)
            (2 * (n + 1) + 1) (B i))
          (Vactual : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
        let V := fun i (t : Bool) ↦ if t then Vactual i else Vfrozen i
        let hs := fun i t ↦ fullReflectedMatrixAmplitude_supportedInCenteredBox
          (weighted v i t) (J i) (u i) (Ω i) (S i) (4 * a' i)
          (fun x hx j ↦ (PiLp.norm_apply_le x j).trans
            (mem_closedBall_zero_iff.mp (FixedCutoffs.physical_tsupport_four (ha' i) 1
              (subset_tsupport _ hx))))
        (∀ i t, carrierChannel (V i t) ∘L (carrierChannel (V i t)).adjoint =
          realOutputCompression (transferOperator
            (vectorTwoPositionL2Operator hn (4 * a' i) (b v i t) (hb i t) (hs i t)
              (B i) (fun j k ξ is his ↦ hB i t j k ξ is (by omega))))) →
        ‖physicalRow image (fun i ↦ restrictCarrier χ (Vactual i))‖ ≤ M ∧
        (∀ w : OutputL2 n,
          (∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) →
          g * ‖w‖ ^ 2 ≤ ‖(physicalRow image (fun i ↦ restrictCarrier χ (Vactual i))).adjoint w‖ ^ 2) ∧
        (∀ w : OutputL2 n, NormalAugmentation.globalGap g M * ‖w‖ ^ 2 ≤
          inner ℝ (augmentedNormal image (fun i ↦ restrictCarrier χ (Vactual i))
            (innerCutoff hrInner hInnerCell) w) w) ∧
        (∀ w : OutputL2 n, NormalAugmentation.globalGap g M * ‖w‖ ^ 2 ≤
          ‖(augmentedRow image (fun i ↦ restrictCarrier χ (Vactual i))
            (innerCutoff hrInner hInnerCell)).adjoint w‖ ^ 2) ∧
        (∀ w : OutputL2 n, ∀ᵐ x ∂volume,
          centeredTorusRepresentative x ∈ closedBall 0 (rInner / 2) →
            exteriorChannel (innerCutoff hrInner hInnerCell) w x = 0) := by
  classical
  dsimp only
  let a := fun i ↦ TransportKernel.coefficientsOfCarrier
    (normalizedCarrierData (T i) (Q i) F (row i) (col i) (Φ i) (Y i) (fun _ ↦ 1)
      (ha' i) (hcell' i)
      (angularMask (z i) (NormedSpace.normalize (ηb i)) (ha' i)
        (angularWidth_spec (hηb i) (hr' i)).1) FixedCutoffs.highFrequency 0)
    (FixedCutoffs.physical (ha' i) 1)
  let weighted := fun (v : ι → Euclidean (n - 1) × Euclidean 3 → ℝ) i (t : Bool) ↦
    {a i with normal := fun p ↦ Real.sqrt (1 + v i
      (if t then sourceDensityFootpointExtension (T i) (Y i) (0, p) else (0, parameter p.2))) •
        (a i).normal p}
  let b := fun v i t ↦ fullReflectedMatrixAmplitude (weighted v i t) (J i) (u i) (Ω i) (S i)
  let χ := FixedCutoffs.periodic (n := n) hμ hμcell 1
  let image := fixedPeriodicChannel hμ hμcell (frozenImageArrays (ProjectedStressFrame.projectedStress F 0))
  obtain ⟨γ, hγ, Vunit, _, _, hgap⟩ := hseed
  obtain ⟨r₀, hr₀, hr₀cell, hr₀μ, _, _, _, _, hdensity⟩ := hgap μ hμ hμcell hμa
  choose C hC herror using fun i ↦ exists_fixed_measurement_sourceDensityLimit_error_constant hn (ha' i)
  let g₀ := (γ / 2) / 16
  have hg₀ : 0 < g₀ := by dsimp [g₀]; positivity
  let K := ∑ i, C i * ((B i : ℝ) + B i)
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ ↦ mul_nonneg (hC i).le (by positivity)
  let rInner := min r₀ (g₀ / (2 * (K + 1)))
  have hrInner : 0 < rInner := lt_min hr₀ (div_pos hg₀ (by positivity))
  have hrInner₀ : rInner ≤ r₀ := min_le_left _ _
  have hrInnerμ : rInner ≤ μ := hrInner₀.trans hr₀μ
  have hInnerCell : rInner < 1 / 2 := hrInner₀.trans_lt hr₀cell
  have hsmall : K * rInner ≤ g₀ / 2 := by
    have h := (le_div_iff₀ (show 0 < 2 * (K + 1) by positivity)).mp
      (min_le_right r₀ (g₀ / (2 * (K + 1))))
    change rInner * (2 * (K + 1)) ≤ g₀ at h
    nlinarith
  let D := fun i ↦ (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n (4 * a' i) * B i)
  have hD : ∀ i, 0 ≤ D i := fun i ↦ mul_nonneg (sq_nonneg _)
    (mul_nonneg (fixedBoxAmplitudeConstant_nonneg ..) (B i).coe_nonneg)
  let M := Real.sqrt (‖image‖ ^ 2 + ∑ i, D i)
  refine ⟨g₀ / 2, half_pos hg₀, rInner, hrInner, hInnerCell, M, Real.sqrt_nonneg _,
    hrInnerμ, NormalAugmentation.globalGap_pos (half_pos hg₀), ?_⟩
  intro v hv hinterval
  obtain ⟨β, hβ, hβBound, hreal, hfrozen, _⟩ := hdensity v hv hinterval
  let Vfrozen := fun i ↦ Vunit i ∘L InitialMultiplier.labelMultiplier
    (β i) (hβ i).continuous (hβBound i)
  refine ⟨Vfrozen, fun i ↦ ⟨(hreal i).2.2.2.2.1, (hreal i).2.2.2.2.2.1⟩, ?_⟩
  intro hb hB Vactual hnormal
  let V := fun i (t : Bool) ↦ if t then Vactual i else Vfrozen i
  have hMeas (i : ι) : ∀ x, (a i).measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a' i := by
    intro x hx j
    exact (PiLp.norm_apply_le x j).trans
      (mem_closedBall_zero_iff.mp (FixedCutoffs.physical_tsupport_four (ha' i) 1
        (subset_tsupport _ hx)))
  let hs := fun i t ↦ fullReflectedMatrixAmplitude_supportedInCenteredBox
    (weighted v i t) (J i) (u i) (Ω i) (S i) (4 * a' i) (hMeas i)
  let N := fun i t ↦ realOutputCompression (transferOperator
    (vectorTwoPositionL2Operator hn (4 * a' i) (b v i t) (hb i t) (hs i t)
      (B i) (fun j k ξ is his ↦ hB i t j k ξ is (by omega))))
  have hN : ∀ i t, carrierChannel (V i t) ∘L (carrierChannel (V i t)).adjoint = N i t := hnormal
  have hNbound (i : ι) : ‖N i true‖ ≤ D i :=
    (fullReflectedMatrixAmplitude_operator_bounds (weighted v i true) (J i) (u i) (Ω i) (S i)
      (hb i true) (2 * (n + 1) + 1) (B i) (hB i true) hn (4 * a' i) (hMeas i) (by omega)).2.2
  have hM : ‖physicalRow image (fun i ↦ restrictCarrier χ (Vactual i))‖ ≤ M :=
    measured_physicalRow_norm_le_of_normal_bounds image χ
      (FixedCutoffs.periodic_norm_le_one hμ hμcell 1) Vactual D hD
      (fun i ↦ by rw [show Vactual i = V i true from rfl, hN]; exact hNbound i)
  have hlocal (w : OutputL2 n)
      (hw : ∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) rInner → w x = 0) :
      g₀ / 2 * ‖w‖ ^ 2 ≤
        ‖(physicalRow image (fun i ↦ restrictCarrier χ (Vactual i))).adjoint w‖ ^ 2 := by
    have hw₀ : ∀ᵐ x ∂volume, x ∉ torusQuotient '' ball (0 : Euclidean n) r₀ → w x = 0 := by
      filter_upwards [hw] with x hx hxr
      exact hx (fun hh ↦ hxr ((image_mono (ball_subset_ball hrInner₀)) hh))
    have hwChart : ∀ᵐ x ∂volume, x ∉ torusChart (closedBall (0 : Euclidean n) rInner) → w x = 0 := by
      have hballChart := torusChart_eq_image (innerBall_subset_cell (n := n) hμ hμcell hrInnerμ)
      filter_upwards [hw] with x hx hxr
      apply hx
      intro hxi
      apply hxr
      exact (show torusChart (ball (0 : Euclidean n) rInner) ⊆
        torusChart (closedBall (0 : Euclidean n) rInner) from preimage_mono ball_subset_closedBall)
          (hballChart.symm ▸ hxi)
    have hwχ : cutoffMultiplier χ w = w := fixedCutoff_fixes_supported hμ hμcell hrInnerμ 1 w hw
    have henergy (i : ι) (t : Bool) :
        ‖(carrierChannel (restrictCarrier χ (V i t))).adjoint w‖ ^ 2 = inner ℝ (N i t w) w := by
      rw [carrierChannel_restrictCarrier, ContinuousLinearMap.adjoint_comp, cutoffMultiplier_adjoint,
        ContinuousLinearMap.comp_apply, hwχ]
      have he := (carrierChannel (V i t)).adjoint.apply_norm_sq_eq_inner_adjoint_left w
      simpa only [ContinuousLinearMap.adjoint_adjoint, RCLike.re_to_real, ← hN] using he
    have herr (i : ι) :
        ‖(carrierChannel (restrictCarrier χ (V i false))).adjoint w‖ ^ 2 ≤
          ‖(carrierChannel (restrictCarrier χ (V i true))).adjoint w‖ ^ 2 +
            C i * ((B i : ℝ) + B i) * rInner * ‖w‖ ^ 2 := by
      have hrMeas : rInner ≤ a' i := by linarith [hμa i]
      have he := herror i (T i) (Y i) (v i) (a i) (J i) (u i) (Ω i) (S i) rfl
        (hb i true) (hb i false) (B i) (B i) (hB i true) (hB i false)
        rInner ⟨hrInner.le, hrMeas⟩ w hwChart
      change |inner ℝ ((N i true - N i false) w) w| ≤ _ at he
      simp only [sub_apply, inner_sub_left] at he
      rw [henergy, henergy]
      linarith [(abs_le.mp he).1]
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ herr i)
    rw [Finset.sum_add_distrib] at hsum
    have hsumError : (∑ i, C i * ((B i : ℝ) + B i) * rInner * ‖w‖ ^ 2) =
        K * rInner * ‖w‖ ^ 2 := by simp only [K, Finset.sum_mul]
    rw [hsumError] at hsum
    have hgapw := hfrozen w hw₀
    rw [physicalRow_adjoint_norm_sq] at hgapw ⊢
    change g₀ * ‖w‖ ^ 2 ≤ ‖image.adjoint w‖ ^ 2 +
      ∑ i, ‖(carrierChannel (restrictCarrier χ (V i false))).adjoint w‖ ^ 2 at hgapw
    change g₀ / 2 * ‖w‖ ^ 2 ≤ ‖image.adjoint w‖ ^ 2 +
      ∑ i, ‖(carrierChannel (restrictCarrier χ (V i true))).adjoint w‖ ^ 2
    have hsmallw := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖w‖)
    linarith
  have hglobal (w : OutputL2 n) : NormalAugmentation.globalGap (g₀ / 2) M * ‖w‖ ^ 2 ≤
      inner ℝ (augmentedNormal image (fun i ↦ restrictCarrier χ (Vactual i))
        (innerCutoff hrInner hInnerCell) w) w :=
    NormalAugmentation.augmentedNormal_uniform_gap_of_local_coercivity _
      (cutoffMultiplier (innerCutoff hrInner hInnerCell))
      (ContinuousLinearMap.isSelfAdjoint_iff'.mpr (cutoffMultiplier_adjoint _))
      (cutoffMultiplier (innerCutoff hrInner hInnerCell)).toLinearMap.range
      (half_pos hg₀) hM (fun f ↦ ⟨f, rfl⟩)
      (fun f ⟨v, hv⟩ ↦ hlocal f (hv ▸ innerCutoff_supported hrInner hInnerCell v)) w
  refine ⟨hM, hlocal, hglobal, ?_, inner_exterior_zero_on_core hrInner hInnerCell⟩
  intro w
  have he := (augmentedRow image (fun i ↦ restrictCarrier χ (Vactual i))
    (innerCutoff hrInner hInnerCell)).adjoint.apply_norm_sq_eq_inner_adjoint_left w
  apply (hglobal w).trans_eq
  simpa only [ContinuousLinearMap.adjoint_adjoint, RCLike.re_to_real, augmentedNormal] using he.symm

end JanetCartan.ContinuumNormal.ActualConstruction
