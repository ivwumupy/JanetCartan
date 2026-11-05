module

public import JanetCartan.Iteration.PhysicalScalarChannel.Original
public import JanetCartan.Iteration.PhysicalSampling.OriginalKernel
public import JanetCartan.Iteration.PhysicalSamplingShells
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.GroupedKernels.Prefixes

/-!
# The bare scalar tester on the original native refined-shell measure

The complete physical row is transferred through the original wide/refined
Hilbert isometry and the literal disjoint-shell measure. A globally continuous
contractive coefficient is used only to reuse the existing kernel realization;
on the original high-pass support it exactly cancels the half derivative.
The FIO bound comes from `Original`, never from a Hilbert--Schmidt estimate.
Consumers: the individual moment of order `q - 1/2` discussed immediately
after `app:ch_mean_pairs:eq:raw-adjoint-moments`, and the fixed-carrier forward
estimate in `app:ch_mean_pairs:eq:block-fields`. The aggregate adjoint moment
bound instead uses `PhysicalSampling` and `PhysicalSamplingShells`, retaining
both the original half weight and every original square-root sample weight.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric MeasureTheory
open scoped BigOperators ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalScalarChannel

open SamplingKernelBounds Sampling Sampling.RawKernel Sampling.ColoredNormalComparison
open RawInputPartition RawInputRealization RawPrimary.MaskProfiles PhysicalSampling PhysicalMean
open PhysicalSamplingShells ActualCarriers FrozenMenu CurrentFullPhase
open Sampling.MeasuredAmplitude LeadingWave.FullModulation FullPhaseCharts ContinuumRow

/-- A globally continuous contraction which is exactly the inverse half weight
on the original high-pass support. It is not a replacement input mask. -/
def physicalInverseHalf {d : ℕ} (η : Euclidean d) : ℂ :=
  ((Real.sqrt (max 1 ‖η‖))⁻¹ : ℝ)

/-- The auxiliary coefficient remains continuous even at zero frequency. -/
theorem continuous_physicalInverseHalf (d : ℕ) : Continuous (physicalInverseHalf (d := d)) := by
  apply Complex.continuous_ofReal.comp
  exact (Real.continuous_sqrt.comp (continuous_const.max continuous_norm)).inv₀
    (fun η ↦ (Real.sqrt_pos.mpr (zero_lt_one.trans_le (le_max_left 1 ‖η‖))).ne')

/-- Removing the half weight does not enlarge any primitive kernel coefficient. -/
theorem norm_physicalInverseHalf_le_one {d : ℕ} (η : Euclidean d) :
    ‖physicalInverseHalf η‖ ≤ 1 := by
  rw [physicalInverseHalf, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (le_max_left _ _))

/-- Literal inverse-half cancellation on the unchanged original high-pass support. -/
theorem sqrt_mul_physicalInverseHalf {d : ℕ} {η : Euclidean d} (hη : 1 ≤ ‖η‖) :
    (Real.sqrt ‖η‖ : ℂ) * physicalInverseHalf η = 1 := by
  have hs : Real.sqrt ‖η‖ ≠ 0 := (Real.sqrt_pos.mpr (zero_lt_one.trans_le hη)).ne'
  simp only [physicalInverseHalf, max_eq_right hη, ← Complex.ofReal_mul,
    mul_inv_cancel₀ hs, Complex.ofReal_one]

/-- Auxiliary kernel realization with the SAME masks, phase and physical
support. Its actual FIO bound is established independently for the full bare
row in `exists_original_bare_scalar_wide_family`. -/
def bareBandData {P : Type*} [TopologicalSpace P] {n : ℕ} (D : BandKernelData P n) :
    BandKernelData P n :=
  { D with
    amplitude := fun q ↦ physicalInverseHalf q.1.2 • D.amplitude q
    amplitude_continuous :=
      ((continuous_physicalInverseHalf (n - 1)).comp (continuous_snd.comp continuous_fst)).smul
        D.amplitude_continuous
    amplitude_eq_zero := fun p η x hx ↦ by rw [D.amplitude_eq_zero p η x hx, smul_zero]
    amplitude_le := fun p η x ↦ by
      rw [norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_physicalInverseHalf_le_one η)).trans
        (D.amplitude_le p η x) }

/-- The auxiliary realization has exactly the bare kernel, including the zero
high-pass region, where no division or cancellation is needed. -/
theorem bareBandData_kernel {P : Type*} [TopologicalSpace P] {n : ℕ}
    (D : BandKernelData P n) (hzero : ∀ η, ‖η‖ ≤ 1 → D.mask η = 0)
    (p : P) (η : Euclidean (n - 1)) (x : Euclidean n) :
    (bareBandData D).kernel p η x =
      (Complex.exp ((D.phase ((p, η), x) : ℂ) * Complex.I) * D.mask η) • D.amplitude ((p, η), x) := by
  by_cases hη : ‖η‖ ≤ 1
  · simp only [BandKernelData.kernel, bandKernel, bareBandData, hzero η hη,
      mul_zero, zero_smul]
  · rw [BandKernelData.kernel, bandKernel, bareBandData, smul_smul]
    congr 1
    calc
      _ = (Complex.exp ((D.phase ((p, η), x) : ℂ) * Complex.I) * D.mask η) *
          ((Real.sqrt ‖η‖ : ℂ) * physicalInverseHalf η) := by ring
      _ = _ := by rw [sqrt_mul_physicalInverseHalf (le_of_not_ge hη), mul_one]

section SingleShell

variable {n J : ℕ} {Z : Type*} [TopologicalSpace Z] [FirstCountableTopology Z]
  [LocallyCompactSpace Z]

/-- A fixed original carrier retains each refined shell as a separate native
component. There is no sample label or square root of a sample weight. -/
def singleShellScalarKernel (hn : 1 ≤ n) (D : BandKernelData (Fin J × Z) n) (z : Z)
    (x : Euclidean n) (u : RefinedIndex J × Euclidean (n - 1)) : ℂ :=
  scalarBandKernel hn D (u.1.1, z) x u.2

/-- The same complete row, in the original disjoint-shell Hilbert coordinates. -/
def singleShellScalarOperator (hn : 1 ≤ n) (D : BandKernelData (Fin J × Z) n) (z : Z) :
    Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Euclidean n)) :=
  (scalarOutputProjection hn).comp ((refinedKernelPrefix D J z).comp
    (annularShellEquiv (V := ℂ) (n := n) (refinedRadius (J := J))).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The native transfer is isometric and scalar extraction is contractive. -/
theorem norm_singleShellScalarOperator_le (hn : 1 ≤ n)
    (D : BandKernelData (Fin J × Z) n) (z : Z) :
    ‖singleShellScalarOperator hn D z‖ ≤ ‖Sampling.MeanNormalBound.wideBandKernelRow D z‖ := by
  unfold singleShellScalarOperator
  apply (norm_scalarOutputProjection_comp_le hn _).trans
  rw [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv,
    Sampling.MeanNormalBound.wideBandKernelRow_eq_refined,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

/-- Every original scalar datum is integrable on the same disjoint shells. -/
theorem integrable_singleShellScalarKernel_mul (hn : 1 ≤ n)
    (D : BandKernelData (Fin J × Z) n) (z : Z)
    (f : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J)))) (x : Euclidean n) :
    Integrable (fun u ↦ singleShellScalarKernel hn D z x u * f u)
      (annularShellMeasure (n := n) (refinedRadius (J := J))) := by
  change Integrable (fun u ↦ singleShellScalarKernel hn D z x u * f u)
    (Measure.sum (fun i : RefinedIndex J ↦
      (annularMeasure n (refinedRadius i)).map (Prod.mk i)))
  rw [Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro i _
  apply (measurableEmbedding_prodMk_left i).integrable_map_iff.mpr
  have hi := (scalar_band_kernel_realization hn D (refinedRadius i) (i.1, z)).1
    (annularShellEquiv (n := n) (refinedRadius (J := J)) f i) x
  apply hi.congr
  filter_upwards [annularShellEquiv_ae (n := n) (refinedRadius (J := J)) f i] with η hη
  exact congrArg (fun w : ℂ ↦ scalarBandKernel hn D (i.1, z) x η * w) hη

/-- Literal finite-channel integrability for the physical Sobolev amplitude test. -/
theorem integrable_singleShellScalarKernel_smul {I : Type*} [Fintype I] (hn : 1 ≤ n)
    (D : BandKernelData (Fin J × Z) n) (z : Z)
    (f : Lp (EuclideanSpace ℂ I) 2
      (annularShellMeasure (n := n) (refinedRadius (J := J)))) (x : Euclidean n) :
    Integrable (fun u ↦ singleShellScalarKernel hn D z x u • f u)
      (annularShellMeasure (n := n) (refinedRadius (J := J))) := by
  apply Integrable.of_eval_piLp
  intro i
  let pr := PiLp.proj (𝕜 := ℂ) 2 (fun _ : I ↦ ℂ) i
  let g := pr.compLpL 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) f
  apply (integrable_singleShellScalarKernel_mul hn D z g x).congr
  filter_upwards [pr.coeFn_compLpL f] with u hu
  simpa only [g, pr, PiLp.proj_apply, PiLp.smul_apply, smul_eq_mul] using
    congrArg (fun w : ℂ ↦ singleShellScalarKernel hn D z x u * w) hu

/-- The constructed native operator has precisely its original scalar kernel
for every L² datum; neither integrability nor kernel matching is assumed. -/
theorem singleShellScalarOperator_ae_integral (hn : 1 ≤ n)
    (D : BandKernelData (Fin J × Z) n) (z : Z)
    (f : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J)))) :
    singleShellScalarOperator hn D z f =ᵐ[volume] fun x ↦
      ∫ u, singleShellScalarKernel hn D z x u * f u
        ∂annularShellMeasure (n := n) (refinedRadius (J := J)) := by
  have hrow := scalar_refinedKernelPrefix_ae hn D J z
    (annularShellEquiv (V := ℂ) (n := n) (refinedRadius (J := J)) f)
  simp only [Fin.is_lt, Finset.filter_true] at hrow
  refine hrow.trans (Filter.Eventually.of_forall fun x ↦ ?_)
  symm
  change (∫ u, singleShellScalarKernel hn D z x u * f u
    ∂Measure.sum (fun i : RefinedIndex J ↦
      (annularMeasure n (refinedRadius i)).map (Prod.mk i))) = _
  rw [integral_sum_measure (integrable_singleShellScalarKernel_mul hn D z f x), tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [(measurableEmbedding_prodMk_left i).integral_map]
  apply integral_congr_ae
  filter_upwards [annularShellEquiv_ae (n := n) (refinedRadius (J := J)) f i] with η hη
  exact congrArg (fun w : ℂ ↦ scalarBandKernel hn D (i.1, z) x η * w) hη.symm

end SingleShell

section Original

variable {m J : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (χ : ContDiffBump (0 : Euclidean (m + 1)))
  (center : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  {ρ : ℝ} (hρ : 0 < ρ) {c C : ℝ} (hP : P.IsValid c C)
  (hcarrier : closedBall center.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  {ηoriginal : Euclidean (m + 1 - 1)} {roriginal : ℝ}
  (hηoriginal : ηoriginal ≠ 0) (hroriginal : 0 < roriginal)
  {τ : ℝ} (hτ : τ ≠ 0)

/-- Actual original bare kernel data. The dummy one-element color type only
fits the existing label API; no sample, sampling weight or color sum is taken. -/
def originalBareBandData : BandKernelData
    (Fin J × ((Fin 3 → Fin 1) × SeparatedSampling.Point)) (m + 1) :=
  bareBandData (originalScalarKernelData T Q χ center hρ hP hcarrier hηoriginal hroriginal
    (fun _ ↦ τ) (fun _ ↦ hτ))

/-- The auxiliary realization has the literal original bare physical kernel,
not a weighted surrogate or a changed dyadic partition. -/
theorem originalBareBandData_kernel (j : Fin J) (z : Euclidean 3)
    (x : Euclidean (m + 1)) (η : Euclidean (m + 1 - 1)) :
    (originalBareBandData T Q χ center hρ hP hcarrier hηoriginal hroriginal hτ).kernel
      (j, (fun _ ↦ 0, z.ofLp)) η x =
      retainedBareScalarVectorKernel T Q χ (originalConicDetector hηoriginal hroriginal)
        (fun η ↦ FixedCutoffs.highFrequency ‖η‖) center.2.1 z hρ τ j.val x η := by
  rw [originalBareBandData, bareBandData_kernel _ (fun η hη ↦ by
    change detectorMask (originalConicDetector hηoriginal hroriginal)
      (fun η ↦ FixedCutoffs.highFrequency ‖η‖) η = 0
    simp only [detectorMask, FixedCutoffs.highFrequency_zero hη, Complex.ofReal_zero, mul_zero])]
  simp only [originalScalarKernelData, retainedScalarKernelData, scalarAuxiliaryKernel,
    bandKernelData, measuredBandAmplitude, retainedBareScalarVectorKernel,
    WithLp.toLp_ofLp, scalarAuxiliaryAmplitude, ← Complex.coe_smul, smul_smul,
    weightedRadialBand, Complex.ofReal_mul]
  congr 1
  rw [mul_comm _ Complex.I]
  ring

/-- The literal unweighted, undifferentiated physical scalar kernel on the
original refined-shell measure. The finite-parameter phase is not linearized. -/
def originalBareNativeKernel (σ : ℝ) (z : Euclidean 3) (x : Euclidean (m + 1))
    (u : RefinedIndex J × Euclidean (m + 1 - 1)) : ℂ :=
  ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) : ℝ) *
    Complex.exp (Complex.I * (rawPrimaryPhaseDifference (extendedRetainedPhase T Q)
      (extendedRetainedCarrier T center.2.1 hρ z) σ x u.2 : ℂ)) *
    weightedRadialBand (detectorMask (originalConicDetector hηoriginal hroriginal)
      (fun η ↦ FixedCutoffs.highFrequency ‖η‖)) u.1.1.val u.2 * (χ x : ℂ)

/-- Scalar coordinate extraction preserves the exact bare kernel, including
all original constants and both refined copies of every radial band. -/
theorem originalBareBandData_scalar_kernel (z : Euclidean 3) (x : Euclidean (m + 1))
    (u : RefinedIndex J × Euclidean (m + 1 - 1)) :
    singleShellScalarKernel (Nat.succ_le_succ (Nat.zero_le m))
      (originalBareBandData T Q χ center hρ hP hcarrier hηoriginal hroriginal hτ)
      (fun _ ↦ 0, z.ofLp) x u =
      originalBareNativeKernel T Q χ center hρ hηoriginal hroriginal τ z x u := by
  rw [singleShellScalarKernel, scalarBandKernel, originalBareBandData_kernel]
  simp only [retainedBareScalarVectorKernel, PiLp.smul_apply,
    scalarAuxiliaryAmplitude_component, originalBareNativeKernel, ← Complex.coe_smul,
    smul_eq_mul]
  ring

/-- The full original bare physical row is exactly the preexisting kernel
synthesis row. This is a forward-map identity, not an additional norm premise. -/
theorem originalBareWideRow_eq
    (z : Euclidean 3)
    (L : WideInput (m + 1) J →L[ℂ] SamplingKernelBounds.Output (m + 1))
    (hL : ∀ f, L f =ᵐ[volume] fun x ↦ ∑ j : Fin J,
      ∫ η in wideBand (m + 1) j.val, f j η •
        retainedBareScalarVectorKernel T Q χ (originalConicDetector hηoriginal hroriginal)
          (fun η ↦ FixedCutoffs.highFrequency ‖η‖) center.2.1 z hρ τ j.val x η) :
    Sampling.MeanNormalBound.wideBandKernelRow
      (originalBareBandData T Q χ center hρ hP hcarrier hηoriginal hroriginal hτ)
        (fun _ ↦ 0, z.ofLp) = L := by
  let D := originalBareBandData (J := J) T Q χ center hρ hP hcarrier hηoriginal hroriginal hτ
  have hband (j : Fin J) (f : WideBandL2 (m + 1) j.val) :
      Sampling.MeanNormalBound.wideBandKernelOperator D j.val (j, (fun _ ↦ 0, z.ofLp)) f =ᵐ[volume]
        fun x ↦ ∫ η in wideBand (m + 1) j.val, f η •
          retainedBareScalarVectorKernel T Q χ (originalConicDetector hηoriginal hroriginal)
            (fun η ↦ FixedCutoffs.highFrequency ‖η‖) center.2.1 z hρ τ j.val x η := by
    have hs : ∀ η ∉ wideBand (m + 1) j.val, ∀ x,
        D.kernel (j, (fun _ ↦ 0, z.ofLp)) η x = 0 := by
      intro η hη x
      rw [originalBareBandData_kernel]
      simp only [retainedBareScalarVectorKernel, weightedRadialBand_eq_zero_off_wideBand _ hη,
        mul_zero, zero_smul, smul_zero]
    simpa only [D, originalBareBandData_kernel] using wideBandKernelOperator_ae_integral D j.val
      (j, (fun _ ↦ 0, z.ofLp)) hs f
  ext1 f
  apply Lp.ext
  have hwide : Sampling.MeanNormalBound.wideBandKernelRow D (fun _ ↦ 0, z.ofLp) f =ᵐ[volume]
      fun x ↦ ∑ j : Fin J, ∫ η in wideBand (m + 1) j.val, f j η •
        retainedBareScalarVectorKernel T Q χ (originalConicDetector hηoriginal hroriginal)
          (fun η ↦ FixedCutoffs.highFrequency ‖η‖) center.2.1 z hρ τ j.val x η := by
    simp only [Sampling.MeanNormalBound.wideBandKernelRow, NormalPerturbation.weightedRow_apply,
      Real.sqrt_one, RCLike.ofReal_one, one_smul]
    refine (Lp.coeFn_finsetSum _ _).trans ?_
    have hh := eventuallyEq_sum (s := Finset.univ) (fun j _ ↦ hband j (f j))
    filter_upwards [hh] with x hx
    simpa only [Finset.sum_apply] using hx
  exact hwide.trans (hL f).symm

include hP hcarrier hτ in
/-- The exact native bare scalar tester follows from the constructed full
physical row. The final factory below supplies that row from primitive original
current-map bounds, before all inverse frequencies and band counts. -/
theorem exists_originalBareNativeOperator
    (z : Euclidean 3) {Cbare : ℝ}
    (L : WideInput (m + 1) J →L[ℂ] SamplingKernelBounds.Output (m + 1))
    (hL : ∀ f, L f =ᵐ[volume] fun x ↦ ∑ j : Fin J,
      ∫ η in wideBand (m + 1) j.val, f j η •
        retainedBareScalarVectorKernel T Q χ (originalConicDetector hηoriginal hroriginal)
          (fun η ↦ FixedCutoffs.highFrequency ‖η‖) center.2.1 z hρ τ j.val x η)
    (hLn : ‖L‖ ^ 2 ≤ Cbare) :
    ∃ T₀ : Lp ℂ 2 (annularShellMeasure (n := m + 1) (refinedRadius (J := J))) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Euclidean (m + 1))),
      ‖T₀‖ ^ 2 ≤ Cbare ∧
      (∀ f, T₀ f =ᵐ[volume] fun x ↦
        ∫ u, originalBareNativeKernel T Q χ center hρ hηoriginal hroriginal τ z x u * f u
          ∂annularShellMeasure (n := m + 1) (refinedRadius (J := J))) ∧
      (∀ {I : Type*} [Fintype I]
        (f : Lp (EuclideanSpace ℂ I) 2
          (annularShellMeasure (n := m + 1) (refinedRadius (J := J)))) x,
        Integrable (fun u ↦ originalBareNativeKernel T Q χ center hρ hηoriginal hroriginal τ z x u • f u)
          (annularShellMeasure (n := m + 1) (refinedRadius (J := J)))) := by
  let D := originalBareBandData (J := J) T Q χ center hρ hP hcarrier hηoriginal hroriginal hτ
  refine ⟨singleShellScalarOperator (Nat.succ_le_succ (Nat.zero_le m)) D (fun _ ↦ 0, z.ofLp), ?_, ?_, ?_⟩
  · apply (pow_le_pow_left₀ (norm_nonneg _)
      (norm_singleShellScalarOperator_le (Nat.succ_le_succ (Nat.zero_le m)) D (fun _ ↦ 0, z.ofLp)) 2).trans
    rwa [originalBareWideRow_eq T Q χ center hρ hP hcarrier hηoriginal hroriginal hτ z L hL]
  · intro f
    simpa only [D, originalBareBandData_scalar_kernel] using
      singleShellScalarOperator_ae_integral (Nat.succ_le_succ (Nat.zero_le m)) D (fun _ ↦ 0, z.ofLp) f
  · intro I _ f x
    simpa only [D, originalBareBandData_scalar_kernel] using
      integrable_singleShellScalarKernel_smul (Nat.succ_le_succ (Nat.zero_le m)) D (fun _ ↦ 0, z.ofLp) f x

end Original

open ProjectedStressFrame

/-- The original bare native scalar tester from primitive current-immersion
bounds, with its constant fixed before every frequency, carrier and shell count.
Its kernel retains the original scalar cutoff, full finite-parameter phase,
detector, high-pass and two sharp copies of every radial band. No sample weight,
half derivative, shell-count factor or assumed operator norm occurs. -/
theorem exists_original_bare_scalar_native_family
    {m : ℕ} (hn : 2 ≤ m + 1) {P : Patch (m + 1)}
    {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {amax bmax emax : ℝ} (hamax : 0 < amax) (hbmax : 0 < bmax) (hemax : 0 < emax) :
    ∃ a > (0 : ℝ), 4 * a ≤ amax ∧
    ∃ e > (0 : ℝ), e ≤ emax ∧
    ∃ δ > (0 : ℝ), δ ≤ T.family.threshold ∧
    ∀ (χ : ContDiffBump (0 : Euclidean (m + 1))),
      tsupport (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall 0 (a / 4) →
    ∀ {ηoriginal : Euclidean (m + 1 - 1)} {roriginal : ℝ}
      (hηoriginal : ηoriginal ≠ 0) (hroriginal : 0 < roriginal),
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
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
    ∀ (center : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
      {ρ : ℝ} (hρ : 0 < ρ),
      closedBall center.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius) →
      closedBall center (2 * ρ) ⊆ domain T →
      Function.support (χ : Euclidean (m + 1) → ℝ) ⊆ closedBall center.1 (ρ / 2) →
    ∀ z ∈ parameterCube P.radius,
      (z, T.reference.spatialPatch z) ∈ closedBall center.2 (ρ / 4) →
    ∀ (J : ℕ) {τ : ℝ}, τ ≠ 0 →
      (∀ j : Fin J, τ * (2 : ℝ) ^ j.val ∈ Icc 0 e) →
      (∀ j : Fin J, |τ * (2 : ℝ) ^ j.val| ≤ ρ / 8) →
    ∃ T₀ : Lp ℂ 2 (annularShellMeasure (n := m + 1) (refinedRadius (J := J))) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Euclidean (m + 1))),
      ‖T₀‖ ^ 2 ≤ Cbare ∧
      (∀ f, T₀ f =ᵐ[volume] fun x ↦
        ∫ u, originalBareNativeKernel T Q χ center hρ hηoriginal hroriginal τ z x u * f u
          ∂annularShellMeasure (n := m + 1) (refinedRadius (J := J))) ∧
      (∀ {I : Type*} [Fintype I]
        (f : Lp (EuclideanSpace ℂ I) 2
          (annularShellMeasure (n := m + 1) (refinedRadius (J := J)))) x,
        Integrable (fun u ↦ originalBareNativeKernel T Q χ center hρ hηoriginal hroriginal τ z x u • f u)
          (annularShellMeasure (n := m + 1) (refinedRadius (J := J)))) := by
  obtain ⟨a, ha, hacap, e, he, hecap, δ, hδ, hδcap, hbuild⟩ :=
    exists_original_bare_scalar_wide_family T hn hP hamax hbmax hemax
  refine ⟨a, ha, hacap, e, he, hecap, δ, hδ, hδcap, ?_⟩
  intro χ hχ ηoriginal roriginal hηoriginal hroriginal K hK hKU hball M γ κ hγ hκ
  obtain ⟨Cbare, hCbare, hcurrent⟩ := hbuild χ hχ
    (originalConicDetector hηoriginal hroriginal) (fun η ↦ FixedCutoffs.highFrequency ‖η‖)
    (fun _ hη ↦ originalConicDetector_contDiffAt hηoriginal hroriginal hη)
    (originalConicDetector_homogeneous hηoriginal hroriginal)
    (contDiff_originalConicHighPass (m + 1))
    (fun _ hη ↦ FixedCutoffs.highFrequency_one hη) hK hKU hball M hγ hκ
  refine ⟨Cbare, hCbare, ?_⟩
  intro F hF hi hrank hFM hmetric hnormal hsmall
  obtain ⟨hlow, hwide⟩ := hcurrent F hF hi hrank hFM hmetric hnormal hsmall
  refine ⟨hlow, ?_⟩
  intro Q center ρ hρ hcarrier hphase hχρ z hz hzg J τ hτ hε hscale
  obtain ⟨L, hL, hLn⟩ := hwide center hρ hphase hχρ z hz hzg J hτ hε hscale
  exact exists_originalBareNativeOperator T Q χ center hρ hP hcarrier hηoriginal hroriginal hτ z L hL hLn

end JanetCartan.PhysicalScalarChannel
