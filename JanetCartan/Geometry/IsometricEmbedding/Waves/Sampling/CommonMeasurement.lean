module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.AngularPartition
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.CommonBounds
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.Freezing.VectorMultipliers

/-!
# One physical measurement for the selected angular charts

Choose a common nonzero bump on the plateaus of the finitely many retained
physical bumps. Literal output multiplication transfers their annular and
unchanged grouped-prefix operators. This permits angular reassembly with a
single physical measurement, without identifying independently chosen bumps.
The consumer is the retained finite-family sampling assembly
(`app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.Sampling
open SamplingKernelBounds RawInputRealization RawInputPartition ContinuumNormal

/-- A common physical cutoff is chosen after the finite cone cover and before
fields or frequencies. Every original local bump equals one on its support;
all local phase and amplitude witnesses remain unchanged
(`app:ch_waves:thm:sampling`). -/
theorem exists_common_sampling_measurement {A : Type*} [Fintype A] {n : ℕ}
    (χ : A → ContDiffBump (0 : Euclidean n)) :
    ∃ θ : ContDiffBump (0 : Euclidean n),
      ∀ a x, θ x ≠ 0 → χ a x = 1 := by
  have hnb : (⋂ a, ball (0 : Euclidean n) (χ a).rIn) ∈ nhds 0 :=
    Filter.iInter_mem.mpr fun a ↦ ball_mem_nhds _ (χ a).rIn_pos
  obtain ⟨b, hb, hsub⟩ := Metric.mem_nhds_iff.mp hnb
  let θ : ContDiffBump (0 : Euclidean n) := ⟨b / 2, b, by positivity, by linarith⟩
  refine ⟨θ, ?_⟩
  intro a x hx
  have hx' : x ∈ Function.support θ := hx
  rw [θ.support_eq] at hx'
  exact (χ a).one_of_mem_closedBall (ball_subset_closedBall (mem_iInter.mp (hsub hx') a))

variable {P : Type*} [TopologicalSpace P] {n : ℕ}

/-- Apply the common measurement to the literal kernel, preserving the full
output space, original input mask and Fourier normalization
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def physicallyLocalizedKernel (D : BandKernelData P n) (θ : ContDiffBump (0 : Euclidean n)) :
    BandKernelData P n where
  phase := D.phase
  phase_continuous := D.phase_continuous
  mask := D.mask
  mask_continuous := D.mask_continuous
  amplitude := fun q ↦ (θ q.2 : ℂ) • D.amplitude q
  amplitude_continuous := (Complex.continuous_ofReal.comp (θ.continuous.comp continuous_snd)).smul
    D.amplitude_continuous
  physicalSupport := D.physicalSupport
  physicalSupport_compact := D.physicalSupport_compact
  amplitude_eq_zero := by
    intro p η x hx
    simp only [D.amplitude_eq_zero p η x hx, smul_zero]
  amplitudeBound := D.amplitudeBound
  amplitudeBound_nonneg := D.amplitudeBound_nonneg
  amplitude_le := by
    intro p η x
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg θ.nonneg]
    exact (mul_le_mul_of_nonneg_right θ.le_one (norm_nonneg _)).trans
      (by simpa only [one_mul] using D.amplitude_le p η x)
  maskBound := D.maskBound
  maskBound_nonneg := D.maskBound_nonneg
  mask_le := D.mask_le

/-- The common measurement is literal scalar multiplication of the original
kernel (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem physicallyLocalizedKernel_kernel (D : BandKernelData P n)
    (θ : ContDiffBump (0 : Euclidean n)) (p : P) (η : Euclidean (n - 1)) (x : Euclidean n) :
    (physicallyLocalizedKernel D θ).kernel p η x = (θ x : ℂ) • D.kernel p η x := by
  simp only [BandKernelData.kernel, bandKernel, physicallyLocalizedKernel]
  simp only [smul_smul, mul_comm]

/-- The kernel constant is unchanged by the contractive common measurement
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem physicallyLocalizedKernel_squaredKernelConstant (D : BandKernelData P n)
    (θ : ContDiffBump (0 : Euclidean n)) :
    (physicallyLocalizedKernel D θ).squaredKernelConstant = D.squaredKernelConstant := rfl

/-- Literal column equality on the original Euclidean Lebesgue output
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem physicallyLocalizedKernel_column (D : BandKernelData P n)
    (θ : ContDiffBump (0 : Euclidean n)) (p : P) (η : Euclidean (n - 1)) :
    (physicallyLocalizedKernel D θ).column p η =
      freezingVectorPhysicalMultiplier θ θ.continuous θ.hasCompactSupport (D.column p η) := by
  apply Lp.ext
  filter_upwards [(physicallyLocalizedKernel D θ).column_coe p η, D.column_coe p η,
    freezingVectorPhysicalMultiplier_coeFn θ θ.continuous θ.hasCompactSupport (D.column p η)]
    with x hx hy hz
  rw [hx, hz, hy, physicallyLocalizedKernel_kernel]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) (θ x) (D.kernel p η x) |>.symm

/-- The common bump acts contractively on the entire output, with no change
of output space or physical measure (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_common_sampling_multiplier_le (θ : ContDiffBump (0 : Euclidean n)) :
    ‖freezingVectorPhysicalMultiplier (I := Fin n) θ θ.continuous θ.hasCompactSupport‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [freezingVectorPhysicalMultiplier_coeFn θ θ.continuous θ.hasCompactSupport f]
    with x hx
  rw [hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg θ.nonneg]
  exact mul_le_mul_of_nonneg_right θ.le_one (norm_nonneg _)

variable [FirstCountableTopology P] [LocallyCompactSpace P]

/-- The physical restriction acts on the SAME annular Lebesgue channel by
postcomposition; it does not construct a second raw family
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem physicallyLocalizedKernel_operator (D : BandKernelData P n)
    (θ : ContDiffBump (0 : Euclidean n)) (R : ℝ) (p : P) :
    (physicallyLocalizedKernel D θ).operator R p =
      (freezingVectorPhysicalMultiplier θ θ.continuous θ.hasCompactSupport).comp (D.operator R p) := by
  ext1 f
  simp only [BandKernelData.operator_apply, physicallyLocalizedKernel_column,
    ContinuousLinearMap.comp_apply]
  rw [← (freezingVectorPhysicalMultiplier θ θ.continuous θ.hasCompactSupport).integral_comp_comm]
  · simp only [map_smul]
  · exact memLp_one_iff_integrable.mp ((Lp.memLp f).smul (D.memLp_column R p))

/-- Every unchanged grouped prefix has the same physical postcomposition.
Both sharp components of each smooth band are retained
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem physicallyLocalizedKernel_prefix {J : ℕ} (D : BandKernelData (Fin J × P) n)
    (θ : ContDiffBump (0 : Euclidean n)) (L : ℕ) (p : P) :
    refinedKernelPrefix (physicallyLocalizedKernel D θ) L p =
      (freezingVectorPhysicalMultiplier θ θ.continuous θ.hasCompactSupport).comp
        (refinedKernelPrefix D L p) := by
  ext1 f
  simp only [refinedKernelPrefix, prefixRow_apply, physicallyLocalizedKernel_operator,
    ContinuousLinearMap.comp_apply, map_sum]

/-- The sharp single-band estimate transfers without a loss after choosing
one common physical measurement (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_physicallyLocalizedKernel_operator_le (D : BandKernelData P n)
    (θ : ContDiffBump (0 : Euclidean n)) (R : ℝ) (p : P) :
    ‖(physicallyLocalizedKernel D θ).operator R p‖ ≤ ‖D.operator R p‖ := by
  rw [physicallyLocalizedKernel_operator]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right (norm_common_sampling_multiplier_le θ) (norm_nonneg _)).trans_eq
      (one_mul _))

/-- The complete output normal has the exact common physical conjugation,
including both annular pieces of every prefix
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem physicallyLocalizedKernel_prefix_normal {J : ℕ} (D : BandKernelData (Fin J × P) n)
    (θ : ContDiffBump (0 : Euclidean n)) (L : ℕ) (p : P) :
    atomNormal (refinedKernelPrefix (physicallyLocalizedKernel D θ) L p) =
      let M := freezingVectorPhysicalMultiplier θ θ.continuous θ.hasCompactSupport
      M.comp ((atomNormal (refinedKernelPrefix D L p)).comp M.adjoint) := by
  rw [physicallyLocalizedKernel_prefix]
  simp only [atomNormal, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

end JanetCartan.Sampling
