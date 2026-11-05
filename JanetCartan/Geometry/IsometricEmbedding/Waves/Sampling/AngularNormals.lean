module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RefinedKernels

/-!
# Angular square partitions preserve the original sampling normals

Multiply only the original input detector by a bounded real angular cutoff.
The fixed high-pass floor makes the resulting mask continuous at zero, even
though a homogeneous angular cutoff need not be continuous there. The literal
annular synthesis and adjoint formulas prove exact normal reassembly on the
full Euclidean output, including every unchanged grouped prefix.

Consumer: the finite covering-family application of
`MeasuredAmplitude.exists_finite_retained_sampling_realization`. Construction
of the subordinate angular square partition is a separate obligation.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped InnerProductSpace
namespace JanetCartan.Sampling
open SamplingKernelBounds RawInputRealization RawInputPartition

variable {P A : Type*} [TopologicalSpace P] {n : ℕ}

/-- Localize the original detector while preserving its phase, measured
amplitude, support and original Lebesgue normalization. The high-pass floor
supplies continuity at zero (`app:ch_waves:thm:sampling`). -/
def angularLocalizedKernel (D : BandKernelData P n)
    (hfloor : ∀ η, ‖η‖ ≤ 1 → D.mask η = 0)
    (χ : Euclidean (n - 1) → ℝ) (hχ : ContinuousOn χ ({0}ᶜ : Set (Euclidean (n - 1))))
    (hbound : ∀ η, |χ η| ≤ 1) : BandKernelData P n where
  phase := D.phase
  phase_continuous := D.phase_continuous
  mask := fun η ↦ (χ η : ℂ) * D.mask η
  mask_continuous := by
    apply continuous_iff_continuousAt.mpr
    intro η
    by_cases hη : η = 0
    · subst η
      have he : (fun η ↦ (χ η : ℂ) * D.mask η) =ᶠ[nhds 0] (fun _ ↦ (0 : ℂ)) := by
        filter_upwards [ball_mem_nhds (0 : Euclidean (n - 1)) zero_lt_one] with η hη
        simp [hfloor η (mem_ball_zero_iff.mp hη).le]
      exact continuousAt_const.congr he.symm
    · exact (Complex.continuous_ofReal.continuousAt.comp
        (hχ.continuousAt (isOpen_compl_singleton.mem_nhds hη))).mul D.mask_continuous.continuousAt
  amplitude := D.amplitude
  amplitude_continuous := D.amplitude_continuous
  physicalSupport := D.physicalSupport
  physicalSupport_compact := D.physicalSupport_compact
  amplitude_eq_zero := D.amplitude_eq_zero
  amplitudeBound := D.amplitudeBound
  amplitudeBound_nonneg := D.amplitudeBound_nonneg
  amplitude_le := D.amplitude_le
  maskBound := D.maskBound
  maskBound_nonneg := D.maskBound_nonneg
  mask_le := by
    intro η
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hbound η) (norm_nonneg _)).trans
      (by simpa only [one_mul] using D.mask_le η)

/-- Angular refinement changes the actual kernel by precisely its real input
factor, with no coordinate or measure change
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem angularLocalizedKernel_kernel (D : BandKernelData P n) hfloor χ hχ hbound
    (p : P) (η : Euclidean (n - 1)) (x : Euclidean n) :
    (angularLocalizedKernel D hfloor χ hχ hbound).kernel p η x =
      (χ η : ℂ) • D.kernel p η x := by
  simp only [BandKernelData.kernel, bandKernel, angularLocalizedKernel]
  simp [smul_smul, mul_assoc, mul_comm]

/-- Equality of the actual Lebesgue L² columns under angular localization
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem angularLocalizedKernel_column (D : BandKernelData P n) hfloor χ hχ hbound
    (p : P) (η : Euclidean (n - 1)) :
    (angularLocalizedKernel D hfloor χ hχ hbound).column p η = (χ η : ℂ) • D.column p η := by
  apply Lp.ext
  filter_upwards [(angularLocalizedKernel D hfloor χ hχ hbound).column_coe p η,
    D.column_coe p η, Lp.coeFn_smul (χ η : ℂ) (D.column p η)] with x hx hy hz
  rw [hx, hz]
  change _ = (χ η : ℂ) • (D.column p η) x
  rw [hy, angularLocalizedKernel_kernel]

/-- Angular localization retains the SAME squared-kernel constant used by
the finite-family concentration threshold
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem angularLocalizedKernel_squaredKernelConstant (D : BandKernelData P n)
    hfloor χ hχ hbound :
    (angularLocalizedKernel D hfloor χ hχ hbound).squaredKernelConstant =
      D.squaredKernelConstant := rfl

variable [FirstCountableTopology P] [LocallyCompactSpace P]

private theorem bandNormal_apply (D : BandKernelData P n) (R : ℝ) (p : P) (v : Output n) :
    atomNormal (D.operator R p) v =
      ∫ η, inner ℂ (D.column p η) v • D.column p η ∂annularMeasure n R := by
  change D.operator R p ((D.operator R p).adjoint v) = _
  rw [D.operator_apply]
  apply integral_congr_ae
  filter_upwards [D.operator_hasAdjointKernel R p v] with η hη
  rw [hη]

/-- A square partition on the original nonzero detector exactly reassembles
the original annular normal. Integrability and the adjoint are consequences
of the constructed kernels, rather than hypotheses about normal operators
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_angularLocalizedKernel_normal [Fintype A]
    (D : BandKernelData P n) (hfloor : ∀ η, ‖η‖ ≤ 1 → D.mask η = 0)
    (χ : A → Euclidean (n - 1) → ℝ)
    (hχ : ∀ a, ContinuousOn (χ a) ({0}ᶜ : Set (Euclidean (n - 1))))
    (hbound : ∀ a η, |χ a η| ≤ 1)
    (hpartition : ∀ η, D.mask η ≠ 0 → ∑ a, χ a η ^ 2 = 1)
    (R : ℝ) (p : P) :
    ∑ a, atomNormal ((angularLocalizedKernel D hfloor (χ a) (hχ a) (hbound a)).operator R p) =
      atomNormal (D.operator R p) := by
  classical
  let D' := fun a ↦ angularLocalizedKernel D hfloor (χ a) (hχ a) (hbound a)
  apply ContinuousLinearMap.ext
  intro v
  simp only [sum_apply, bandNormal_apply]
  have hint (a : A) : Integrable
      (fun η ↦ inner ℂ ((D' a).column p η) v • (D' a).column p η) (annularMeasure n R) :=
    memLp_one_iff_integrable.mp
      (((D' a).memLp_column R p).inner_const (𝕜 := ℂ) v |>.smul ((D' a).memLp_column R p))
  rw [← integral_finsetSum Finset.univ (fun a _ ↦ hint a)]
  apply integral_congr_ae
  filter_upwards with η
  dsimp only [D']
  by_cases hm : D.mask η = 0
  · have hc : D.column p η = 0 := by
      apply Lp.ext
      filter_upwards [D.column_coe p η] with x hx
      simp [hx, BandKernelData.kernel, bandKernel, hm]
    simp only [angularLocalizedKernel_column, hc, smul_zero, inner_zero_left,
      Finset.sum_const_zero]
  · have hs : ∑ a, (χ a η : ℂ) ^ 2 = 1 := by exact_mod_cast hpartition η hm
    have he (a : A) :
        inner ℂ ((χ a η : ℂ) • D.column p η) v • ((χ a η : ℂ) • D.column p η) =
          (χ a η : ℂ) ^ 2 • (inner ℂ (D.column p η) v • D.column p η) := by
      rw [inner_smul_left, smul_smul, smul_smul]
      congr 1
      simp only [Complex.conj_ofReal]
      ring
    simp_rw [angularLocalizedKernel_column, he]
    rw [← Finset.sum_smul, hs, one_smul]

/-- Angular refinement preserves every original grouped prefix normal on
the SAME two-shell input convention. The smooth band is unchanged and no
sharp indicator enters the angular calculus
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_angularLocalizedKernel_prefix_normal [Fintype A] {J : ℕ}
    (D : BandKernelData (Fin J × P) n) (hfloor : ∀ η, ‖η‖ ≤ 1 → D.mask η = 0)
    (χ : A → Euclidean (n - 1) → ℝ)
    (hχ : ∀ a, ContinuousOn (χ a) ({0}ᶜ : Set (Euclidean (n - 1))))
    (hbound : ∀ a η, |χ a η| ≤ 1)
    (hpartition : ∀ η, D.mask η ≠ 0 → ∑ a, χ a η ^ 2 = 1)
    (L : ℕ) (p : P) :
    ∑ a, atomNormal (refinedKernelPrefix
      (angularLocalizedKernel D hfloor (χ a) (hχ a) (hbound a)) L p) =
      atomNormal (refinedKernelPrefix D L p) := by
  classical
  simp_rw [refinedKernelPrefix_normal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact sum_angularLocalizedKernel_normal D hfloor χ hχ hbound hpartition
    (refinedRadius i) (i.1, p)

/-- The same reassembly keeps both physical input quadratures and the exact
factor four on the entire real output (`app:ch_waves:eq:real-normal`). -/
theorem sum_angularLocalizedKernel_realPrefix_normal [Fintype A] {J : ℕ}
    (D : BandKernelData (Fin J × P) n) (hfloor : ∀ η, ‖η‖ ≤ 1 → D.mask η = 0)
    (χ : A → Euclidean (n - 1) → ℝ)
    (hχ : ∀ a, ContinuousOn (χ a) ({0}ᶜ : Set (Euclidean (n - 1))))
    (hbound : ∀ a η, |χ a η| ≤ 1)
    (hpartition : ∀ η, D.mask η ≠ 0 → ∑ a, χ a η ^ 2 = 1)
    (L : ℕ) (p : P) :
    (∑ a, (realQuadratureChannel (refinedKernelPrefix
      (angularLocalizedKernel D hfloor (χ a) (hχ a) (hbound a)) L p)) ∘L
        (realQuadratureChannel (refinedKernelPrefix
          (angularLocalizedKernel D hfloor (χ a) (hχ a) (hbound a)) L p)).adjoint) =
      (4 : ℝ) • realOutputCompression (atomNormal (refinedKernelPrefix D L p)) := by
  classical
  simp_rw [realQuadratureChannel_normal_eq_four_realPart]
  rw [← sum_angularLocalizedKernel_prefix_normal D hfloor χ hχ hbound hpartition L p]
  ext1 v
  simp [realOutputCompression, atomNormal, Finset.smul_sum]

end JanetCartan.Sampling
