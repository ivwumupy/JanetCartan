module

public import JanetCartan.Iteration.PhysicalMean.ScalarRow
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.Realization.CompactKernel

/-!
# Literal scalar kernels of the original annular operators

Coordinate projection of the actual `BandKernelData.operator` has its literal
scalar kernel. The proof constructs a compact auxiliary kernel equal on the
original annular measure, then identifies the operators through their actual
Hilbert adjoints. The auxiliary cutoff disappears from the statement and does
not change any original input, phase, half derivative, or radial factor.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped InnerProductSpace

namespace JanetCartan.PhysicalSamplingShells
open SamplingKernelBounds RawInputRealization
open ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel

variable {n : ℕ} {P : Type*} [TopologicalSpace P]

/-- The literal scalar coordinate of the same full-phase band kernel,
including its original half derivative and radial mask. -/
def scalarBandKernel (hn : 1 ≤ n) (D : BandKernelData P n) (p : P)
    (x : Euclidean n) (η : Euclidean (n - 1)) : ℂ :=
  (D.kernel p η x).ofLp ⟨0, hn⟩

variable [FirstCountableTopology P] [LocallyCompactSpace P]

/-- Projecting the original annular operator gives the actual scalar integral
on its original measure; all input integrability is proved here, not assumed
(`new:eq:amplitude-test`). -/
theorem scalar_band_kernel_realization (hn : 1 ≤ n) (D : BandKernelData P n)
    (R : ℝ) (p : P) :
    (∀ (f : AnnularL2 n R) (x : Euclidean n),
      Integrable (fun η ↦ scalarBandKernel hn D p x η * f η) (annularMeasure n R)) ∧
    (∀ f : AnnularL2 n R,
      (PhysicalMean.scalarOutputProjection hn) (D.operator R p f) =ᵐ[volume]
        fun x ↦ ∫ η, scalarBandKernel hn D p x η * f η ∂annularMeasure n R) := by
  let χ : ContDiffBump (0 : Euclidean (n - 1)) :=
    ⟨|R| + 1, |R| + 2, by linarith [abs_nonneg R], by linarith⟩
  let t := fun x η ↦ (χ η : ℂ) * scalarBandKernel hn D p x η
  have hk : Continuous (Function.uncurry (scalarBandKernel hn D p)) := by
    exact (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) ⟨0, hn⟩).continuous.comp
      (D.continuous_kernel.comp (f := fun q : Euclidean n × Euclidean (n - 1) ↦
        ((p, q.2), q.1)) (by fun_prop))
  have ht : Continuous (Function.uncurry t) :=
    (Complex.continuous_ofReal.comp (χ.continuous.comp continuous_snd)).mul hk
  have hs : HasCompactSupport (Function.uncurry t) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (D.physicalSupport_compact.prod χ.hasCompactSupport)
    intro q hq
    constructor
    · by_contra hx
      apply hq
      change (χ q.2 : ℂ) * (D.kernel p q.2 q.1).ofLp ⟨0, hn⟩ = 0
      simp only [D.kernel_eq_zero p q.2 q.1 hx, PiLp.zero_apply, mul_zero]
    · apply subset_tsupport χ
      intro hz
      apply hq
      change (χ q.2 : ℂ) * scalarBandKernel hn D p q.1 q.2 = 0
      simp only [hz, Complex.ofReal_zero, zero_mul]
  have hone : ∀ η ∈ annulus n R, χ η = 1 := by
    intro η hη
    apply χ.one_of_mem_closedBall
    apply Metric.closedBall_subset_closedBall (show R ≤ χ.rIn by
      dsimp [χ]
      linarith [le_abs_self R]) hη.1
  have hae : ∀ᵐ η ∂annularMeasure n R, χ η = 1 :=
    (ae_restrict_mem (measurableSet_annulus n R)).mono (fun η hη ↦ hone η hη)
  let T := compactKernelOperator (μ := annularMeasure n R) (ν := volume) ht hs
  have hop : (PhysicalMean.scalarOutputProjection hn).comp (D.operator R p) = T := by
    apply ContinuousLinearMap.adjoint.injective
    apply ContinuousLinearMap.ext
    intro v
    apply Lp.ext
    filter_upwards [D.operator_hasAdjointKernel R p
      ((PhysicalMean.scalarOutputProjection hn).adjoint v),
      compactKernelOperator_adjoint_ae_integral (μ := annularMeasure n R) ht hs v,
      hae] with η hD hT hχ
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
    rw [hD, hT, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) ⟨0, hn⟩).coeFn_compLpL
      (D.column p η), D.column_coe p η] with x hp hx
    change inner ℂ ((PhysicalMean.scalarOutputProjection hn) (D.column p η) x) (v x) = _
    rw [PhysicalMean.scalarOutputProjection, hp, hx]
    simp only [t, hχ, Complex.ofReal_one, one_mul, scalarBandKernel,
      PiLp.proj_apply, RCLike.inner_apply, starRingEnd_apply, mul_comm]
  constructor
  · intro f x
    apply (integrable_compactKernel_mul_L2 ht hs f x).congr
    filter_upwards [hae] with η hη
    simp only [t, hη, Complex.ofReal_one, one_mul]
  · intro f
    have he := congrArg (fun S : AnnularL2 n R →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)) ↦ S f) hop
    rw [ContinuousLinearMap.comp_apply] at he
    rw [he]
    refine (compactKernelOperator_ae_integral ht hs f).trans ?_
    exact Filter.Eventually.of_forall fun x ↦ integral_congr_ae (hae.mono (fun η hη ↦ by
      simp only [t, hη, Complex.ofReal_one, one_mul]))

end JanetCartan.PhysicalSamplingShells
