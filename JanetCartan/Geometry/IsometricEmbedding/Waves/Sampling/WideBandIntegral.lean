module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.Reassembly
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.EuclideanDisintegration.KernelColumns

/-!
# Physical integral of the reassembled sampling band

The consumer is the sharp band estimate in `app:ch_waves:eq:sampling-operator-bounds`.
Identify the existing column synthesis with its physical integral, then transfer
the norm of that SAME wide band to either sharp Hilbert component. No sharp
indicator is differentiated and the full Lebesgue output is unchanged.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set
open scoped InnerProductSpace

namespace JanetCartan.Sampling
open SamplingKernelBounds RawInputPartition MeanNormalBound NormalComparison
open ColoredNormalComparison ColoredNormalComparison.EuclideanDisintegration Pseudodifferential

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {n : ℕ}

/-- The wide-band column synthesis has the literal vector-valued physical
integral. Its sole support input concerns the primitive kernel, and is proved
for the actual smooth radial amplitude in `RawKernel`
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem wideBandKernelOperator_ae_integral (D : BandKernelData P n) (j : ℕ) (z : P)
    (hs : ∀ η ∉ wideBand n j, ∀ x, D.kernel z η x = 0)
    (f : WideBandL2 n j) :
    wideBandKernelOperator D j z f =ᵐ[volume]
      fun x ↦ ∫ η in wideBand n j, f η • D.kernel z η x := by
  let t : Fin n → Euclidean n → Euclidean (n - 1) → ℂ :=
    fun i x η ↦ D.kernel z η x i
  have ht (i : Fin n) : Continuous (Function.uncurry (t i)) :=
    (PiLp.continuous_apply 2 _ i).comp
      (D.continuous_kernel.comp ((continuous_const.prodMk continuous_snd).prodMk continuous_fst))
  have hW : IsCompact (wideBand n j) :=
    (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hsupport (i : Fin n) (x : Euclidean n) (η : Euclidean (n - 1))
      (h : (x, η) ∉ D.physicalSupport ×ˢ wideBand n j) : t i x η = 0 := by
    by_cases hx : x ∈ D.physicalSupport
    · have hη : η ∉ wideBand n j := fun hη ↦ h ⟨hx, hη⟩
      simp [t, hs η hη x]
    · simp [t, D.kernel_eq_zero z η x hx]
  let A := compactVectorKernelOperator (wideBand n j) ht
    (fun i ↦ HasCompactSupport.intro (D.physicalSupport_compact.prod hW)
      (fun q hq ↦ hsupport i q.1 q.2 hq))
  have hA : toSamplingOutput A = wideBandKernelOperator D j z := by
    apply ContinuousLinearMap.adjoint.injective
    rw [toSamplingOutput_adjoint]
    ext1 v
    apply Lp.ext
    have hAc : A = kernelSynthesis
        (memLp_compactCoordinateColumn t ht D.physicalSupport_compact hW hsupport
          (wideBand n j)) :=
      compactVectorKernelOperator_eq_synthesis t ht D.physicalSupport_compact hW
        hsupport (wideBand n j)
    change A.adjoint (finiteL2CoordinateIsometry volume v) =ᵐ[_] _
    rw [hAc]
    filter_upwards [kernelSynthesis_hasAdjointKernel
      (memLp_compactCoordinateColumn t ht D.physicalSupport_compact hW hsupport
        (wideBand n j)) (finiteL2CoordinateIsometry volume v),
      wideBandKernelOperator_hasAdjointKernel D j z v] with η ha hb
    rw [ha, hb]
    have hc : compactCoordinateColumn t ht D.physicalSupport_compact hsupport η =
        finiteL2CoordinateIsometry volume (D.column z η) := by
      apply PiLp.ext
      intro i
      apply Lp.ext
      filter_upwards [compactCoordinateColumn_coe t ht D.physicalSupport_compact hsupport η i,
        finiteL2Coordinates_apply_ae volume (D.column z η) i, D.column_coe z η]
        with x hx hy hz
      exact hx.trans (by change _ = ((finiteL2Coordinates volume (D.column z η)) i) x; rw [hy, hz])
    rw [hc]
    exact (finiteL2CoordinateIsometry volume).inner_map_map _ _
  rw [← hA]
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro i
  have h := compactVectorKernelOperator_ae_integral (wideBand n j) ht
    (fun i ↦ HasCompactSupport.intro (D.physicalSupport_compact.prod hW)
      (fun q hq ↦ hsupport i q.1 q.2 hq)) f i
  change (finiteL2CoordinateIsometry volume ((finiteL2CoordinateIsometry volume).symm
    (A f))) i =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  refine h.trans (Filter.Eventually.of_forall fun x ↦ ?_)
  have hk : MemLp (fun η ↦ D.kernel z η x) 2 (volume.restrict (wideBand n j)) :=
    memLp_restrict_compact_column
      (D.continuous_kernel.comp ((continuous_const.prodMk continuous_id).prodMk continuous_const)) hW
  have hi : Integrable (fun η ↦ f η • D.kernel z η x)
      (volume.restrict (wideBand n j)) := memLp_one_iff_integrable.mp ((Lp.memLp f).smul hk)
  have he := (PiLp.proj 2 (fun _ : Fin n ↦ ℂ) i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)
    |>.integral_comp_comm hi
  change _ = (∫ η in wideBand n j, f η • D.kernel z η x) i
  refine Eq.trans ?_ he
  apply integral_congr_ae
  filter_upwards [] with η
  change D.kernel z η x i * f η = f η * D.kernel z η x i
  ring

/-- Either original annular restriction has norm at most the reassembled
smooth band's norm. This is a Hilbert-space deduction, before any use of
smooth symbol calculus (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_annularOperator_le_wideBand (D : BandKernelData P n) (j : ℕ) (z : P)
    (b : Fin 2) :
    ‖D.operator ((2 : ℝ) ^ (j + b.val)) z‖ ≤ ‖wideBandKernelOperator D j z‖ := by
  let R := annularRow (fun b : Fin 2 ↦ D.operator ((2 : ℝ) ^ (j + b.val)) z)
  have hR : ‖wideBandKernelOperator D j z‖ = ‖R‖ := by
    rw [wideBandKernelOperator_eq_refined]
    exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv R (bandRefinement n j)
  rw [hR]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  have h := R.le_opNorm (PiLp.single 2 b f)
  fin_cases b <;> simpa [R, annularRow_apply, PiLp.single_apply, Pi.single_apply,
    PiLp.norm_single] using h

end JanetCartan.Sampling
