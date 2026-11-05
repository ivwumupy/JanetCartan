module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.Sobolev
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Assembly.Components
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Density

/-!
# Compact extension of periodic vector data

For `app:ch_background:prop:bg-adjoint`, the source cutoff transfers the literal
vector periodic Sobolev norm to the existing Euclidean Fourier Sobolev norm.
These comparisons are consumed by the periodic raw adjoint transfer.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open Pseudodifferential Pseudodifferential.DifferentialChart
variable {n : ℕ}

/-- Coordinate projections preserve smooth periodic data
(`app:ch_background:prop:bg-adjoint`). -/
theorem smoothPeriodic_vector_coordinate {u : Torus n → EuclideanSpace ℂ (Fin n)}
    (hu : IsSmoothPeriodic u) (j : Fin n) : IsSmoothPeriodic (fun x ↦ u x j) :=
  hu.comp_clm ((EuclideanSpace.proj j).restrictScalars ℝ)

/-- The finite Hilbert sum of scalar periodic Sobolev norms is the literal
vector periodic norm, with both real Fourier quadratures and the original Haar
measure (`app:ch_background:prop:bg-adjoint`). -/
theorem periodicSobolevNorm_vector_coordinates (s : ℕ)
    {u : Torus n → EuclideanSpace ℂ (Fin n)} (hu : IsSmoothPeriodic u) :
    ‖(WithLp.toLp 2 (fun j ↦ periodicSobolevNorm s (fun x ↦ u x j)) :
      EuclideanSpace ℝ (Fin n))‖ = periodicSobolevNorm s u := by
  have hc (j : Fin n) (k : Fin n → ℤ) :
      periodicFourierCoeff (fun x ↦ u x j) k =
        ((periodicFourierCoeff u k).1 j, (periodicFourierCoeff u k).2 j) :=
    periodicFourierCoeff_map ((EuclideanSpace.proj j).restrictScalars ℝ) hu.1 k
  have hs (f : Torus n → ℂ) : periodicSobolevNorm s f ^ 2 =
      ∑' k, (1 + frequencyNorm k ^ 2) ^ (s : ℝ) *
        (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2) := by
    exact Real.sq_sqrt (tsum_nonneg fun _ ↦ by positivity)
  have hn : 0 ≤ periodicSobolevNorm s u := Real.sqrt_nonneg _
  rw [← sq_eq_sq₀ (norm_nonneg _) hn, PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs, hs]
  rw [← Summable.tsum_finsetSum (fun j _ ↦
    (smoothPeriodic_vector_coordinate hu j).summable_periodicSobolevNorm s)]
  unfold periodicSobolevNorm
  rw [Real.sq_sqrt (tsum_nonneg fun _ ↦ by positivity)]
  apply tsum_congr
  intro k
  simp only [hc, EuclideanSpace.norm_sq_eq, ← Finset.sum_add_distrib, ← Finset.mul_sum]

/-- A smooth vector test's compact extension, synthesized from the already
constructed scalar extensions (`app:ch_background:prop:bg-adjoint`). -/
def periodicVectorExtension {r : ℝ} (ψ : SourceCutoff n r)
    {u : Torus n → EuclideanSpace ℂ (Fin n)} (hu : IsSmoothPeriodic u) :
    EuclideanL2 n (EuclideanSpace ℂ (Fin n)) :=
  (finiteL2CoordinateIsometry volume).symm
    (WithLp.toLp 2 (fun j ↦ ψ.extendL2 (smoothPeriodic_vector_coordinate hu j)))

/-- The coordinate realization uses the original scalar extensions
(`app:ch_background:prop:bg-adjoint`). -/
theorem periodicVectorExtension_coordinates {r : ℝ} (ψ : SourceCutoff n r)
    {u : Torus n → EuclideanSpace ℂ (Fin n)} (hu : IsSmoothPeriodic u) :
    finiteL2CoordinateIsometry volume (periodicVectorExtension ψ hu) =
      WithLp.toLp 2 (fun j ↦ ψ.extendL2 (smoothPeriodic_vector_coordinate hu j)) :=
  (finiteL2CoordinateIsometry volume).apply_symm_apply _

/-- The actual vector representative of compact extension
(`app:ch_background:prop:bg-adjoint`). -/
theorem periodicVectorExtension_coe {r : ℝ} (ψ : SourceCutoff n r)
    {u : Torus n → EuclideanSpace ℂ (Fin n)} (hu : IsSmoothPeriodic u) :
    periodicVectorExtension ψ hu =ᵐ[volume] fun x ↦ ψ.toFun x • periodicLift u x := by
  rw [finiteL2CoordinateIsometry_ae_iff, periodicVectorExtension_coordinates]
  intro j
  filter_upwards [ψ.extendL2_coe (smoothPeriodic_vector_coordinate hu j)] with x hx
  change ψ.extendL2 (smoothPeriodic_vector_coordinate hu j) x = _
  rw [hx]
  change (ψ.toFun x : ℂ) * u (torusQuotient x) j = ψ.toFun x • u (torusQuotient x) j
  rw [Complex.real_smul]

/-- Compact extension has every finite Euclidean Fourier Sobolev order
(`app:ch_background:prop:bg-adjoint`). -/
theorem periodicVectorExtension_mem {r : ℝ} (ψ : SourceCutoff n r)
    {u : Torus n → EuclideanSpace ℂ (Fin n)} (hu : IsSmoothPeriodic u) (s : ℕ) :
    MemVectorFourierSobolev s (periodicVectorExtension ψ hu) := by
  intro j
  change MemFourierSobolev s (finiteL2CoordinateIsometry volume
    (periodicVectorExtension ψ hu) j)
  rw [periodicVectorExtension_coordinates]
  exact memFourierSobolev_nat_toLp s _
    (ψ.smooth_extend (smoothPeriodic_vector_coordinate hu j)) (ψ.compact_extend _)

/-- Compact extension is contractive in the original L² norms
(`app:ch_background:prop:bg-adjoint`). -/
theorem norm_periodicVectorExtension_le {r : ℝ} (ψ : SourceCutoff n r)
    {u : Torus n → EuclideanSpace ℂ (Fin n)} (hu : IsSmoothPeriodic u)
    (v : PeriodicL2 n (EuclideanSpace ℂ (Fin n))) (hv : v =ᵐ[volume] u) :
    ‖periodicVectorExtension ψ hu‖ ≤ ‖v‖ := by
  rw [← (toEuclidean (𝕜 := ℂ)).norm_map v]
  apply Lp.norm_le_norm_of_ae_le
  have hlift := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae_eq_comp hv)
  filter_upwards [periodicVectorExtension_coe ψ hu, toEuclidean_coe (𝕜 := ℂ) v, hlift]
    with x hx hy hz
  rw [hx, hy]
  by_cases hc : x ∈ halfOpenCell n
  · rw [indicator_of_mem hc, show periodicLift v x = periodicLift u x from hz hc,
      norm_smul, Real.norm_of_nonneg (ψ.range x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (ψ.range x).2
  · have hz : ψ.toFun x = 0 := by
      by_contra h
      exact hc (subset_halfOpenCell_of_strict (fun _ h ↦ h)
        (ψ.support_cell (subset_tsupport _ h)))
    simp [hz, hc]

/-- A constant chosen solely from the fixed cutoff and order controls vector
extension. No datum or adjoint budget enters its choice
(`app:ch_background:prop:bg-adjoint`). -/
theorem exists_periodicVectorExtension_bound {r : ℝ} (ψ : SourceCutoff n r) (s : ℕ) :
    ∃ B ≥ 0, ∀ (u : Torus n → EuclideanSpace ℂ (Fin n)) (hu : IsSmoothPeriodic u),
      vectorFourierSobolevNorm s (periodicVectorExtension ψ hu) ≤
        B * ‖PeriodicSobolevSpace.ofSmooth s u hu‖ := by
  obtain ⟨B, hB, hb⟩ := ψ.exists_matrix_sobolev_extension_bound s
  refine ⟨B, hB, fun u hu ↦ ?_⟩
  have he : ‖PeriodicSobolevSpace.ofSmooth s u hu‖ = periodicSobolevNorm s u := by
    rw [PeriodicSobolevSpace.norm_eq]
    simp only [periodicSobolevNorm,
      periodicFourierCoeff_congr_ae (PeriodicSobolevSpace.toL2_ofSmooth_ae s u hu)]
  unfold vectorFourierSobolevNorm matrixFourierSobolevNorm
  rw [periodicVectorExtension_coordinates, he]
  simpa only [PiLp.toLp_apply, periodicSobolevNorm_vector_coordinates s hu] using
    hb (Fin n) (fun j x ↦ u x j) (smoothPeriodic_vector_coordinate hu)

end JanetCartan.ContinuumAdjoint.DerivativeKernels
