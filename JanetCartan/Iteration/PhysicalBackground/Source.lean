module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.PhysicalCancellation

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalBackground
open ContinuumRow CarrierSobolev PositiveBackground

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- The literal v2 source `-χmeas q_F R₀`, using cutoff 1, not cutoff 0
(`app:ch_background:eq:bg-density-input`). Only the compact source is
localized on the torus; physical histories are not periodized. -/
def measuredSourceToL2 {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r))) : OutputL2 n :=
  -fixedResidualToL2 hr hcell Q R hQ hR

/-- Exact measured-source normalization, including the cutoff transition
region; no second measurement multiplier is inserted. -/
theorem measuredSourceToL2_coeFn {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r))) :
    measuredSourceToL2 hr hcell Q R hQ hR =ᵐ[volume]
      fun z ↦ -(FixedCutoffs.periodic hr hcell 1 z •
        WithLp.toLp 2 (CubeKernel.tensorContraction
          (Q (AmplitudeBound.centeredTorusRepresentative z))
          (R (AmplitudeBound.centeredTorusRepresentative z)))) := by
  filter_upwards [Lp.coeFn_neg (fixedResidualToL2 hr hcell Q R hQ hR),
    fixedResidualToL2_coeFn hr hcell Q R hQ hR] with x hx he
  exact hx.trans (congrArg Neg.neg he)

/-- Local smoothness proves every Sobolev membership for the same measured
source, ready for task22's uncorrected current inverse. -/
theorem measuredSourceToL2_mem {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (Q : Euclidean n → Fin n → MetricTensor n) (R : MetricField n)
    (hQ : ContDiffOn ℝ ∞ Q (ball 0 (4 * r)))
    (hR : ContDiffOn ℝ ∞ R (ball 0 (4 * r))) (s : ℕ) :
    measuredSourceToL2 hr hcell Q R hQ hR ∈ periodicSobolevLevel n (Euclidean n) s := by
  apply (periodicSobolevLevel n (Euclidean n) s).neg_mem
  exact (periodicSobolevLevel n (Euclidean n) s).smul_mem (-2 : ℝ)
    (sourceToL2_mem _ (fixedCutReducedSource_periodic hr hcell hQ hR 1) s)

/-- The physical source with the actual residual `Dγ_F(dF X₀)+H_F[σ²]`.
The caller retains the original limiting mean in `X₀`. -/
def physicalSourceToL2 {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (F : Euclidean n → Euclidean N) (X₀ : Euclidean n → Euclidean n) (H : MetricField n)
    (hF : ContDiffOn ℝ ∞ F (ball 0 (4 * r)))
    (hX₀ : ContDiffOn ℝ ∞ X₀ (ball 0 (4 * r)))
    (hH : ContDiffOn ℝ ∞ H (ball 0 (4 * r)))
    (himm : IsImmersionOn F (ball 0 (4 * r)))
    (hrank : HasFullNormalRankOn F (ball 0 (4 * r))) : OutputL2 n :=
  -physicalBackgroundResidualToL2 hr hcell F X₀ H hF hX₀ hH himm hrank

/-- `h=A_F* E₀⁻¹ e`, with the unchanged supplied exterior slot. -/
def rawCorrection (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (ψ : C(Torus n, ℝ)) (e : OutputL2 n) : AugmentedInput n ι :=
  CoerciveInverse.rightInverse (augmentedRow image U ψ) e

/-- The literal factor-two v2 density on all initial variables. There is no
initial-position cutoff or upper-frequency truncation. -/
def uncutDensity (d : ι → CarrierData n N)
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (ψ : C(Torus n, ℝ)) (e : OutputL2 n) (i : ι) : CarrierVariable n → ℝ :=
  UncutDensity.initialDensity (d i) 2 ((rawCorrection image U ψ e).fst.snd i)

/-- The same current augmented row solves its measured source. The gap is
produced by task19/22, before constructing the positive density. -/
theorem row_rawCorrection (image : OutputL2 n →L[ℝ] OutputL2 n)
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (ψ : C(Torus n, ℝ)) (e : OutputL2 n) {gap : ℝ} (hgap : 0 < gap)
    (hcoercive : ∀ w, gap * ‖w‖ ^ 2 ≤ ‖(augmentedRow image U ψ).adjoint w‖ ^ 2) :
    augmentedRow image U ψ (rawCorrection image U ψ e) = e :=
  CoerciveInverse.apply_rightInverse _ hgap hcoercive e

end JanetCartan.PhysicalBackground
