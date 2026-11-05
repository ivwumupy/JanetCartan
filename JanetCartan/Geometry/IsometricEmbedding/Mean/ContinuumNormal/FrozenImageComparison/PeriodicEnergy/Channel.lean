module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.Model
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.Assembly

/-!
# The fixed frozen channel and its literal lattice correction

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, specialize the proved
one-factor comparison to the fixed outer masks and constant arrays. The source
mask itself supplies the output plateau. These identities are inputs to the
two-factor kernel construction in `FrozenImageComparison.PeriodicEnergy`;
they do not by themselves give the required L¹-squared energy bound.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace
open JanetCartan.ContinuumRow JanetCartan.PeriodicLocalL2
open JanetCartan.Pseudodifferential.DifferentialChart
open JanetCartan.ContinuumNormalReduction.ImageNormal
open JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R²" => EuclideanL2 n E

/-- The fixed physical masks fit the chart used by the literal periodic
comparison (`app:ch_background:prop:bg-frame`, frozen image term). -/
theorem fixedCutoff_tsupport_chartBox (hR : 0 < R) (i : Fin 3) :
    tsupport (FixedCutoffs.physical (n := n) hR i) ⊆ chartBox (4 * R) :=
  ImageGeometry.imageCutoff_support_box (FixedCutoffs.physical_tsupport_four hR i)

/-- The fixed source mask is an open plateau around the entire measurement
support, including its boundary (`app:ch_background:prop:bg-frame`). -/
theorem fixedSource_eventuallyEq_one (hR : 0 < R) {x : E}
    (hx : x ∈ tsupport (FixedCutoffs.physical hR 1)) :
    (FixedCutoffs.physical hR 2 : E → ℝ) =ᶠ[nhds x] (fun _ ↦ 1) := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨interior {y : E | FixedCutoffs.physical hR 2 y = 1}, ?_, ?_⟩
  · apply isOpen_interior.mem_nhds
    apply FixedCutoffs.physical_plateau hR 2
    have hs := ball_subset_closedBall (FixedCutoffs.physical_tsupport hR 1 hx)
    convert hs using 1
    norm_num
  · intro y hy
    exact (show y ∈ {y : E | FixedCutoffs.physical hR 2 y = 1} from interior_subset hy)

/-- The actual differentiated nonzero-lattice kernel of the frozen channel.
Both occurrences of the source cutoff are intentional: the first is the
output plateau, the second is the original input mask
(`app:ch_background:prop:bg-frame`, frozen image comparison). -/
def fixedLatticeKernel (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : E × E → ℝ :=
  oneFactorRemainderKernel (FixedCutoffs.physical hR 2)
    (FixedCutoffs.physical hR 2) (FixedCutoffs.physical hR 1)
    (fun _ ↦ A) (fun _ ↦ 0) i j

/-- The fixed one-factor kernel is smooth; its actual normal products still
have to be identified (`app:ch_background:prop:bg-frame`). -/
theorem contDiff_fixedLatticeKernel (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ContDiff ℝ ∞ (fixedLatticeKernel hR A i j) :=
  contDiff_oneFactorRemainderKernel hcell _ _ _
    (FixedCutoffs.physical hR 2).contDiff (FixedCutoffs.physical hR 2).contDiff
    (FixedCutoffs.physical hR 1).contDiff
    (fun _ hx ↦ fixedCutoff_tsupport_chartBox hR 2 (subset_tsupport _ hx))
    (fun _ hx ↦ fixedCutoff_tsupport_chartBox hR 2 (subset_tsupport _ hx))
    (fun _ ↦ A) (fun _ ↦ 0)
    (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const) i j

/-- The fixed one-factor kernel keeps the measurement and source supports
in their original order (`app:ch_background:prop:bg-frame`). -/
theorem tsupport_fixedLatticeKernel_subset (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    tsupport (fixedLatticeKernel hR A i j) ⊆
      tsupport (FixedCutoffs.physical hR 1) ×ˢ
        tsupport (FixedCutoffs.physical hR 2) :=
  tsupport_oneFactorRemainderKernel_subset _ _ _ _ _ i j

/-- Joint compact support of the actual one-factor kernel
(`app:ch_background:prop:bg-frame`, frozen image comparison). -/
theorem hasCompactSupport_fixedLatticeKernel (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    HasCompactSupport (fixedLatticeKernel hR A i j) :=
  hasCompactSupport_oneFactorRemainderKernel _ _ _
    (fun _ hx ↦ fixedCutoff_tsupport_chartBox hR 2 (subset_tsupport _ hx))
    (fun _ hx ↦ fixedCutoff_tsupport_chartBox hR 1 (subset_tsupport _ hx)) _ _ i j

/-- The bounded real operator constructed from the fixed lattice kernel,
not from a subtraction of channels (`app:ch_background:prop:bg-frame`). -/
def fixedLatticeOperator (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) : R² →L[ℝ] R² :=
  realOneFactorRemainderOperator hcell (FixedCutoffs.physical hR 2)
    (FixedCutoffs.physical hR 2) (FixedCutoffs.physical hR 1)
    (FixedCutoffs.physical hR 2).contDiff (FixedCutoffs.physical hR 2).contDiff
    (FixedCutoffs.physical hR 1).contDiff
    (fun _ hx ↦ fixedCutoff_tsupport_chartBox hR 2 (subset_tsupport _ hx))
    (fun _ hx ↦ fixedCutoff_tsupport_chartBox hR 2 (subset_tsupport _ hx))
    (fun _ hx ↦ fixedCutoff_tsupport_chartBox hR 1 (subset_tsupport _ hx))
    (fun _ ↦ A) (fun _ ↦ 0) (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const)

/-- Literal integral action of the fixed lattice correction on every real
L² input (`app:ch_background:prop:bg-frame`, frozen image comparison). -/
theorem fixedLatticeOperator_ae_integral
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (f : R²) :
    fixedLatticeOperator hR hcell A f =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (fun i ↦ ∑ j, ∫ y, fixedLatticeKernel hR A i j (x, y) * f y j) :=
  realOneFactorRemainderOperator_ae_integral _ _ _ _ _ _ _ _ _ _ _ _ _ _ f

/-- The actual adjoint integrates the reversed transposed fixed kernel
(`app:ch_background:prop:bg-frame`, frozen image comparison). -/
theorem fixedLatticeOperator_adjoint_ae_integral
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (f : R²) :
    (fixedLatticeOperator hR hcell A).adjoint f =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (fun j ↦ ∑ i, ∫ x, fixedLatticeKernel hR A i j (x, y) * f x i) :=
  realOneFactorRemainderOperator_adjoint_ae_integral _ _ _ _ _ _ _ _ _ _ _ _ _ _ f

set_option maxHeartbeats 800000 in
/-- The fixed periodic channel equals the masked Euclidean channel plus its
concrete lattice correction, on all real L². The auxiliary plateau is the
original source mask; no new support radius enters the objects
(`app:ch_background:prop:bg-frame`, frozen image comparison). -/
theorem pullback_fixedPeriodicChannel_eq_add_latticeOperator (hn : 0 < n)
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    pullback (fixedPeriodicChannel hR hcell A) =
      fixedEuclideanChannel hR A + fixedLatticeOperator hR hcell A := by
  let S : ℝ := (4 * R + 1 / 2) / 2
  have hRS : 4 * R < S := by dsimp [S]; linarith
  have hS : S < 1 / 2 := by dsimp [S]; linarith
  have hS₀ : 0 < S := lt_trans (by positivity : 0 < 4 * R) hRS
  have hc : ∀ k, IsSmoothPeriodic (constantImageCoefficients A k) := by
    intro k
    cases k with
    | inl k => exact ⟨continuous_const, contDiff_const⟩
    | inr k => exact ⟨continuous_const, contDiff_const⟩
  have hρs : tsupport (FixedCutoffs.physical (n := n) hR 2) ⊆ chartBox S := by
    intro x hx a
    exact (fixedCutoff_tsupport_chartBox hR 2 hx a).trans hRS.le
  exact periodicChannel_eq_add_oneFactorRemainder hn hcell hS₀ hRS hS
    (constantImageCoefficients A) hc
    (FixedCutoffs.physical hR 2) (FixedCutoffs.physical hR 1)
    (FixedCutoffs.physical hR 2)
    (FixedCutoffs.physical hR 2).contDiff (FixedCutoffs.physical hR 1).contDiff
    (FixedCutoffs.physical hR 2).contDiff
    (fixedCutoff_tsupport_chartBox hR 2) (fixedCutoff_tsupport_chartBox hR 1)
    hρs (fun _ hx ↦ fixedSource_eventuallyEq_one hR hx)
    (fun _ ↦ A) (fun _ ↦ 0) (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const)
    (fun _ _ _ _ _ ↦ Filter.EventuallyEq.rfl) (fun _ _ _ _ ↦ Filter.EventuallyEq.rfl)
    (fixedEuclideanChannel hR A)
    (euclideanChannel_schwartz_action _ _ _ _ _ _ _ _ _ _)

/-- Both Bessel factors are expanded, retaining `B D*`, `D B*`, and `D D*`
with the original source masks (`app:ch_background:prop:bg-frame`). -/
theorem fixedPeriodicNormal_eq_euclidean_add_crossTerms (hn : 0 < n)
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    pullback ((fixedPeriodicChannel hR hcell A).comp
      (fixedPeriodicChannel hR hcell A).adjoint) =
      (fixedEuclideanChannel hR A).comp (fixedEuclideanChannel hR A).adjoint +
        normalCrossTerms (fixedEuclideanChannel hR A) (fixedLatticeOperator hR hcell A) :=
  pullback_normal_eq_of_channel_eq _ _ _
    (pullback_fixedPeriodicChannel_eq_add_latticeOperator hn hR hcell A)

/-- The frozen periodic energy error is the quadratic form of all three
actual cross terms. The fixed normal-kernel identity must identify this
operator to obtain the L¹-squared bound (`app:ch_background:prop:bg-frame`). -/
theorem fixedPeriodicEnergyDifference_eq_inner_crossTerms (hn : 0 < n)
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (f : OutputL2 n) :
    let u := toEuclidean (𝕜 := ℝ) f
    ‖(fixedPeriodicChannel hR hcell A).adjoint f‖ ^ 2 -
        ‖(fixedEuclideanChannel hR A).adjoint u‖ ^ 2 =
      ⟪u, normalCrossTerms (fixedEuclideanChannel hR A)
        (fixedLatticeOperator hR hcell A) u⟫ := by
  dsimp only
  rw [← norm_fixedPeriodicPullback_adjoint_zeroExtension hR hcell A f]
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  have he := DFunLike.congr_fun (fixedPeriodicNormal_eq_euclidean_add_crossTerms
    hn hR hcell A) (toEuclidean (𝕜 := ℝ) f)
  rw [pullback_normal] at he
  simp only [ContinuousLinearMap.comp_apply, add_apply] at he
  rw [he, inner_add_right]
  ring

end JanetCartan.ContinuumNormal.FrozenImageComparison
