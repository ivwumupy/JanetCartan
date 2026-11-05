module

public import JanetCartan.Iteration.PhysicalMean.MomentLocalization
public import JanetCartan.Iteration.PhysicalPairs.FourierNorm
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PeriodicRepresentative

/-!
# The actual smooth current-inverse datum and its compact scalar coordinates

For `app:ch_mean_pairs:eq:raw-adjoint-moments`, the original current inverse
returns a real periodic L² class with all Sobolev memberships. Its existing
literal Fourier representative supplies ONE smooth source, independent of
order. The adjoint localization uses exactly its compact physical cutoff.
Every scalar coordinate in the native matrix moment estimate has the same
source Sobolev order, with constants depending only on the fixed cutoff.
No inverse estimate or replacement source is assumed or selected here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory FourierTransform
open scoped ContDiff

namespace JanetCartan.PhysicalMean

open CurrentMean SmoothPeriodicFamily PeriodicLocalL2 Pseudodifferential

variable {n : ℕ}

/-- One actual smooth representative of an all-order regular output class.
Applied to `Q₀ e`, this retains the SAME current inverse datum. -/
def regularSourceRepresentative (v : ContinuumRow.OutputL2 n)
    (hv : ∀ s, v ∈ periodicSobolevLevel n (Euclidean n) s) : SmoothResidual n :=
  ⟨fun x _ ↦ preparationFourierRepresentative v x,
    fun _ ↦ isSmoothPeriodic_preparationFourierRepresentative v hv⟩

/-- The constructed smooth source represents exactly the supplied L² class,
not an approximation or independently chosen inverse. -/
theorem regularSourceRepresentative_toL2 (v : ContinuumRow.OutputL2 n)
    (hv : ∀ s, v ∈ periodicSobolevLevel n (Euclidean n) s) :
    smoothResidualToL2 n (regularSourceRepresentative v hv) = v := by
  apply Lp.ext
  exact (componentL2_coe_ae () (regularSourceRepresentative v hv)).trans
    (preparationFourierRepresentative_ae v hv).symm

/-- The same representative preserves every periodic source Sobolev norm. -/
theorem regularSourceRepresentative_sobolevNorm (v : ContinuumRow.OutputL2 n)
    (hv : ∀ s, v ∈ periodicSobolevLevel n (Euclidean n) s) (s : ℕ) :
    periodicSobolevNorm s (fun x ↦ (regularSourceRepresentative v hv).val x ()) =
      periodicSobolevNorm s v := by
  simp only [regularSourceRepresentative, periodicSobolevNorm,
    periodicFourierCoeff_congr_ae (preparationFourierRepresentative_ae v hv)]

variable (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)

/-- Literal scalar Schwartz coordinates of the existing localized source. -/
def cutSmoothResidualCoordinate (r : SmoothResidual n) (i : Fin n) :
    SchwartzMap (Euclidean n) ℂ :=
  SchwartzMap.postcompCLM (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) i)
    (PhysicalCutoff.complexify (cutSmoothResidual χ hχ hc r))

@[simp] theorem cutSmoothResidualCoordinate_apply (r : SmoothResidual n) (i : Fin n)
    (x : Euclidean n) :
    cutSmoothResidualCoordinate χ hχ hc r i x = (cutSmoothResidual χ hχ hc r x i : ℂ) := rfl

/-- Each coordinate has the fixed original source cutoff's compact support,
not just Schwartz decay. -/
theorem hasCompactSupport_cutSmoothResidualCoordinate (r : SmoothResidual n) (i : Fin n) :
    HasCompactSupport (cutSmoothResidualCoordinate χ hχ hc r i : Euclidean n → ℂ) := by
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro x hx
  by_contra hxχ
  have hzero := image_eq_zero_of_notMem_tsupport hxχ
  exact hx (by simp only [cutSmoothResidualCoordinate_apply, cutSmoothResidual_apply,
    hzero, zero_smul, PiLp.zero_apply, Complex.ofReal_zero])

/-- Complexification retains exactly the L² inclusion appearing in the real
quadrature adjoint identity; no factor or normalization is changed. -/
theorem cutSmoothResidual_complex_toLp (r : SmoothResidual n) :
    (PhysicalCutoff.complexify (cutSmoothResidual χ hχ hc r)).toLp 2 volume =
      l2ComplexInclusion volume ((cutSmoothResidual χ hχ hc r).toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(PhysicalCutoff.complexify (cutSmoothResidual χ hχ hc r)).coeFn_toLp 2 volume,
    (cutSmoothResidual χ hχ hc r).coeFn_toLp 2 volume,
    (euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL
      ((cutSmoothResidual χ hχ hc r).toLp 2 volume)] with x hleft hsource hright
  exact hleft.trans ((congrArg euclideanComplexInclusion hsource).symm.trans hright.symm)

/-- The exact coordinate isometry of the same complexified cut source has the
literal scalar Schwartz coordinates used by the matrix moment theorem. -/
theorem cutSmoothResidual_coordinates_toLp (r : SmoothResidual n) :
    finiteL2CoordinateIsometry volume
      (l2ComplexInclusion volume ((cutSmoothResidual χ hχ hc r).toLp 2 volume)) =
        WithLp.toLp 2 (fun i ↦ (cutSmoothResidualCoordinate χ hχ hc r i).toLp 2 volume) := by
  rw [← cutSmoothResidual_complex_toLp]
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [finiteL2Coordinates_apply_ae volume
    ((PhysicalCutoff.complexify (cutSmoothResidual χ hχ hc r)).toLp 2 volume) i,
    (PhysicalCutoff.complexify (cutSmoothResidual χ hχ hc r)).coeFn_toLp 2 volume,
    (cutSmoothResidualCoordinate χ hχ hc r i).coeFn_toLp 2 volume] with x hi hv hc
  exact hi.trans ((congrArg (fun z : EuclideanSpace ℂ (Fin n) ↦ z i) hv).trans hc.symm)

private theorem sobolevWeight_le_physical (s : ℕ) (ξ : Euclidean n) :
    euclideanSobolevWeight s ξ ≤ euclideanSobolevWeight s ((2 * Real.pi) • ξ) := by
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hn : ‖ξ‖ ≤ ‖(2 * Real.pi) • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    exact le_mul_of_one_le_left (norm_nonneg _) hπ
  unfold euclideanSobolevWeight
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  gcongr

/-- Every exact scalar source coordinate has a same-order physical Sobolev
bound by the original periodic source. The constant precedes source and
coordinate and depends only on the fixed cutoff and order. -/
theorem exists_cutSmoothResidual_coordinateSobolev_bound
    (hs : tsupport χ ⊆ halfOpenCell n) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : SmoothResidual n, ∀ i : Fin n,
      fourierSobolevNorm s ((cutSmoothResidualCoordinate χ hχ hc r i).toLp 2 volume) ≤
        C * periodicSobolevNorm s (fun x ↦ r.val x ()) := by
  obtain ⟨C, hC, hb⟩ := exists_cutSmoothResidual_physicalSobolev_bound χ hχ hc hs s
  refine ⟨C, hC, ?_⟩
  intro r i
  have hi := fourierSobolevNorm_coordinate_le (s : ℝ)
    (finiteL2CoordinateIsometry volume
      ((PhysicalCutoff.complexify (cutSmoothResidual χ hχ hc r)).toLp 2 volume)) i
  rw [cutSmoothResidual_complex_toLp, cutSmoothResidual_coordinates_toLp] at hi
  have hv : matrixFourierSobolevNorm s
      (WithLp.toLp 2 (fun i ↦ (cutSmoothResidualCoordinate χ hχ hc r i).toLp 2 volume)) =
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ξ •
        𝓕 (PhysicalCutoff.complexify (cutSmoothResidual χ hχ hc r)) ξ) 2 volume).toReal := by
    rw [← cutSmoothResidual_coordinates_toLp, ← cutSmoothResidual_complex_toLp]
    exact PhysicalPairs.vectorFourierSobolevNorm_schwartz_eq s _
  have hp : (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ξ •
      𝓕 (PhysicalCutoff.complexify (cutSmoothResidual χ hχ hc r)) ξ) 2 volume).toReal ≤
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
        𝓕 (PhysicalCutoff.complexify (cutSmoothResidual χ hχ hc r)) ξ) 2 volume).toReal := by
    apply ENNReal.toReal_mono (PhysicalCutoff.memLp_physicalWeightedFourier s
      (cutSmoothResidual χ hχ hc r)).eLpNorm_ne_top
    apply eLpNorm_mono
      ((continuous_euclideanSobolevWeight s).aestronglyMeasurable.smul
        (𝓕 (PhysicalCutoff.complexify (cutSmoothResidual χ hχ hc r))).continuous.aestronglyMeasurable)
    intro ξ
    change ‖euclideanSobolevWeight s ξ •
      𝓕 (PhysicalCutoff.complexify (cutSmoothResidual χ hχ hc r)) ξ‖ ≤
        ‖euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
          𝓕 (PhysicalCutoff.complexify (cutSmoothResidual χ hχ hc r)) ξ‖
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (euclideanSobolevWeight_pos _ _).le,
      Real.norm_of_nonneg (euclideanSobolevWeight_pos _ _).le]
    exact mul_le_mul_of_nonneg_right (sobolevWeight_le_physical s ξ) (norm_nonneg _)
  exact hi.trans (hv.le.trans (hp.trans (hb r)))

end JanetCartan.PhysicalMean
