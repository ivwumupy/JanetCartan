module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.Basic

/-!
# Transport of the original image cutoffs

The periodized cutoff and physical multiplication intertwine under the actual
cell maps in `app:ch_background:defn:bg-row`. These identities connect the
one-inverse local comparison to the cutoff factors of `ContinuumRow.imageChannel`;
they do not identify the torus and Euclidean inverse kernels.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open JanetCartan.PeriodicLocalL2
open JanetCartan.Pseudodifferential.DifferentialChart

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ} {r : ℝ} (hr : r < 1 / 2)
    (χ : EuclideanSpace ℝ (Fin d) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ chartBox r)
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "M" => realImageCutoffOperator (I := Fin d) χ hχ.continuous
  (hasCompactSupport_of_imageBessel_cube_support χ (fun x hx ↦ hχs (subset_tsupport χ hx)))
local notation "MT" => ContinuumRow.cutoffMultiplier (periodizedCutoff hr χ hχ hχs)

/-- Euclidean extension intertwines the original cutoff multipliers with
their literal real periodizations (`app:ch_background:defn:bg-row`). -/
theorem toEuclidean_cutoffMultiplier :
    (toEuclidean (n := d) (𝕜 := ℝ) (F := E)).toContinuousLinearMap.comp MT =
      (M).comp toEuclidean.toContinuousLinearMap := by
  ext1 f
  apply Lp.ext
  have hcut := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae_eq_comp
      (ContinuumRow.cutoffMultiplier_coeFn (periodizedCutoff hr χ hχ hχs) f))
  filter_upwards [toEuclidean_coe (𝕜 := ℝ) (MT f), toEuclidean_coe (𝕜 := ℝ) f,
    realImageCutoffOperator_coe χ hχ.continuous
      (hasCompactSupport_of_imageBessel_cube_support χ
        (fun x hx ↦ hχs (subset_tsupport χ hx))) (toEuclidean (𝕜 := ℝ) f),
    hcut] with x hx hy hz ht
  change toEuclidean (𝕜 := ℝ) (MT f) x = M (toEuclidean (𝕜 := ℝ) f) x
  rw [hx, hz, hy]
  by_cases hc : x ∈ halfOpenCell d
  · simp only [Set.indicator_of_mem hc, periodicLift, Function.comp_apply]
    have hm := (periodizedCutoff_eventuallyEq hr χ hχ hχs
      (halfOpenCell_subset_fundamentalCell hc)).self_of_nhds
    exact (ht hc).trans (congrArg (fun a : ℝ ↦ a • f (torusQuotient x)) hm)
  · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hc (chartBox_subset_cell hr (hχs h)))
    simp only [Set.indicator_of_notMem hc, hχx, zero_smul]

/-- Restriction intertwines the same cutoffs. This is the literal adjoint
of the extension identity (`app:ch_background:defn:bg-row`). -/
theorem toTorus_realImageCutoffOperator :
    (toTorus (n := d) (𝕜 := ℝ) (F := E)).comp M = (MT).comp toTorus := by
  have h := congrArg ContinuousLinearMap.adjoint (toEuclidean_cutoffMultiplier hr χ hχ hχs)
  simpa only [ContinuousLinearMap.adjoint_comp, toEuclidean_adjoint,
    ContinuumRow.cutoffMultiplier_adjoint, realImageCutoffOperator_adjoint] using h.symm

/-- Pulling back the periodic cutoff gives the exact physical multiplier on
all Lebesgue L² data (`app:ch_background:defn:bg-row`). -/
theorem pullback_cutoffMultiplier : pullback MT = M := by
  ext1 f
  change toEuclidean (𝕜 := ℝ) (MT (toTorus (𝕜 := ℝ) f)) = M f
  have he := DFunLike.congr_fun (toTorus_realImageCutoffOperator hr χ hχ hχs) f
  change toTorus (𝕜 := ℝ) (M f) = MT (toTorus (𝕜 := ℝ) f) at he
  rw [← he]
  apply toEuclidean_toTorus
  filter_upwards [realImageCutoffOperator_coe χ hχ.continuous
    (hasCompactSupport_of_imageBessel_cube_support χ
      (fun x hx ↦ hχs (subset_tsupport χ hx))) f] with x hx hxc
  rw [hx, image_eq_zero_of_notMem_tsupport
    (fun h ↦ hxc (chartBox_subset_cell hr (hχs h))), zero_smul]

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
