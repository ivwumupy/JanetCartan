module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.Quadratures
public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.FiniteAccuracy
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.QuadratureSource
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.RealCompression

/-!
# The initial defect on the original local real source

The cutoff proves admission of the actual zero extension. The SAME even right
mask acts through the existing `localRealCompression`, and its single identity
subtraction is the restricted real quadrature of the complex defect. This is
the local source used by `finiteChain_observation_rapidDecayAt.hsource`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff JanetCartan.RegularSector.Realization

namespace JanetCartan.InitialSourceLocalization

open FiniteChain.Graph JanetCartan.Localization Pseudodifferential LocalSobolev
open RegularSector.Realization ArbitraryAccuracy.ResidualLocalization
open RegularSector.Characteristic.RetardedLocalization ResponseTransfer.SourceNegative

variable {d r : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "RV" => EuclideanSpace ℝ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

private theorem initial_quadrature_restriction_ae (W : Set E) (u : H) (c : ℂ) :
    l2RealPart (volume.restrict W) (c • restrictL2 W u) =ᵐ[volume.restrict W]
      l2RealPart volume (c • u) := by
  filter_upwards [euclideanRealPart.coeFn_compLpL (c • restrictL2 W u),
    Lp.coeFn_smul c (restrictL2 W u), restrictL2_coeFn W u,
    ae_restrict_of_ae (euclideanRealPart.coeFn_compLpL (c • u)),
    ae_restrict_of_ae (Lp.coeFn_smul c u)] with y hr hs hi hg hc
  change (l2RealPart (volume.restrict W) (c • restrictL2 W u)) y = _ at hr
  change (l2RealPart volume (c • u)) y = _ at hg
  rw [hr, hs, Pi.smul_apply, hi, hg, hc, Pi.smul_apply]

/-- The original source cutoff supplies the zero extension in the local
identity-minus-first-mask defect. Both quadratures use the given even mask
and its given bounded right realization (`app:ch_regular:eq:source-tail`). -/
theorem local_initialSource_modulated_quadrature_defect
    (ρ : ℝ) (m : LocalizerSymbol (d+1)) (heven : ∀ y ξ, m (y, -ξ) = m (y, ξ))
    (M : H →L[ℂ] H)
    (hM : ∀ v : H, M v =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ m (fun y ↦ (v y).ofLp) x))
    (χ φ : E → ℝ) (a : E → V) (hf : MemLp (modulatedSource χ φ a ρ) 2 volume)
    {W : Set E} (hW : MeasurableSet W) (hχW : tsupport χ ⊆ W) (c : ℂ) :
    let u := hf.toLp (modulatedSource χ φ a ρ)
    let h := l2RealPart (volume.restrict W) (c • restrictL2 W u)
    h - localRealCompression hW W M h =
      l2RealPart (volume.restrict W) (c • restrictL2 W (u - M u)) := by
  intro u h
  have hlocal := localRealCompression_coeFn hW W M h
  rw [zeroExtend_restrictL2_modulatedSource_real_quadrature hW χ φ a ρ hχW hf c]
    at hlocal
  have hinput := initial_quadrature_restriction_ae W u c
  have houtput := initial_quadrature_restriction_ae W (u - M u) c
  rw [← initialSource_real_quadrature_defect ρ m heven M hM u c] at houtput
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub h (localRealCompression hW W M h), hlocal, hinput,
    houtput, ae_restrict_of_ae (Lp.coeFn_sub (l2RealPart volume (c • u))
      (realCompression M (l2RealPart volume (c • u))))] with y hs hl hi ho hg
  rw [hs, Pi.sub_apply, hl, hi, ho, hg, Pi.sub_apply]

/-- Unit real quadratures of the initial defect have the same restriction
regularity and a fixed factor two. This uses actual weak-jet extensions,
and supplies the real source estimate from the complex one
(`app:ch_regular:lem:finite-chain`, `app:ch_osc:cor:osc-real`). -/
theorem initial_quadrature_restriction_scale_bound
    (W : Set E) (hW : MeasurableSet W) (s : ℕ) (u : LocalL2 W V)
    (hu : u ∈ (restrictionSobolevScale W V hW).level s) (c : ℂ) (hc : ‖c‖ = 1) :
    l2RealPart (volume.restrict W) (c • u) ∈ (restrictionSobolevScale W RV hW).level s ∧
      (restrictionSobolevScale W RV hW).gradeNorm s
        (l2RealPart (volume.restrict W) (c • u)) ≤
          2 * (restrictionSobolevScale W V hW).gradeNorm s u := by
  let L : V →L[ℝ] RV := euclideanRealPart.comp
    ((c • ContinuousLinearMap.id ℂ V).restrictScalars ℝ)
  have hL : ‖L‖ ≤ 1 := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    have hid : ‖(c • ContinuousLinearMap.id ℂ V).restrictScalars ℝ‖ ≤ 1 := by
      rw [ContinuousLinearMap.norm_restrictScalars, norm_smul, hc, one_mul]
      exact ContinuousLinearMap.norm_id_le
    exact (mul_le_mul euclideanRealPart_norm_le hid (norm_nonneg _) zero_le_one).trans_eq
      (mul_one 1)
  have he : L.compLp u = l2RealPart (volume.restrict W) (c • u) := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLp u, euclideanRealPart.coeFn_compLpL (c • u),
      Lp.coeFn_smul c u] with y hl hr hs
    change (l2RealPart (volume.restrict W) (c • u)) y = _ at hr
    rw [hl, hr, hs, Pi.smul_apply]
    rfl
  obtain ⟨hm, hb⟩ := compLp_restrictionSobolev_bound L hu
  rw [he] at hm hb
  refine ⟨hm, ?_⟩
  rw [restrictionSobolevScale_gradeNorm hW hm, restrictionSobolevScale_gradeNorm hW hu]
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith : ‖L‖ + 1 ≤ 2)
    restrictionSobolevNorm_nonneg)

end JanetCartan.InitialSourceLocalization
