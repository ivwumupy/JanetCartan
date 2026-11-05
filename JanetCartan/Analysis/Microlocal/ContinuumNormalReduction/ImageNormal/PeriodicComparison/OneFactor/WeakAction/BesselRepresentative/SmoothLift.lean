module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.Cutoff
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.RealAssembly

/-!
# A smooth representative of the actual masked Bessel lift

For `app:ch_background:prop:bg-frame`, Step 1, periodize the Euclidean
Schwartz Bessel outputs coordinatewise and take their real parts. The actual
real inverse identifies this smooth function with the prescribed H¹ lift.
The consumer is `exists_smooth_localized_periodicBesselLift`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff SchwartzMap
open JanetCartan.PeriodicLocalL2 JanetCartan.AmplitudeBound
open JanetCartan.Pseudodifferential.DifferentialChart
open JanetCartan.ContinuumNormal

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison.BesselRepresentative

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Extract the given Schwartz representative in each complex coordinate,
for the smooth Bessel construction in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem coordinate_eq_toLp (v : Fin d → 𝓢(E, ℂ)) (f : EuclideanL2 d E)
    (hf : l2ComplexInclusion volume f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun j ↦ v j x)) (j : Fin d) :
    complexifiedL2Coordinate volume j f = (v j).toLp 2 := by
  apply Lp.ext
  filter_upwards [complexifiedL2Coordinate_coe volume j f,
    euclideanComplexInclusion.coeFn_compLpL f, hf, (v j).coeFn_toLp 2]
    with x hc hi hv hj
  rw [hc, hj]
  exact congrArg (fun z : EuclideanSpace ℂ (Fin d) ↦ z j) (hi.symm.trans hv)

/-- The real source mask has its literal Schwartz action, used in both the
smooth lift and localized comparison (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem cutoff_coordinate_eq_toLp (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (v : Fin d → 𝓢(E, ℂ)) (f : EuclideanL2 d E)
    (hf : l2ComplexInclusion volume f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun j ↦ v j x)) (j : Fin d) :
    complexifiedL2Coordinate volume j (realImageCutoffOperator χ hχ.continuous hχc f) =
      (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ)) (v j)).toLp 2 := by
  rw [complexifiedL2Coordinate_realImageCutoffOperator, coordinate_eq_toLp v f hf]
  have ht : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp (hχc.hasTemperateGrowth hχ)
  apply Lp.ext
  filter_upwards [freezingPhysicalMultiplier_coeFn χ hχ.continuous hχc ((v j).toLp 2),
    (v j).coeFn_toLp 2,
    (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ)) (v j)).coeFn_toLp 2]
    with x hx hv hu
  rw [hx, hv, hu, SchwartzMap.smulLeftCLM_apply_apply ht, Complex.real_smul, smul_eq_mul]

/-- The actual masked real inverse admits a smooth periodic representative.
This supplies the H¹ identity for `exists_smooth_localized_periodicBesselLift`
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem exists_smooth_periodicBesselLift {r : ℝ} (hr : r < 1 / 2)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ chartBox r)
    (v : Fin d → 𝓢(E, ℂ)) (f : EuclideanL2 d E)
    (hf : l2ComplexInclusion volume f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun j ↦ v j x)) :
    ∃ (w : Torus d → E) (hw : IsSmoothPeriodic w),
      ContinuumRow.periodicBesselLift
        (ContinuumRow.cutoffMultiplier (periodizedCutoff hr χ hχ hχs) (toTorus (𝕜 := ℝ) f)) =
        PeriodicSobolevSpace.ofSmooth 1 w hw := by
  let u (j : Fin d) := SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ)) (v j)
  let b (j : Fin d) := imageBesselSchwartzCLM (u j)
  let W (j : Fin d) := schwartzTorusPeriodization (b j)
  let w (z : Torus d) : E := WithLp.toLp 2 (fun j ↦ (W j z).re)
  have hχc : HasCompactSupport χ := hasCompactSupport_of_imageBessel_cube_support χ
    (fun x hx ↦ hχs (subset_tsupport χ hx))
  have ht : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp (hχc.hasTemperateGrowth hχ)
  have hus (j : Fin d) : SupportedInCenteredBox r (u j) := by
    intro x hx
    apply hχs (subset_tsupport χ ?_)
    intro hz
    apply hx
    simp [u, SchwartzMap.smulLeftCLM_apply_apply ht, hz]
  have hw : IsSmoothPeriodic w := by
    constructor
    · exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j ↦
        Complex.continuous_re.comp (W j).continuous)
    · have he : periodicLift w = fun x ↦ WithLp.toLp 2
          (fun j ↦ (schwartzLatticePeriodization (b j) x).re) := by
        funext x
        simp [periodicLift, w, W]
      rw [he]
      exact PiLp.contDiff_toLp.comp (contDiff_pi.mpr fun j ↦
        Complex.reCLM.contDiff.comp (contDiff_schwartzLatticePeriodization (b j)))
  let g := ContinuumRow.cutoffMultiplier (periodizedCutoff hr χ hχ hχs)
    (toTorus (𝕜 := ℝ) f)
  have hg : g = toTorus (𝕜 := ℝ) (realImageCutoffOperator χ hχ.continuous hχc f) :=
    (DFunLike.congr_fun (toTorus_realImageCutoffOperator hr χ hχ hχs) f).symm
  have hc (j : Fin d) : complexifiedL2Coordinate volume j
      (ContinuumRow.periodicBesselInverse g) = (W j).toLp 2 volume ℂ := by
    rw [complexifiedL2Coordinate_periodicBesselInverse, hg,
      complexifiedL2Coordinate_toTorus, cutoff_coordinate_eq_toLp χ hχ hχc v f hf,
      toTorus_schwartz_eq_periodization hr (u j) (hus j),
      complexPeriodicBesselOperator_eq_periodized_euclidean_on_schwartz]
    simp only [W, b, imageBesselSchwartzCLM_apply]
  have hae : ContinuumRow.periodicBesselInverse g =ᵐ[volume] w := by
    have hj (j : Fin d) : ∀ᵐ z ∂volume,
        ContinuumRow.periodicBesselInverse g z j = (W j z).re := by
      have he := complexifiedL2Coordinate_coe volume j (ContinuumRow.periodicBesselInverse g)
      rw [hc j] at he
      filter_upwards [he, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (W j)]
        with z hz hz'
      exact (congrArg Complex.re (hz.symm.trans hz')).trans rfl
    filter_upwards [ae_all_iff.mpr hj] with z hz
    exact PiLp.ext hz
  refine ⟨w, hw, ?_⟩
  apply PeriodicSobolevSpace.toL2_injective 1
  rw [ContinuumRow.toL2_periodicBesselLift]
  exact Lp.ext (hae.trans (PeriodicSobolevSpace.toL2_ofSmooth_ae 1 w hw).symm)

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison.BesselRepresentative
