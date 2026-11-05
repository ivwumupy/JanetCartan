module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.EuclideanKernel
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.LatticeRemainder
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.SchwartzComparison

/-!
# Identification of the local Bessel error with its kernel

The summable off-diagonal bound justifies exchanging the lattice sum and
Lebesgue input integral in `app:ch_background:prop:bg-frame`, Step 1.
This identifies the previously constructed Schwartz output tail with the
explicit heat-kernel remainder, without identifying the periodic kernel with
its zero translate.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped SchwartzMap ContDiff
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Absolute input-integral convergence permits summing the nonzero translates
before integrating (`app:ch_background:prop:bg-frame`, Step 1). The uniform
majorant is proved from the heat integral, rather than assumed. -/
theorem hasSum_integral_imageBesselLatticeTerm
    {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1 / 2)
    (f : E → ℂ) (hf : Integrable f) (hfs : SupportedInCenteredBox r f)
    (x : E) (hx : ∀ i, |x i| ≤ r) :
    HasSum (fun k : Fin d → ℤ ↦
      ∫ y : E, (imageBesselLatticeTerm k (x, y) : ℂ) * f y)
      (∫ y : E, (imageBesselLatticeRemainder x y : ℂ) * f y) := by
  classical
  obtain ⟨b, hb, hb₀, hbound⟩ :=
    exists_summable_imageBesselLatticeTerm_jet_majorant_on_cube hr₀ hr 0
  have hmajor (k : Fin d → ℤ) (y : E) :
      ‖(imageBesselLatticeTerm k (x, y) : ℂ) * f y‖ ≤ b k * ‖f y‖ := by
    by_cases hy : f y = 0
    · simp [hy]
    · rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [norm_iteratedFDeriv_zero] using hbound 0 le_rfl k (x, y) hx (hfs y hy))
        (norm_nonneg _)
  have hmeas (k : Fin d → ℤ) :
      AEStronglyMeasurable (fun y : E ↦ (imageBesselLatticeTerm k (x, y) : ℂ) * f y) := by
    by_cases hk : k = 0
    · simpa [imageBesselLatticeTerm, hk] using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : E ↦ (0 : ℂ)) volume)
    · have hK : Measurable (fun y : E ↦ imageBesselKernel (x - y + integerTranslation k)) :=
        measurable_imageBesselKernel.comp (by fun_prop)
      simpa only [imageBesselLatticeTerm, ite_eq_right hk, Pi.mul_apply] using
        hK.complex_ofReal.aestronglyMeasurable.fun_mul hf.aestronglyMeasurable
  apply hasSum_integral_of_dominated_convergence (fun k y ↦ b k * ‖f y‖) hmeas
    (fun k ↦ Filter.Eventually.of_forall (hmajor k))
    (Filter.Eventually.of_forall (fun y ↦ hb.mul_right ‖f y‖))
  · simpa only [tsum_mul_right] using hf.norm.const_mul (∑' k, b k)
  · filter_upwards [] with y
    by_cases hy : f y = 0
    · simp [hy]
    · have hp : (x, y) ∈ imageBesselComparisonDomain d :=
        ⟨fun i ↦ (hx i).trans_lt hr, fun i ↦ (hfs y hy i).trans_lt hr⟩
      exact (Complex.hasSum_ofReal.mpr (summable_imageBesselLatticeTerm hp).hasSum).mul_right (f y)

/-- On the comparison cube the Schwartz output tail is the literal integral
against the nonzero lattice remainder (`app:ch_background:prop:bg-frame`,
Step 1). This is the analytic identification used by the localized operator. -/
theorem imageBesselSchwartzTail_eq_integral
    {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1 / 2)
    (u : 𝓢(E, ℂ)) (hu : SupportedInCenteredBox r u)
    (x : E) (hx : ∀ i, |x i| ≤ r) :
    imageBesselSchwartzTail u x =
      ∫ y : E, (imageBesselLatticeRemainder x y : ℂ) * u y := by
  classical
  rw [← (hasSum_integral_imageBesselLatticeTerm hr₀ hr u u.integrable hu x hx).tsum_eq]
  apply tsum_congr
  intro k
  by_cases hk : k = 0
  · simp [imageBesselLatticeTerm, hk]
  · simp only [ite_eq_right hk, imageBesselLatticeTerm]
    rw [imageBesselMultiplier_eq_convolution]
    congr 1
    funext y
    congr 2
    abel

/-- With both masks retained, the Schwartz comparison error is integration
against the explicitly constructed compact kernel
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem localized_imageBesselSchwartzTail_eq_integral
    {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1 / 2)
    (χ ψ : E → ℝ) (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (u v : 𝓢(E, ℂ)) (hv : ∀ y, v y = (ψ y : ℂ) * u y)
    (hvs : SupportedInCenteredBox r v) (x : E) :
    (χ x : ℂ) * imageBesselSchwartzTail v x =
      ∫ y : E, (localizedImageBesselRemainder χ ψ x y : ℂ) * u y := by
  by_cases hx : χ x = 0
  · simp [hx, localizedImageBesselRemainder]
  · rw [imageBesselSchwartzTail_eq_integral hr₀ hr v hvs x (hχs x hx),
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [hv, localizedImageBesselRemainder, Complex.ofReal_mul]
    ring

/-- The actual periodic multiplier on a masked Schwartz input equals the
localized Euclidean multiplier plus the explicit smooth kernel integral
(`app:ch_background:prop:bg-frame`, Step 1). The only operator premise is
the permitted lattice Fourier action. The source mask is constructed using
`SchwartzMap.smulLeftCLM`, so no masked-input identity is assumed. -/
theorem periodicBessel_localized_schwartz_eq_add_kernel
    (J : PeriodicL2 d ℂ →L[ℂ] PeriodicL2 d ℂ)
    (hJ : ∀ (v : PeriodicL2 d ℂ) (k : Fin d → ℤ),
      UnitAddTorus.mFourierCoeff (J v) k =
        (ContinuumRow.periodicBesselSymbol k : ℂ) * UnitAddTorus.mFourierCoeff v k)
    {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1 / 2)
    (χ ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r) (u : 𝓢(E, ℂ)) :
    let v := SchwartzMap.smulLeftCLM ℂ (fun y ↦ (ψ y : ℂ)) u
    (fun z ↦ (χ (centeredTorusRepresentative z) : ℂ) *
      J (PeriodicLocalL2.toTorus (𝕜 := ℂ) (v.toLp 2)) z) =ᵐ[volume]
      fun z ↦ (χ (centeredTorusRepresentative z) : ℂ) *
        schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) v
          (centeredTorusRepresentative z) +
        ∫ y : E, (localizedImageBesselRemainder χ ψ
          (centeredTorusRepresentative z) y : ℂ) * u y := by
  let v := SchwartzMap.smulLeftCLM ℂ (fun y ↦ (ψ y : ℂ)) u
  have hψt : (fun y ↦ (ψ y : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp
      ((hasCompactSupport_of_imageBessel_cube_support ψ hψs).hasTemperateGrowth hψ)
  have hv (y : E) : v y = (ψ y : ℂ) * u y :=
    SchwartzMap.smulLeftCLM_apply_apply hψt u y
  have hvs : SupportedInCenteredBox r v := by
    intro y hy
    apply hψs y
    intro hz
    exact hy (by simp [hv, hz])
  filter_upwards [periodicBessel_chart_schwartz_eq_add_tail J hJ hr v hvs] with z hz
  change (χ (centeredTorusRepresentative z) : ℂ) *
    J (PeriodicLocalL2.toTorus (𝕜 := ℂ) (v.toLp 2)) z = _
  rw [hz, mul_add, localized_imageBesselSchwartzTail_eq_integral
    hr₀ hr χ ψ hχs u v hv hvs]

end JanetCartan.ContinuumNormalReduction.ImageNormal
