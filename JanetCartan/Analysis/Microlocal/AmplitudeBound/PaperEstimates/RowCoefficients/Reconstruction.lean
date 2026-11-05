module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.RowCoefficients.Energy
public import JanetCartan.Analysis.Fourier.Periodic.Interpolation.Summation

/-!
# Reconstruction of the original finite-Sobolev row

The weighted coefficient energy in `app:ch_osc:eq:amplitude-row` gives absolute
Fourier summability when `d < 2s`.  Continuity of the original supported row
then identifies the series at every point, including the faces of the physical
cell.  The same fixed cutoff removes all periodic copies globally.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology
open JanetCartan.Pseudodifferential

namespace JanetCartan.AmplitudeBound.RowCoefficients

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A support gap suffices to periodize a continuous row continuously.  No
smooth approximation of the row is assumed in
`app:ch_osc:eq:amplitude-row`. -/
theorem continuous_amplitudePeriodization_of_supported {r : ℝ} (hr : r < 1 / 2)
    {f : E → ℂ} (hs : SupportedInCenteredBox r f) (hf : Continuous f) :
    Continuous (amplitudePeriodization f) := by
  have hd : Continuous (periodicLift (amplitudePeriodization f)) := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨y, hy, k, rfl⟩ := exists_mem_fundamentalCell_add_integerTranslation x
    have hlocal : ContinuousAt (periodicLift (amplitudePeriodization f)) y :=
      hf.continuousAt.congr_of_eventuallyEq
        (periodicLift_amplitudePeriodization_eventuallyEq hr hs hy)
    have hlocal' : ContinuousAt (periodicLift (amplitudePeriodization f))
        ((y + integerTranslation k) - integerTranslation k) := by
      simpa only [add_sub_cancel_right] using hlocal
    have hcomp := hlocal'.comp (f := fun z : E ↦ z - integerTranslation k)
      (continuousAt_id.sub continuousAt_const)
    convert hcomp using 1
    funext z
    exact (periodicLift_periodic (amplitudePeriodization f) k).sub_eq z |>.symm
  have hq : IsOpenQuotientMap (@torusQuotient d) :=
    (IsOpenQuotientMap.piMap (fun _ : Fin d ↦
      QuotientAddGroup.isOpenQuotientMap_mk)).comp
        (PiLp.homeomorph 2 (fun _ : Fin d ↦ ℝ)).isOpenQuotientMap
  exact hq.isQuotientMap.continuous_iff.mpr hd

/-- The original box-normalized row has summable complex Fourier
coefficients at the exact strict Sobolev threshold
(`app:ch_osc:eq:amplitude-row`). -/
theorem summable_actual_row_coefficients (R : ℝ) (s : ℕ) (hds : d < 2 * s)
    (f : E → ℂ) (hs : SupportedInCenteredBox R f) (hf : MemLp f 2 volume)
    (hHs : MemFourierSobolev (s : ℝ) (hf.toLp f)) :
    Summable (UnitAddTorus.mFourierCoeff
      (boxAmplitudePeriodization (amplitudeBoxScale R) f)) := by
  let β := UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization (amplitudeBoxScale R) f)
  have he := (actual_row_coefficient_energy R s f hs hf hHs).1
  have hw : Summable (fun k : Fin d → ℤ ↦ (1 + frequencyNorm k ^ 2) ^ (-(s : ℝ))) :=
    summable_besselWeight (by exact_mod_cast hds)
  have h := summable_and_tsum_le_sqrt_mul_sqrt
    (t := fun k ↦ ‖β k‖)
    (a := fun k ↦ (1 + frequencyNorm k ^ 2) ^ (-(s : ℝ)))
    (b := fun k ↦ (1 + frequencyNorm k ^ 2) ^ s * ‖β k‖ ^ 2)
    (fun _ ↦ norm_nonneg _) (fun _ ↦ by positivity) (fun _ ↦ by positivity)
    (fun k ↦ by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← mul_assoc,
        inv_mul_cancel₀ (by positivity), one_mul]) hw he
  exact h.1.of_norm

/-- The globally defined physical cutoff removes the periodic copies of the
same row, retaining the literal physical chart
(`app:ch_osc:eq:amplitude-row`). -/
theorem boxCellCutoff_boxAmplitudePeriodization_row_eq {L R : ℝ}
    (hL : 0 < L) (hR : R / L < 1 / 2) {f : E → ℂ}
    (hs : SupportedInCenteredBox R f) (x : E) :
    boxCellCutoff L x * boxAmplitudePeriodization L f (scaledTorusChart L x) = f x := by
  have hscaled := supportedInCenteredBox_comp_smul hL hs
  by_cases hx : L⁻¹ • x ∈ fundamentalCell d
  · rw [boxCellCutoff, physicalCellCutoff, Set.indicator_of_mem hx, one_mul]
    have he := periodicLift_amplitudePeriodization_eq hR hscaled hx
    simpa only [boxAmplitudePeriodization, scaledTorusChart, periodicLift,
      Function.comp_apply, smul_inv_smul₀ hL.ne'] using he
  · have hz : f x = 0 := by
      by_contra hn
      have hn' : f (L • (L⁻¹ • x)) ≠ 0 := by simpa only [smul_inv_smul₀ hL.ne'] using hn
      exact hx (fun i ↦ abs_le.mp ((hscaled _ hn' i).trans hR.le))
    simp only [boxCellCutoff, physicalCellCutoff, Set.indicator_of_notMem hx, zero_mul, hz]

/-- Absolute Fourier reconstruction on the original closed physical cell,
for the exact finite-Sobolev row in `app:ch_osc:eq:amplitude-row`. -/
theorem actual_row_fourier_hasSum_on_cell (R : ℝ) (s : ℕ) (hds : d < 2 * s)
    (f : E → ℂ) (hc : Continuous f) (hs : SupportedInCenteredBox R f)
    (hf : MemLp f 2 volume) (hHs : MemFourierSobolev (s : ℝ) (hf.toLp f))
    (x : E) (hx : (amplitudeBoxScale R)⁻¹ • x ∈ fundamentalCell d) :
    HasSum (fun k ↦
      UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization (amplitudeBoxScale R) f) k *
        UnitAddTorus.mFourier k (scaledTorusChart (amplitudeBoxScale R) x)) (f x) := by
  let L := amplitudeBoxScale R
  have hF : Continuous (boxAmplitudePeriodization L f) :=
    continuous_amplitudePeriodization_of_supported (div_amplitudeBoxScale_lt R)
      (supportedInCenteredBox_comp_smul (amplitudeBoxScale_pos R) hs)
      (hc.comp (continuous_const_smul L))
  let F : C(Torus d, ℂ) := ⟨boxAmplitudePeriodization L f, hF⟩
  have hsum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := F)
    (summable_actual_row_coefficients R s hds f hs hf hHs) (scaledTorusChart L x)
  have he : boxAmplitudePeriodization L f (scaledTorusChart L x) = f x := by
    have he' := periodicLift_amplitudePeriodization_eq (div_amplitudeBoxScale_lt R)
      (supportedInCenteredBox_comp_smul (amplitudeBoxScale_pos R) hs) hx
    simpa only [boxAmplitudePeriodization, scaledTorusChart, periodicLift,
      Function.comp_apply, smul_inv_smul₀ (amplitudeBoxScale_pos R).ne'] using he'
  simpa only [F, ContinuousMap.coe_mk, smul_eq_mul, he] using hsum

/-- The literal Fourier series with the original physical cutoff sums to the
row globally.  This is the reconstruction consumed by the row-kernel identity
in `app:ch_osc:eq:amplitude-row`. -/
theorem actual_row_fourier_hasSum_cutoff (R : ℝ) (s : ℕ) (hds : d < 2 * s)
    (f : E → ℂ) (hc : Continuous f) (hs : SupportedInCenteredBox R f)
    (hf : MemLp f 2 volume) (hHs : MemFourierSobolev (s : ℝ) (hf.toLp f)) (x : E) :
    HasSum (fun k ↦ boxCellCutoff (amplitudeBoxScale R) x *
      UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization (amplitudeBoxScale R) f) k *
        UnitAddTorus.mFourier k (scaledTorusChart (amplitudeBoxScale R) x)) (f x) := by
  let L := amplitudeBoxScale R
  have hF : Continuous (boxAmplitudePeriodization L f) :=
    continuous_amplitudePeriodization_of_supported (div_amplitudeBoxScale_lt R)
      (supportedInCenteredBox_comp_smul (amplitudeBoxScale_pos R) hs)
      (hc.comp (continuous_const_smul L))
  let F : C(Torus d, ℂ) := ⟨boxAmplitudePeriodization L f, hF⟩
  have hsum := (UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := F)
    (summable_actual_row_coefficients R s hds f hs hf hHs)
    (scaledTorusChart L x)).mul_left (boxCellCutoff L x)
  simpa only [F, ContinuousMap.coe_mk, smul_eq_mul, ← mul_assoc, L,
    boxCellCutoff_boxAmplitudePeriodization_row_eq (amplitudeBoxScale_pos R)
      (div_amplitudeBoxScale_lt R) hs] using hsum

end JanetCartan.AmplitudeBound.RowCoefficients
