module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.KernelAction
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.RemainderOperator
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.BoundedMultiplier
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.Freezing.AllData.Multipliers
/-!
# Bounded local periodic–Euclidean Bessel comparison

The kernel identity extends by Schwartz density to the full Lebesgue L² space.
The two cell maps retain normalized torus volume separately from Lebesgue measure.
This closes the bounded scalar assembly for `app:ch_background:prop:bg-frame`,
Step 1; `RealAssembly` instantiates it with the actual real periodic inverse.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped SchwartzMap ContDiff
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound JanetCartan.ContinuumNormal
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
variable {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1 / 2) (χ ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r)
local notation "Mχ" => freezingPhysicalMultiplier (d := d) χ hχ.continuous
  (hasCompactSupport_of_imageBessel_cube_support χ hχs)
local notation "Mψ" => freezingPhysicalMultiplier (d := d) ψ hψ.continuous
  (hasCompactSupport_of_imageBessel_cube_support ψ hψs)
local notation "R" => localizedImageBesselRemainderOperator hr χ ψ hχ hψ hχs hψs

include hr₀ in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 300000 in
/-- The localized chart identity on Schwartz L² classes, with the actual
Lebesgue restriction and zero extension (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem periodicBessel_localized_L2_schwartz_eq_add_remainder
    (J : PeriodicL2 d ℂ →L[ℂ] PeriodicL2 d ℂ)
    (hJ : ∀ (v : PeriodicL2 d ℂ) (k : Fin d → ℤ),
      UnitAddTorus.mFourierCoeff (J v) k =
        (ContinuumRow.periodicBesselSymbol k : ℂ) * UnitAddTorus.mFourierCoeff v k)
    (u : 𝓢(E, ℂ)) :
    Mχ (PeriodicLocalL2.toEuclidean (n := d) (𝕜 := ℂ) (F := ℂ)
      (J (PeriodicLocalL2.toTorus (n := d) (𝕜 := ℂ) (F := ℂ) (Mψ (u.toLp 2 volume))))) =
      Mχ (imageBesselL2Operator (Mψ (u.toLp 2 volume))) + R (u.toLp 2 volume) := by
  let v := SchwartzMap.smulLeftCLM ℂ (fun y ↦ (ψ y : ℂ)) u
  have hψt : (fun y ↦ (ψ y : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp
      ((hasCompactSupport_of_imageBessel_cube_support ψ hψs).hasTemperateGrowth hψ)
  have hv (y : E) : v y = (ψ y : ℂ) * u y :=
    SchwartzMap.smulLeftCLM_apply_apply hψt u y
  have hvs : SupportedInCenteredBox r v := by
    intro y hy
    apply hψs y
    intro hzero
    exact hy (by simp [hv, hzero])
  have hMv : Mψ (u.toLp 2 volume) = v.toLp 2 := by
    apply Lp.ext
    filter_upwards [freezingPhysicalMultiplier_coeFn (d := d) ψ hψ.continuous
      (hasCompactSupport_of_imageBessel_cube_support ψ hψs) (u.toLp 2 volume),
      u.coeFn_toLp 2 volume, v.coeFn_toLp 2 volume] with y hy hu' hv'
    rw [hy, hu', hv', hv, Complex.real_smul]
  rw [hMv, imageBesselL2Operator_toLp]
  let w := schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) v
  let jv := J (PeriodicLocalL2.toTorus (n := d) (𝕜 := ℂ) (F := ℂ) (v.toLp 2 volume))
  have hj := periodicBessel_chart_schwartz_eq_add_tail J hJ hr v hvs
  have hjlift := (ae_restrict_iff' PeriodicLocalL2.measurableSet_halfOpenCell).mp
    (PeriodicLocalL2.measurePreserving_quotient.quasiMeasurePreserving.ae_eq_comp hj)
  have hR : R (u.toLp 2 volume) =ᵐ[volume] fun x ↦
      ∫ y : E, (localizedImageBesselRemainder χ ψ x y : ℂ) * u y := by
    filter_upwards [localizedImageBesselRemainderOperator_ae_integral
      hr χ ψ hχ hψ hχs hψs (u.toLp 2 volume)] with x hx
    rw [hx]
    apply integral_congr_ae
    filter_upwards [u.coeFn_toLp 2] with y hy
    rw [hy]
  change Mχ (PeriodicLocalL2.toEuclidean (n := d) (𝕜 := ℂ) (F := ℂ) jv) =
    Mχ (w.toLp 2 volume) + R (u.toLp 2 volume)
  have hleft := freezingPhysicalMultiplier_coeFn (d := d) χ hχ.continuous
    (hasCompactSupport_of_imageBessel_cube_support χ hχs)
    (PeriodicLocalL2.toEuclidean (n := d) (𝕜 := ℂ) (F := ℂ) jv)
  have hlift := PeriodicLocalL2.toEuclidean_coe (𝕜 := ℂ) jv
  have hright := freezingPhysicalMultiplier_coeFn (d := d) χ hχ.continuous
    (hasCompactSupport_of_imageBessel_cube_support χ hχs) (w.toLp 2 volume)
  have hw := w.coeFn_toLp 2 volume
  have hadd := Lp.coeFn_add (Mχ (w.toLp 2 volume)) (R (u.toLp 2 volume))
  apply Lp.ext
  filter_upwards [hleft, hlift, hright, hw, hR, hjlift, hadd]
    with x hleft hlift hright hw hrem hjx hadd
  rw [hadd, Pi.add_apply, hleft, hright, hw, hrem]
  simp only [Complex.real_smul]
  by_cases hx : χ x = 0
  · simp [hx, localizedImageBesselRemainder]
  · have hcell : x ∈ PeriodicLocalL2.halfOpenCell d := by
      intro i
      have hi := abs_le.mp (hχs x hx i)
      exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
    have hjx' := hjx hcell
    simp only [Function.comp_apply,
      PeriodicLocalL2.centeredTorusRepresentative_quotient hcell] at hjx'
    rw [hlift, Set.indicator_of_mem hcell]
    change (χ x : ℂ) * jv (torusQuotient x) = _
    rw [hjx', mul_add, localized_imageBesselSchwartzTail_eq_integral
      hr₀ hr χ ψ hχs u v hv hvs x]

include hr₀ in
/-- The bounded periodic operator equals its Euclidean multiplier plus the
explicit smooth lattice remainder (`app:ch_background:prop:bg-frame`, Step 1).
Only the lattice Fourier action is assumed; Schwartz density gives all L² inputs. -/
 theorem periodicBessel_localized_L2_eq_add_remainder
    (J : PeriodicL2 d ℂ →L[ℂ] PeriodicL2 d ℂ)
    (hJ : ∀ (v : PeriodicL2 d ℂ) (k : Fin d → ℤ),
      UnitAddTorus.mFourierCoeff (J v) k =
        (ContinuumRow.periodicBesselSymbol k : ℂ) * UnitAddTorus.mFourierCoeff v k) :
    Mχ ∘L (PeriodicLocalL2.toEuclidean (n := d) (𝕜 := ℂ) (F := ℂ)).toContinuousLinearMap ∘L J ∘L
      PeriodicLocalL2.toTorus (n := d) (𝕜 := ℂ) (F := ℂ) ∘L Mψ =
        Mχ ∘L imageBesselL2Operator ∘L Mψ + R := by
  apply DFunLike.coe_injective
  apply (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2)
    (by norm_num)).equalizer
    (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext u
  exact periodicBessel_localized_L2_schwartz_eq_add_remainder hr₀ hr χ ψ hχ hψ hχs hψs J hJ u

end JanetCartan.ContinuumNormalReduction.ImageNormal
