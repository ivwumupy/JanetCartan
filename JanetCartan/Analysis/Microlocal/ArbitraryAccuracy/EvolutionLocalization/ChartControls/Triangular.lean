module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.CanonicalMap
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Coordinates
public import JanetCartan.Analysis.Calculus.BufferedInverse

/-!
# Quantitative triangular estimates for the elapsed charts

The temporal shear in `app:ch_regular:eq:joint-stationary` need not be small.
The estimates retain its derivative budget explicitly. The consumer is the
inverse field of both chart controls for `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
variable {d : ℕ}

/-- Coordinate norm estimate used for the full elapsed covector, including
arbitrary temporal components (`app:ch_regular:lem:finite-chain`). -/
theorem norm_timeSpacePoint_le (t : ℝ) (y : Euclidean d) :
    ‖timeSpacePoint t y‖ ≤ |t| + ‖y‖ := by
  simpa using norm_le_time_add_spatial (timeSpacePoint t y)

/-- Subtraction in the actual physical time/space coordinates
(`app:ch_regular:eq:joint-stationary`). -/
theorem timeSpacePoint_sub (t s : ℝ) (y z : Euclidean d) :
    timeSpacePoint t y - timeSpacePoint s z = timeSpacePoint (t-s) (y-z) :=
  (timeSpacePointCLM.map_sub (t,y) (s,z)).symm

private theorem spatial_sub_le (x y : Euclidean (d+1)) :
    ‖spatialPart x - spatialPart y‖ ≤ ‖x-y‖ := by
  simpa only [← spatialPartCLM_apply, ← map_sub] using norm_spatialPart_le (x-y)

private theorem time_sub_le (x y : Euclidean (d+1)) : |x 0-y 0| ≤ ‖x-y‖ :=
  PiLp.norm_apply_le (x-y) 0

/-- The spatial mixed half-gap gives a quantitative difference estimate;
this is a deduction from the original mixed derivative, not an assumed
elapsed inverse bound (`app:ch_regular:eq:joint-stationary`). -/
theorem spatial_difference_le_of_mixed_gap {F : Euclidean d → Euclidean d}
    {D : Set (Euclidean d)} (hc : Convex ℝ D)
    (hd : ∀ η ∈ D, DifferentiableAt ℝ F η)
    (hg : ∀ η ∈ D, ‖fderiv ℝ F η - ContinuousLinearMap.id ℝ _‖ ≤ 1/2)
    {η ζ : Euclidean d} (hη : η ∈ D) (hζ : ζ ∈ D) :
    ‖η-ζ‖ ≤ 2 * ‖F η-F ζ‖ := by
  have hh := normalized_lower_lipschitz_of_derivative_gap hc
    (ContinuousLinearEquiv.refl ℝ (Euclidean d)) hd (by simpa using hg) hη hζ
  change ‖η-ζ‖ / 2 ≤ ‖F η-F ζ‖ at hh
  linarith

/-- The reverse triangular chart has inverse constant `3+2L`, including
its temporal shear. Only the spatial mixed half-gap and the derivative
of the original simultaneous-time term are inputs. Consumer: the reverse
chart's `inverse_bound` (`app:ch_regular:lem:finite-chain`). -/
theorem triangular_covector_inverse_bound
    {F : Euclidean d → Euclidean d} {a : Euclidean d → ℝ}
    {D : Set (Euclidean d)} (hc : Convex ℝ D) {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ η ∈ D, DifferentiableAt ℝ F η)
    (hg : ∀ η ∈ D, ‖fderiv ℝ F η - ContinuousLinearMap.id ℝ _‖ ≤ 1/2)
    (ha : ∀ η ∈ D, DifferentiableAt ℝ a η)
    (hb : ∀ η ∈ D, ‖fderiv ℝ a η‖ ≤ L)
    {ξ ζ : Euclidean (d+1)} (hξ : spatialPart ξ ∈ D) (hζ : spatialPart ζ ∈ D) :
    ‖ξ-ζ‖ ≤ (3+2*L) *
      ‖timeSpacePoint (ξ 0+a (spatialPart ξ)) (F (spatialPart ξ)) -
        timeSpacePoint (ζ 0+a (spatialPart ζ)) (F (spatialPart ζ))‖ := by
  let v := timeSpacePoint (ξ 0+a (spatialPart ξ)) (F (spatialPart ξ)) -
    timeSpacePoint (ζ 0+a (spatialPart ζ)) (F (spatialPart ζ))
  have hs : ‖spatialPart ξ-spatialPart ζ‖ ≤ 2*‖v‖ := by
    have hh := spatial_difference_le_of_mixed_gap hc hd hg hξ hζ
    have hp : ‖F (spatialPart ξ)-F (spatialPart ζ)‖ ≤ ‖v‖ := by
      simpa only [spatialPart_timeSpacePoint] using spatial_sub_le
        (timeSpacePoint (ξ 0+a (spatialPart ξ)) (F (spatialPart ξ)))
        (timeSpacePoint (ζ 0+a (spatialPart ζ)) (F (spatialPart ζ)))
    linarith
  have ht : |ξ 0-ζ 0| ≤ ‖v‖ + L * ‖spatialPart ξ-spatialPart ζ‖ := by
    have he := norm_sub_le ((ξ 0+a (spatialPart ξ))-(ζ 0+a (spatialPart ζ)))
      (a (spatialPart ξ)-a (spatialPart ζ))
    have ha' := Convex.norm_image_sub_le_of_norm_fderiv_le ha hb hc hζ hξ
    have hp : |(ξ 0+a (spatialPart ξ))-(ζ 0+a (spatialPart ζ))| ≤ ‖v‖ := by
      simpa only [timeSpacePoint_time] using time_sub_le
        (timeSpacePoint (ξ 0+a (spatialPart ξ)) (F (spatialPart ξ)))
        (timeSpacePoint (ζ 0+a (spatialPart ζ)) (F (spatialPart ζ)))
    have eq : (ξ 0+a (spatialPart ξ)-(ζ 0+a (spatialPart ζ))) -
        (a (spatialPart ξ)-a (spatialPart ζ)) = ξ 0-ζ 0 := by ring
    rw [eq] at he
    exact he.trans (add_le_add hp ha')
  have hn : ‖ξ-ζ‖ ≤ |ξ 0-ζ 0| + ‖spatialPart ξ-spatialPart ζ‖ := by
    simpa only [← spatialPartCLM_apply, map_sub, PiLp.sub_apply] using norm_le_time_add_spatial (ξ-ζ)
  change ‖ξ-ζ‖ ≤ (3+2*L)*‖v‖
  nlinarith [mul_le_mul_of_nonneg_left hs hL]

/-- The forward triangular chart has the same constant. The time-variable
variation is derived from the original first-jet budget on a rectangular
convex buffer, while the spatial mixed block supplies the half-gap.
Consumer: the forward chart's `inverse_bound`
(`app:ch_regular:eq:joint-stationary`). -/
theorem triangular_base_inverse_bound
    {F : ℝ → Euclidean d → Euclidean d}
    {T : Set ℝ} {Y : Set (Euclidean d)} (hT : Convex ℝ T) (hY : Convex ℝ Y)
    {L r : ℝ} (hL : 0 ≤ L)
    (hd : ∀ t ∈ T, ∀ y ∈ Y, DifferentiableAt ℝ (F t) y)
    (hg : ∀ t ∈ T, ∀ y ∈ Y,
      ‖fderiv ℝ (F t) y - ContinuousLinearMap.id ℝ _‖ ≤ 1/2)
    (ht : ∀ y ∈ Y, ∀ t ∈ T, DifferentiableAt ℝ (fun s => F s y) t)
    (hb : ∀ y ∈ Y, ∀ t ∈ T, ‖fderiv ℝ (fun s => F s y) t‖ ≤ L)
    {x z : Euclidean (d+1)} (hx : x 0 ∈ T ∧ spatialPart x ∈ Y)
    (hz : z 0 ∈ T ∧ spatialPart z ∈ Y) :
    ‖x-z‖ ≤ (3+2*L) *
      ‖timeSpacePoint (x 0-r) (F (x 0) (spatialPart x)) -
        timeSpacePoint (z 0-r) (F (z 0) (spatialPart z))‖ := by
  let v := timeSpacePoint (x 0-r) (F (x 0) (spatialPart x)) -
    timeSpacePoint (z 0-r) (F (z 0) (spatialPart z))
  have hp : ‖F (x 0) (spatialPart x)-F (z 0) (spatialPart z)‖ ≤ ‖v‖ := by
    simpa only [spatialPart_timeSpacePoint] using spatial_sub_le
      (timeSpacePoint (x 0-r) (F (x 0) (spatialPart x)))
      (timeSpacePoint (z 0-r) (F (z 0) (spatialPart z)))
  have htime : |x 0-z 0| ≤ ‖v‖ := by
    have hh := time_sub_le (timeSpacePoint (x 0-r) (F (x 0) (spatialPart x)))
      (timeSpacePoint (z 0-r) (F (z 0) (spatialPart z)))
    simpa only [timeSpacePoint_time, sub_sub_sub_cancel_right] using hh
  have hs := spatial_difference_le_of_mixed_gap hY (hd (x 0) hx.1)
    (hg (x 0) hx.1) hx.2 hz.2
  have he := norm_sub_le_norm_sub_add_norm_sub (F (x 0) (spatialPart x))
    (F (z 0) (spatialPart z)) (F (x 0) (spatialPart z))
  have hv := Convex.norm_image_sub_le_of_norm_fderiv_le
    (ht _ hz.2) (hb _ hz.2) hT hx.1 hz.1
  rw [norm_sub_rev (z 0) (x 0), Real.norm_eq_abs] at hv
  have hn : ‖x-z‖ ≤ |x 0-z 0| + ‖spatialPart x-spatialPart z‖ := by
    simpa only [← spatialPartCLM_apply, map_sub, PiLp.sub_apply] using norm_le_time_add_spatial (x-z)
  change ‖x-z‖ ≤ (3+2*L)*‖v‖
  nlinarith [mul_le_mul_of_nonneg_left htime hL]

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization
