module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Scalar transport on a characteristic

For `app:ch_waves:thm:leading` and `app:ch_background:prop:bg-positive`, solve
`u' + c u = 0` by the positive multiplier `exp (-∫ c)`. The coefficient here
is already pulled back to a given characteristic. No characteristic existence
or parameter regularity is assumed as a conclusion of this module.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace JanetCartan

/-- `app:ch_waves:thm:leading`: positive characteristic multiplier, independent
of the initial amplitude. The integral is oriented, so negative times are allowed. -/
def transportFactor (c : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  Real.exp (-(∫ s in t₀..t, c s))

/-- `app:ch_waves:thm:leading`: scalar solution with initial value `r` at `t₀`. -/
def scalarTransport (c : ℝ → ℝ) (t₀ r t : ℝ) : ℝ :=
  transportFactor c t₀ t * r

/-- `app:ch_waves:thm:leading`: the characteristic multiplier starts at one. -/
@[simp] theorem transportFactor_initial (c : ℝ → ℝ) (t₀ : ℝ) :
    transportFactor c t₀ t₀ = 1 := by simp [transportFactor]

/-- `app:ch_waves:thm:leading`: the prescribed initial value is attained. -/
@[simp] theorem scalarTransport_initial (c : ℝ → ℝ) (t₀ r : ℝ) :
    scalarTransport c t₀ r t₀ = r := by simp [scalarTransport]

/-- `app:ch_waves:thm:leading`: the flow exponential is strictly positive. -/
theorem transportFactor_pos (c : ℝ → ℝ) (t₀ t : ℝ) :
    0 < transportFactor c t₀ t := Real.exp_pos _

/-- `app:ch_background:prop:bg-positive`: positive initial amplitudes stay positive. -/
theorem scalarTransport_pos (c : ℝ → ℝ) (t₀ t : ℝ) {r : ℝ} (hr : 0 < r) :
    0 < scalarTransport c t₀ r t := mul_pos (transportFactor_pos _ _ _) hr

/-- `app:ch_waves:thm:leading`: additivity in the initial datum. -/
theorem scalarTransport_add (c : ℝ → ℝ) (t₀ r q t : ℝ) :
    scalarTransport c t₀ (r + q) t =
      scalarTransport c t₀ r t + scalarTransport c t₀ q t := mul_add _ _ _

/-- `app:ch_waves:thm:leading`: homogeneity in the initial datum. -/
theorem scalarTransport_smul (c : ℝ → ℝ) (t₀ k r t : ℝ) :
    scalarTransport c t₀ (k * r) t = k * scalarTransport c t₀ r t := by
  simp only [scalarTransport]; ring

/-- `app:ch_waves:thm:leading`: the solution operator is linear in its initial value. -/
def scalarTransportLinearMap (c : ℝ → ℝ) (t₀ : ℝ) : ℝ →ₗ[ℝ] (ℝ → ℝ) where
  toFun r := scalarTransport c t₀ r
  map_add' r q := funext (scalarTransport_add c t₀ r q)
  map_smul' k r := funext (scalarTransport_smul c t₀ k r)

/-- `app:ch_waves:thm:leading`: squared amplitudes depend linearly on initial densities. -/
theorem scalarTransport_sq (c : ℝ → ℝ) (t₀ r t : ℝ) :
    scalarTransport c t₀ r t ^ 2 = transportFactor c t₀ t ^ 2 * r ^ 2 :=
  mul_pow _ _ _

/-- `app:ch_waves:thm:leading`: FTC on any open time interval containing `t₀`. -/
theorem hasDerivAt_transportIntegral {c : ℝ → ℝ} {I : Set ℝ} {t₀ t : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hc : ContinuousOn c I)
    (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    HasDerivAt (fun τ ↦ ∫ s in t₀..τ, c s) (c t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.mono (hIc.uIcc_subset ht₀ ht)).intervalIntegrable
    (hc.stronglyMeasurableAtFilter hI t ht)
    ((hc t ht).continuousAt (hI.mem_nhds ht))

/-- `app:ch_waves:thm:leading`: the exponential solves the homogeneous scalar ODE. -/
theorem hasDerivAt_transportFactor {c : ℝ → ℝ} {I : Set ℝ} {t₀ t : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hc : ContinuousOn c I)
    (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    HasDerivAt (transportFactor c t₀) (-c t * transportFactor c t₀ t) t := by
  exact ((hasDerivAt_transportIntegral hI hIc hc ht₀ ht).neg.exp).congr_deriv
    (by dsimp [transportFactor]; ring)

/-- `app:ch_waves:thm:leading`: the actual solution satisfies `u' = -c u`. -/
theorem hasDerivAt_scalarTransport {c : ℝ → ℝ} {I : Set ℝ} {t₀ t : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hc : ContinuousOn c I)
    (ht₀ : t₀ ∈ I) (ht : t ∈ I) (r : ℝ) :
    HasDerivAt (scalarTransport c t₀ r) (-c t * scalarTransport c t₀ r t) t := by
  exact ((hasDerivAt_transportFactor hI hIc hc ht₀ ht).mul_const r).congr_deriv
    (by dsimp [scalarTransport]; ring)

/-- `app:ch_waves:thm:leading`: uniqueness on the entire given open time interval,
proved with an integrating factor, with no boundedness hypothesis on `c`. -/
theorem scalarTransport_unique {c u : ℝ → ℝ} {I : Set ℝ} {t₀ r : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hc : ContinuousOn c I)
    (ht₀ : t₀ ∈ I) (hu : ∀ t ∈ I, HasDerivAt u (-c t * u t) t)
    (hu₀ : u t₀ = r) : EqOn u (scalarTransport c t₀ r) I := by
  let v : ℝ → ℝ := fun t ↦ Real.exp (∫ s in t₀..t, c s) * u t
  have hv (t) (ht : t ∈ I) : HasDerivAt v 0 t := by
    convert ((hasDerivAt_transportIntegral hI hIc hc ht₀ ht).exp.mul (hu t ht))
      using 1; ring
  intro t ht
  have he : v t = v t₀ := hI.is_const_of_deriv_eq_zero hIc.isPreconnected
    (fun s hs ↦ (hv s hs).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hv s hs).deriv) ht ht₀
  have he' : Real.exp (∫ s in t₀..t, c s) * u t = r := by
    simpa [v, hu₀] using he
  have hcancel : transportFactor c t₀ t * Real.exp (∫ s in t₀..t, c s) = 1 := by
    rw [transportFactor, ← Real.exp_add]; simp
  calc
    u t = transportFactor c t₀ t *
        (Real.exp (∫ s in t₀..t, c s) * u t) := by rw [← mul_assoc, hcancel, one_mul]
    _ = scalarTransport c t₀ r t := by rw [he']; rfl

/-- `app:ch_waves:thm:leading`: a coefficient bound gives a uniform positive
lower bound on every fixed time box, retaining the initial lower bound `m`. -/
theorem scalarTransport_lower_bound {c : ℝ → ℝ} {t₀ t K T m r : ℝ}
    (hK : 0 ≤ K) (hm : 0 ≤ m) (hr : m ≤ r) (ht : |t - t₀| ≤ T)
    (hc : ∀ s ∈ uIoc t₀ t, |c s| ≤ K) :
    m * Real.exp (-K * T) ≤ scalarTransport c t₀ r t := by
  have hint : |∫ s in t₀..t, c s| ≤ K * T := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun s hs ↦ show ‖c s‖ ≤ K by simpa only [Real.norm_eq_abs] using hc s hs)
    have h' : |∫ s in t₀..t, c s| ≤ K * |t - t₀| := by
      simpa only [Real.norm_eq_abs] using h
    exact h'.trans (mul_le_mul_of_nonneg_left ht hK)
  have hexp : Real.exp (-K * T) ≤ transportFactor c t₀ t := by
    apply Real.exp_le_exp.mpr
    have := (le_abs_self (∫ s in t₀..t, c s)).trans hint
    linarith
  calc
    m * Real.exp (-K * T) ≤ m * transportFactor c t₀ t :=
      mul_le_mul_of_nonneg_left hexp hm
    _ ≤ r * transportFactor c t₀ t :=
      mul_le_mul_of_nonneg_right hr (transportFactor_pos _ _ _).le
    _ = scalarTransport c t₀ r t := mul_comm _ _

end JanetCartan
