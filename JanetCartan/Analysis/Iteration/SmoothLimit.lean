module

public import JanetCartan.Analysis.Iteration.SmoothLimit.Periodic
public import JanetCartan.Analysis.Iteration.SmoothLimit.Rescaling
public import JanetCartan.Geometry.IsometricEmbedding.Scales

/-!
# The limiting metric equation

The final limiting argument of Section 9. From the periodic increment estimate
`main:eq:final-Cr` and stage metric errors, obtain one smooth isometric limit
on a fixed neighborhood and undo the fixed target dilation. These results do
not construct the increments or prove the input Fourier estimate.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius
open Filter

namespace JanetCartan

/-- Section 9 after `main:eq:final-Cr`: convergence of first jets implies convergence
of each coordinate derivative. -/
theorem tendsto_partialDeriv_of_tendsto_iteratedFDeriv_one {n N : ℕ}
    {M : ℕ → Euclidean n → Euclidean N} {F : Euclidean n → Euclidean N}
    {x : Euclidean n}
    (h : Tendsto (fun j ↦ iteratedFDeriv ℝ 1 (M j) x) atTop
      (𝓝 (iteratedFDeriv ℝ 1 F x))) (i : Fin n) :
    Tendsto (fun j ↦ partialDeriv (M j) x i) atTop (𝓝 (partialDeriv F x i)) := by
  simpa only [Function.comp_def, iteratedFDeriv_one_apply, partialDeriv] using
    (continuous_eval_const (fun _ : Fin 1 ↦ EuclideanSpace.single i (1 : ℝ))).tendsto
      (iteratedFDeriv ℝ 1 F x) |>.comp h

/-- Section 9 after `main:eq:final-Cr`: first derivative convergence passes the
induced metric to the limit when the stage metrics tend to the target. -/
theorem inducedMetric_eq_of_tendsto {n N : ℕ}
    {M : ℕ → Euclidean n → Euclidean N} {F : Euclidean n → Euclidean N}
    {g : MetricField n} {s : Set (Euclidean n)}
    (hderiv : ∀ x ∈ s, ∀ i, Tendsto (fun j ↦ partialDeriv (M j) x i) atTop
      (𝓝 (partialDeriv F x i)))
    (hmetric : ∀ x ∈ s, Tendsto (fun j ↦ inducedMetric (M j) x) atTop (𝓝 (g x))) :
    IsIsometricOn g F s := by
  intro x hx
  ext i k
  exact tendsto_nhds_unique ((hderiv x hx i).inner (hderiv x hx k))
    ((tendsto_pi_nhds.1 (tendsto_pi_nhds.1 (hmetric x hx) i)) k)

/-- Section 9, `main:eq:metric-induction` and `main:eq:final-Cr`: eventual summable
derivative bounds and a vanishing Frobenius metric error imply the limiting metric equation. -/
theorem isIsometricOn_series_of_metric_error {n N : ℕ}
    {G : Euclidean n → Euclidean N} {f : ℕ → Euclidean n → Euclidean N}
    {v : ℕ → ℕ → ℝ} {g : MetricField n} {s : Set (Euclidean n)} {ε : ℕ → ℝ}
    (hG : ContDiff ℝ ∞ G) (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (hv : ∀ r, Summable (v r))
    (hb : ∀ r, ∀ᶠ j in atTop, ∀ x, ‖iteratedFDeriv ℝ r (f j) x‖ ≤ v r j)
    (hε : Tendsto ε atTop (𝓝 0))
    (herror : ∀ J, ∀ x ∈ s,
      ‖inducedMetric (fun y ↦ G y + ∑ j ∈ Finset.range J, f j y) x - g x‖ ≤ ε J) :
    IsIsometricOn g (fun x ↦ G x + ∑' j, f j x) s := by
  apply inducedMetric_eq_of_tendsto
    (M := fun J x ↦ G x + ∑ j ∈ Finset.range J, f j x)
  · intro x _ i
    exact tendsto_partialDeriv_of_tendsto_iteratedFDeriv_one
      (((smooth_limit_of_eventual_bounds hG hf hv hb).2 1).tendsto_at x) i
  · intro x hx
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun J ↦ norm_nonneg _) (fun J ↦ herror J x hx) hε

/-- Section 9, `main:eq:final-Cr` and `main:eq:metric-induction`: the periodic
increment estimate and the stage defect bound give one smooth isometric limit
on the fixed open neighborhood. The construction of these increments remains an input. -/
theorem smooth_isometric_limit_of_periodic_bounds {n N : ℕ}
    {G : Euclidean n → Euclidean N} {f : ℕ → Torus n → Euclidean N}
    {W : Set (Euclidean n)} {g : MetricField n} {R : ℕ → ℝ} {k : ℕ → ℕ}
    {C b : ℕ → ℝ} (hW : IsOpen W) (hG : ContDiffOn ℝ ∞ G W)
    (hf : ∀ j, IsSmoothPeriodic (f j)) (hR : ∀ j, 1 ≤ R j)
    (hRsum : Summable (fun j ↦ (R j)⁻¹)) (hk : Tendsto k atTop atTop)
    (hCr : ∀ r, ∀ᶠ j in atTop, cNorm (fundamentalCell n) r (periodicLift (f j)) ≤
      C r * (R j) ^ (-(k j : ℝ) + b r))
    (herror : ∀ J, ∀ x ∈ W,
      ‖inducedMetric (fun y ↦ G y + ∑ j ∈ Finset.range J, periodicLift (f j) y) x - g x‖ ≤
        ((R J) ^ (-(k J : ℝ))) ^ 2) :
    ContDiffOn ℝ ∞ (fun x ↦ G x + ∑' j, periodicLift (f j) x) W ∧
      (∀ r : ℕ, TendstoUniformlyOn
        (fun J ↦ iteratedFDeriv ℝ r
          (fun x ↦ G x + ∑ j ∈ Finset.range J, periodicLift (f j) x))
        (iteratedFDeriv ℝ r (fun x ↦ G x + ∑' j, periodicLift (f j) x)) atTop W) ∧
      IsIsometricOn g (fun x ↦ G x + ∑' j, periodicLift (f j) x) W := by
  obtain ⟨hsmooth, hconv⟩ := smooth_periodic_limit_of_power_bounds hW hG hf hR hRsum hk hCr
  refine ⟨hsmooth, hconv, ?_⟩
  have hδ : Tendsto (fun J ↦ (R J) ^ (-(k J : ℝ))) atTop (𝓝 0) := by
    simpa only [add_zero] using (summable_rpow_order_bound hR hRsum hk 0).tendsto_atTop_zero
  apply inducedMetric_eq_of_tendsto
    (M := fun J x ↦ G x + ∑ j ∈ Finset.range J, periodicLift (f j) x)
  · intro x hx i
    exact tendsto_partialDeriv_of_tendsto_iteratedFDeriv_one ((hconv 1).tendsto_at hx) i
  · intro x hx
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun J ↦ norm_nonneg _) (fun J ↦ herror J x hx)
      (by simpa using hδ.pow 2)

/-- Section 9 after `main:eq:final-Cr`: with the exact manuscript power loss and
superexponential scales, the metric induction passes to the limit, and the single
rescaling by `a = sρ` gives the original metric on `a • W`. The Fourier estimate
and metric induction are explicit hypotheses; this is the final limiting argument. -/
theorem smooth_isometric_rescale_of_final_cNorm_bound {n N : ℕ}
    {G : Euclidean n → Euclidean N} {f : ℕ → Torus n → Euclidean N}
    {W : Set (Euclidean n)} {g : MetricField n} {R₀ v a : ℝ} {k : ℕ → ℕ}
    {C : ℕ → ℝ} (hW : IsOpen W) (hG : ContDiffOn ℝ ∞ G W)
    (hf : ∀ j, IsSmoothPeriodic (f j)) (hR₀ : 1 < R₀) (hv : 1 < v)
    (ha : a ≠ 0) (hk : Tendsto k atTop atTop)
    (hCr : ∀ r j, cNorm (fundamentalCell n) r (periodicLift (f j)) ≤
      C r * (R₀ ^ (v ^ j)) ^ (-(k j : ℝ) +
        (displacementLoss n + 1 + bandExponent * ((r : ℝ) + (n : ℝ) / 2))))
    (herror : ∀ J, ∀ x ∈ W,
      ‖inducedMetric (fun y ↦ G y + ∑ j ∈ Finset.range J, periodicLift (f j) y) x -
        g (a • x)‖ ≤ ((R₀ ^ (v ^ J)) ^ (-(k J : ℝ))) ^ 2) :
    ContDiffOn ℝ ∞
      (fun x ↦ a • (G (a⁻¹ • x) + ∑' j, periodicLift (f j) (a⁻¹ • x)))
      ((fun y ↦ a • y) '' W) ∧
    IsIsometricOn g
      (fun x ↦ a • (G (a⁻¹ • x) + ∑' j, periodicLift (f j) (a⁻¹ • x)))
      ((fun y ↦ a • y) '' W) := by
  have hR (j : ℕ) : 1 ≤ R₀ ^ (v ^ j) :=
    Real.one_le_rpow hR₀.le (pow_nonneg (le_trans zero_le_one hv.le) j)
  obtain ⟨hsmooth, _, hmetric⟩ := smooth_isometric_limit_of_periodic_bounds hW hG hf hR
    (summable_inverse_power_scale hR₀ hv) hk (fun r ↦ Filter.Eventually.of_forall (hCr r))
    herror
  exact smooth_isometric_rescale ha hsmooth hW hmetric

end JanetCartan
