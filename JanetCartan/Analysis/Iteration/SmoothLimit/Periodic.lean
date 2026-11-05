module

public import JanetCartan.Analysis.Iteration.SmoothLimit.Series
public import JanetCartan.Analysis.Iteration.SmoothLimit.Rates
public import JanetCartan.Analysis.Iteration.SmoothLimit.Seminorm
public import JanetCartan.Analysis.Fourier.Periodic.Calculus

/-!
# Smooth convergence from periodic seminorm estimates

Section 9, `main:eq:final-Cr`: the cell seminorm estimate for each increment is an
explicit analytic input. Periodicity transfers it to the whole coordinate space;
the derivative order changes only the summable majorant, never the sum or its domain.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology
open Filter

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:eq:final-Cr`: the seminorm on the fundamental cell controls each derivative
of a smooth periodic lift at every Euclidean point. -/
theorem norm_iteratedFDeriv_periodicLift_le_cNorm {f : Torus n → F}
    (hf : IsSmoothPeriodic f) {r k : ℕ} (hkr : k ≤ r) (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ k (periodicLift f) x‖ ≤
      cNorm (fundamentalCell n) r (periodicLift f) := by
  apply norm_iteratedFDeriv_periodicLift_le f k _ x
  intro y hy
  exact norm_iteratedFDeriv_le_cNorm (isCompact_fundamentalCell n)
    (hf.2.of_le (by simp)) hy hkr

/-- `main:eq:final-Cr`: eventual cell seminorm bounds give eventual global derivative
bounds, with the same constants and the same order-dependent exceptional indices. -/
theorem eventually_iteratedFDeriv_le_of_periodic_cNorm {f : ℕ → Torus n → F}
    {v : ℕ → ℕ → ℝ} (hf : ∀ j, IsSmoothPeriodic (f j))
    (hb : ∀ r, ∀ᶠ j in atTop, cNorm (fundamentalCell n) r (periodicLift (f j)) ≤ v r j) :
    ∀ r, ∀ᶠ j in atTop, ∀ x, ‖iteratedFDeriv ℝ r (periodicLift (f j)) x‖ ≤ v r j := by
  intro r
  filter_upwards [hb r] with j hj
  exact fun x ↦ (norm_iteratedFDeriv_periodicLift_le_cNorm (hf j) le_rfl x).trans hj

variable [CompleteSpace F]

/-- Section 9, `main:eq:final-Cr`: one smooth sum on the fixed open neighborhood,
from eventual summable fundamental-cell seminorm bounds. -/
theorem smooth_periodic_limit_of_cNorm_bounds
    {G : EuclideanSpace ℝ (Fin n) → F} {f : ℕ → Torus n → F}
    {v : ℕ → ℕ → ℝ} {W : Set (EuclideanSpace ℝ (Fin n))}
    (hW : IsOpen W) (hG : ContDiffOn ℝ ∞ G W)
    (hf : ∀ j, IsSmoothPeriodic (f j)) (hv : ∀ r, Summable (v r))
    (hb : ∀ r, ∀ᶠ j in atTop, cNorm (fundamentalCell n) r (periodicLift (f j)) ≤ v r j) :
    ContDiffOn ℝ ∞ (fun x ↦ G x + ∑' j, periodicLift (f j) x) W ∧
      ∀ r : ℕ, TendstoUniformlyOn
        (fun J ↦ iteratedFDeriv ℝ r
          (fun x ↦ G x + ∑ j ∈ Finset.range J, periodicLift (f j) x))
        (iteratedFDeriv ℝ r (fun x ↦ G x + ∑' j, periodicLift (f j) x)) atTop W :=
  smooth_limit_on_of_eventual_bounds hW hG (fun j ↦ (hf j).2) hv
    (eventually_iteratedFDeriv_le_of_periodic_cNorm hf hb)

/-- Section 9, `main:eq:final-Cr`: the fixed-order power loss is harmless once the
orders diverge. The estimate is an input, not a claimed proof of Fourier Bernstein. -/
theorem smooth_periodic_limit_of_power_bounds
    {G : EuclideanSpace ℝ (Fin n) → F} {f : ℕ → Torus n → F}
    {W : Set (EuclideanSpace ℝ (Fin n))} {R : ℕ → ℝ} {k : ℕ → ℕ}
    {C b : ℕ → ℝ} (hW : IsOpen W) (hG : ContDiffOn ℝ ∞ G W)
    (hf : ∀ j, IsSmoothPeriodic (f j)) (hR : ∀ j, 1 ≤ R j)
    (hRsum : Summable (fun j ↦ (R j)⁻¹)) (hk : Tendsto k atTop atTop)
    (hb : ∀ r, ∀ᶠ j in atTop, cNorm (fundamentalCell n) r (periodicLift (f j)) ≤
      C r * (R j) ^ (-(k j : ℝ) + b r)) :
    ContDiffOn ℝ ∞ (fun x ↦ G x + ∑' j, periodicLift (f j) x) W ∧
      ∀ r : ℕ, TendstoUniformlyOn
        (fun J ↦ iteratedFDeriv ℝ r
          (fun x ↦ G x + ∑ j ∈ Finset.range J, periodicLift (f j) x))
        (iteratedFDeriv ℝ r (fun x ↦ G x + ∑' j, periodicLift (f j) x)) atTop W :=
  smooth_periodic_limit_of_cNorm_bounds hW hG hf
    (fun r ↦ (summable_rpow_order_bound hR hRsum hk (b r)).mul_left (C r)) hb

/-- Section 9 after `main:eq:final-Cr`: the same partial sums converge in every
`C^r` seminorm to the single smooth limit, on the original open neighborhood. -/
theorem tendsto_cNorm_periodic_partial_sums_of_power_bounds
    {G : EuclideanSpace ℝ (Fin n) → F} {f : ℕ → Torus n → F}
    {W : Set (EuclideanSpace ℝ (Fin n))} {R : ℕ → ℝ} {k : ℕ → ℕ}
    {C b : ℕ → ℝ} (hW : IsOpen W) (hG : ContDiffOn ℝ ∞ G W)
    (hf : ∀ j, IsSmoothPeriodic (f j)) (hR : ∀ j, 1 ≤ R j)
    (hRsum : Summable (fun j ↦ (R j)⁻¹)) (hk : Tendsto k atTop atTop)
    (hb : ∀ r, ∀ᶠ j in atTop, cNorm (fundamentalCell n) r (periodicLift (f j)) ≤
      C r * (R j) ^ (-(k j : ℝ) + b r)) (r : ℕ) :
    Tendsto (fun J ↦ cNorm W r
      ((fun x ↦ G x + ∑ j ∈ Finset.range J, periodicLift (f j) x) -
        (fun x ↦ G x + ∑' j, periodicLift (f j) x))) atTop (𝓝 0) := by
  obtain ⟨hsmooth, hconv⟩ := smooth_periodic_limit_of_power_bounds hW hG hf hR hRsum hk hb
  apply tendsto_cNorm_sub_of_uniform_derivatives hW _ (hsmooth.of_le (by simp))
    (fun i _ ↦ hconv i)
  intro J
  exact hG.of_le (by simp) |>.add
    (ContDiff.sum (fun j _ ↦ (hf j).2.of_le (by simp))).contDiffOn

end JanetCartan
