module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.CompactSupport
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth compact exhaustion of the literal carrier

Concrete regularizations for `app:ch_background:prop:bg-adjoint`. The product
norm is used only to choose a cutoff; the integration measure remains `dz dη`.
Consumer: `modifiedCarrierOperator` and removal of its regularization.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels

open ContinuumRow
variable {n : ℕ}

/-- Carrier cutoff with inner radius `k+1` and outer radius `2(k+1)`, for
`app:ch_background:prop:bg-adjoint`. -/
def modifiedCarrierCutoffBump (n k : ℕ) : ContDiffBump (0 : CarrierVariable n) where
  rIn := k + 1
  rOut := 2 * (k + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith [Nat.cast_nonneg (α := ℝ) k]

/-- A concrete compact regularization sequence on the actual carrier space
(`app:ch_background:prop:bg-adjoint`). -/
def modifiedCarrierCutoff (k : ℕ) : CarrierVariable n → ℝ := modifiedCarrierCutoffBump n k

/-- All primitive derivatives of the carrier regularization exist
(`app:ch_background:prop:bg-adjoint`). -/
theorem contDiff_modifiedCarrierCutoff (k : ℕ) :
    ContDiff ℝ ∞ (modifiedCarrierCutoff (n := n) k) :=
  (modifiedCarrierCutoffBump n k).contDiff

/-- Compact support of the concrete regularization
(`app:ch_background:prop:bg-adjoint`). -/
theorem hasCompactSupport_modifiedCarrierCutoff (k : ℕ) :
    HasCompactSupport (modifiedCarrierCutoff (n := n) k) :=
  (modifiedCarrierCutoffBump n k).hasCompactSupport

/-- The regularization is real, nonnegative, and at most one
(`app:ch_background:prop:bg-adjoint`). -/
theorem modifiedCarrierCutoff_mem_Icc (k : ℕ) (u : CarrierVariable n) :
    modifiedCarrierCutoff k u ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(modifiedCarrierCutoffBump n k).nonneg, (modifiedCarrierCutoffBump n k).le_one⟩

/-- Exact outer support of the regularization
(`app:ch_background:prop:bg-adjoint`). -/
theorem modifiedCarrierCutoff_eq_zero (k : ℕ) (u : CarrierVariable n)
    (hu : 2 * ((k : ℝ) + 1) ≤ ‖u‖) : modifiedCarrierCutoff k u = 0 :=
  (modifiedCarrierCutoffBump n k).zero_of_le_dist (by simpa [modifiedCarrierCutoffBump] using hu)

/-- Exact inner plateau of the regularization
(`app:ch_background:prop:bg-adjoint`). -/
theorem modifiedCarrierCutoff_eq_one (k : ℕ) (u : CarrierVariable n)
    (hu : ‖u‖ ≤ (k : ℝ) + 1) : modifiedCarrierCutoff k u = 1 :=
  (modifiedCarrierCutoffBump n k).one_of_mem_closedBall
    (by simpa [modifiedCarrierCutoffBump] using hu)

/-- On the open plateau all positive-order derivatives vanish, as follows
from this local equality to the constant one
(`app:ch_background:prop:bg-adjoint`). -/
theorem modifiedCarrierCutoff_eventuallyEq_one (k : ℕ) (u : CarrierVariable n)
    (hu : ‖u‖ < (k : ℝ) + 1) :
    modifiedCarrierCutoff k =ᶠ[𝓝 u] fun _ ↦ (1 : ℝ) :=
  (modifiedCarrierCutoffBump n k).eventuallyEq_one_of_mem_ball
    (by simpa [modifiedCarrierCutoffBump] using hu)

/-- Pointwise limit one, with eventual exact equality
(`app:ch_background:prop:bg-adjoint`). -/
theorem tendsto_modifiedCarrierCutoff (u : CarrierVariable n) :
    Tendsto (fun k ↦ modifiedCarrierCutoff k u) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := exists_nat_gt ‖u‖
  filter_upwards [eventually_ge_atTop N] with k hk
  symm
  apply modifiedCarrierCutoff_eq_one
  exact le_trans hN.le (by exact_mod_cast (by omega : N ≤ k + 1))

/-- Each cutoff is a dilation of one fixed bump. This is the primitive
scaling used for cutoff derivatives (`app:ch_background:prop:bg-adjoint`). -/
theorem modifiedCarrierCutoff_eq_dilate (k : ℕ) (u : CarrierVariable n) :
    modifiedCarrierCutoff k u = modifiedCarrierCutoff 0 (((k : ℝ) + 1)⁻¹ • u) := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  simp [modifiedCarrierCutoff, ContDiffBump.apply, modifiedCarrierCutoffBump,
    mul_div_cancel_right₀ _ hk]

/-- Exact derivative scaling of the regularization, before any symbol estimate
(`app:ch_background:prop:bg-adjoint`). -/
theorem iteratedFDeriv_modifiedCarrierCutoff (k r : ℕ) (u : CarrierVariable n) :
    iteratedFDeriv ℝ r (modifiedCarrierCutoff k) u =
      (((k : ℝ) + 1)⁻¹) ^ r • iteratedFDeriv ℝ r (modifiedCarrierCutoff 0)
        (((k : ℝ) + 1)⁻¹ • u) := by
  have he : modifiedCarrierCutoff (n := n) k =
      fun u ↦ modifiedCarrierCutoff 0 (((k : ℝ) + 1)⁻¹ • u) :=
    funext (modifiedCarrierCutoff_eq_dilate k)
  rw [he, iteratedFDeriv_comp_const_smul _
    ((contDiff_modifiedCarrierCutoff 0).of_le (by simp))]

/-- Every primitive derivative retains compact support
(`app:ch_background:prop:bg-adjoint`). -/
theorem hasCompactSupport_iteratedFDeriv_modifiedCarrierCutoff (k r : ℕ) :
    HasCompactSupport (iteratedFDeriv ℝ r (modifiedCarrierCutoff (n := n) k)) :=
  (hasCompactSupport_modifiedCarrierCutoff k).iteratedFDeriv r

end JanetCartan.ContinuumAdjoint.DerivativeKernels
