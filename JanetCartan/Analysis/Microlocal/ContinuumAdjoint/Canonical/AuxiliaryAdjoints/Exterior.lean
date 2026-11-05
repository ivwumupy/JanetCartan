module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Multipliers

/-!
# The fixed exterior adjoint on the natural Sobolev scale

For `app:ch_background:prop:bg-adjoint`, the exterior adjoint is the literal
self-adjoint multiplier by `1 - ψ` on normalized torus measure. Its Sobolev
bound follows from the fixed smooth multiplier, without an estimate premise.
The consumer is the exterior slot of the parent's augmented adjoint.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumAdjoint.Canonical.AuxiliaryAdjoints

open PeriodicSobolevSpace ContinuumRow
open ContinuumCommutator.ImageChannel.Differential

variable {n : ℕ}

/-- Smoothness of the fixed exterior multiplier used in the constructed
Sobolev adjoint (`app:ch_background:prop:bg-adjoint`). -/
theorem smooth_exteriorCutoff (ψ : C(Torus n, ℝ)) (hψ : IsSmoothPeriodic ψ) :
    IsSmoothPeriodic (1 - ψ : C(Torus n, ℝ)) :=
  ⟨continuous_const.sub hψ.1, contDiff_const.sub hψ.2⟩

/-- Construct the fixed exterior adjoint at every natural Sobolev order
(`app:ch_background:prop:bg-adjoint`). -/
def exteriorAdjointSobolev (ψ : C(Torus n, ℝ)) (hψ : IsSmoothPeriodic ψ) (s : ℕ) :
    PeriodicSobolevSpace n (Euclidean n) s →L[ℝ]
      PeriodicSobolevSpace n (Euclidean n) s :=
  cutoffSobolev (1 - ψ) (smooth_exteriorCutoff ψ hψ) s

/-- The Sobolev action is the literal exterior-channel adjoint, with the same
cutoff and normalized measure (`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem toL2_exteriorAdjointSobolev (ψ : C(Torus n, ℝ))
    (hψ : IsSmoothPeriodic ψ) (s : ℕ) (u : PeriodicSobolevSpace n (Euclidean n) s) :
    toL2 s (exteriorAdjointSobolev ψ hψ s u) = (exteriorChannel ψ).adjoint (toL2 s u) := by
  rw [exteriorAdjointSobolev, toL2_cutoffSobolev, exteriorChannel_adjoint]
  rfl

/-- All-data natural-order regularity of the fixed exterior adjoint
(`app:ch_background:prop:bg-adjoint`). -/
theorem exteriorAdjoint_mem (ψ : C(Torus n, ℝ)) (hψ : IsSmoothPeriodic ψ)
    (s : ℕ) {v : OutputL2 n} (hv : v ∈ periodicSobolevLevel n (Euclidean n) s) :
    (exteriorChannel ψ).adjoint v ∈ periodicSobolevLevel n (Euclidean n) s := by
  have h := toL2_mem s (exteriorAdjointSobolev ψ hψ s (ofL2 s v hv))
  simpa only [toL2_exteriorAdjointSobolev, toL2_ofL2] using h

/-- The fixed smooth exterior multiplier gives uniform all-data bounds at
every natural order, including zero (`app:ch_background:prop:bg-adjoint`).
The bounded Sobolev multiplier is constructed, not supplied as a hypothesis. -/
theorem exists_exteriorAdjoint_bound (ψ : C(Torus n, ℝ)) (hψ : IsSmoothPeriodic ψ) :
    ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ (s : ℕ) (u : PeriodicSobolevSpace n (Euclidean n) s),
        ‖exteriorAdjointSobolev ψ hψ s u‖ ≤ C s * ‖u‖ := by
  refine ⟨fun s ↦ 1 + ‖exteriorAdjointSobolev ψ hψ s‖,
    fun s ↦ by positivity, ?_⟩
  intro s u
  exact ((exteriorAdjointSobolev ψ hψ s).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg u))

end JanetCartan.ContinuumAdjoint.Canonical.AuxiliaryAdjoints
