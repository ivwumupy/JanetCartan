module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.SupportedBudgets
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.KernelExtensions
public import JanetCartan.Analysis.Fourier.SeparatedSampling.Geometry

/-!
# The retained background on the original carrier graph

The graph uses the original sampling coordinate `WithLp.toLp 2 z` and the
existing extension of the SAME frozen covector. The extension is removed on
the prescribed measurement support in `CarrierBounds.Matching`.
Consumer: `app:ch_waves:eq:background-quadrature` and its rough bound.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.RetainedBackground
open ActualCarriers FrozenMenu CurrentFullPhase MeasuredAmplitude

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  {ρ : ℝ} (hρ : 0 < ρ)

/-- The original carrier substitution, with the fixed smooth covector
extension used by the measured kernel (`app:ch_waves:eq:background-quadrature`). -/
def retainedCarrierPoint (q : ℝ × (SeparatedSampling.Point × Euclidean (m + 1))) :
    ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) :=
  (q.1, (q.2.2, (WithLp.toLp 2 q.2.1,
    extendedRetainedCarrier T a.2.1 hρ (WithLp.toLp 2 q.2.1))))

/-- Global joint smoothness of the actual fixed carrier substitution follows
from the original buffered patch (`app:ch_waves:setup:oscillatory`). -/
theorem contDiff_retainedCarrierPoint {c C : ℝ} (hP : P.IsValid c C)
    (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius)) :
    ContDiff ℝ ∞ (retainedCarrierPoint T a hρ) := by
  have hz : ContDiff ℝ ∞ (fun q : ℝ × (SeparatedSampling.Point × Euclidean (m + 1)) ↦
      WithLp.toLp 2 q.2.1) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).symm.contDiff.comp
      (contDiff_fst.comp contDiff_snd)
  exact contDiff_fst.prodMk (contDiff_snd.snd.prodMk
    (hz.prodMk ((contDiff_extendedRetainedCarrier T hP a.2.1 hρ hcarrier).comp hz)))

/-- A fixed compact set in the original sampling and physical coordinates.
It bounds the support before all fields and frequencies
(`app:ch_waves:eq:background-quadrature`). -/
def retainedCarrierSupport : Set (SeparatedSampling.Point × Euclidean (m + 1)) :=
  ((WithLp.toLp 2) ⁻¹' closedBall a.2.1 ρ) ×ˢ closedBall a.1 ρ

/-- Compactness uses the original finite-dimensional coordinate equivalence;
no measure is changed (`app:ch_waves:eq:background-quadrature`). -/
theorem isCompact_retainedCarrierSupport : IsCompact (retainedCarrierSupport a (ρ := ρ)) := by
  have hz : IsCompact ((WithLp.toLp 2) ⁻¹' closedBall a.2.1 ρ) :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).symm.toHomeomorph.isCompact_preimage).mpr (isCompact_closedBall _ _)
  exact hz.prod (isCompact_closedBall _ _)

/-- Pull the supported joint tensor back to the SAME carrier graph, retaining
all inverse-frequency and physical variables
(`app:ch_waves:eq:background-quadrature`). -/
def retainedCarrierPullback (χ : Euclidean (m + 1) → ℝ)
    (H : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (τ : ℝ) (z : SeparatedSampling.Point) (x : Euclidean (m + 1)) :=
  supportedJointTensor a hρ χ H (retainedCarrierPoint T a hρ (τ, (z, x)))

/-- Joint smoothness is inherited from the actual supported polynomial and
proved carrier extension (`app:ch_waves:eq:background-quadrature`). -/
theorem contDiff_retainedCarrierPullback {c C : ℝ} (hP : P.IsValid c C)
    (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    (χ : Euclidean (m + 1) → ℝ)
    (H : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hH : ContDiff ℝ ∞ (supportedJointTensor a hρ χ H)) :
    ContDiff ℝ ∞ (fun q : ℝ × (SeparatedSampling.Point × Euclidean (m + 1)) ↦
      retainedCarrierPullback T a hρ χ H q.1 q.2.1 q.2.2) :=
  hH.comp (contDiff_retainedCarrierPoint T a hρ hP hcarrier)

/-- All jets vanish outside one fixed carrier/physical compact set. This
reduces the carrier chain rule to compact fixed geometry, rather than assuming
its derivative bounds (`app:ch_waves:eq:background-quadrature-rough`). -/
theorem retainedCarrierPullback_eventuallyEq_zero {c C : ℝ} (hP : P.IsValid c C)
    (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    (χ : Euclidean (m + 1) → ℝ)
    (H : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    {q : ℝ × (SeparatedSampling.Point × Euclidean (m + 1))}
    (hq : q.2 ∉ retainedCarrierSupport a (ρ := ρ)) :
    (fun p : ℝ × (SeparatedSampling.Point × Euclidean (m + 1)) ↦
      retainedCarrierPullback T a hρ χ H p.1 p.2.1 p.2.2) =ᶠ[𝓝 q] 0 := by
  have hw : (retainedCarrierPoint T a hρ q).2 ∉ closedBall a (3 * ρ / 4) := by
    intro hw
    rw [← closedBall_prod_same, ← closedBall_prod_same] at hw
    exact hq ⟨closedBall_subset_closedBall (by linarith) hw.2.1,
      closedBall_subset_closedBall (by linarith) hw.1⟩
  have hz : (retainedAmplitudeCutoff a hρ : _ → ℝ) =ᶠ[𝓝 (retainedCarrierPoint T a hρ q).2] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (by
      simpa only [ContDiffBump.tsupport_eq, retainedAmplitudeCutoff] using hw)
  filter_upwards [hz.comp_tendsto
    ((contDiff_retainedCarrierPoint T a hρ hP hcarrier).continuous.snd.tendsto q)] with p hp
  change retainedAmplitudeCutoff a hρ (retainedCarrierPoint T a hρ p).2 = 0 at hp
  simp only [retainedCarrierPullback, supportedJointTensor, hp, zero_mul, zero_smul,
    Pi.zero_apply]

/-- Common compact physical support, uniform in the polynomial, inverse
frequency and original carrier label (`app:ch_waves:eq:background-quadrature`). -/
theorem retainedCarrierPullback_tsupport_subset
    (χ : Euclidean (m + 1) → ℝ)
    (H : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (τ : ℝ) (z : SeparatedSampling.Point) :
    tsupport (retainedCarrierPullback T a hρ χ H τ z) ⊆ closedBall a.1 (3 * ρ / 4) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hn
  exact hx (supportedJointTensor_eq_zero_off_physical a hρ χ H τ
    (retainedCarrierPoint T a hρ (τ, (z, x))).2 hn)

/-- Multiplication by the original sampling weight preserves the same common
compact physical support (`app:ch_waves:eq:background-quadrature-rough`). -/
theorem weighted_retainedCarrierPullback_tsupport_subset
    (χ : Euclidean (m + 1) → ℝ) (ψ : SeparatedSampling.Point → ℝ)
    (H : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (τ : ℝ) (z : SeparatedSampling.Point) :
    tsupport (fun x ↦ ψ z • retainedCarrierPullback T a hρ χ H τ z x) ⊆
      closedBall a.1 (3 * ρ / 4) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hn
  apply hx
  change ψ z • retainedCarrierPullback T a hρ χ H τ z x = 0
  rw [show retainedCarrierPullback T a hρ χ H τ z x = 0 from
    supportedJointTensor_eq_zero_off_physical a hρ χ H τ
      (retainedCarrierPoint T a hρ (τ, (z, x))).2 hn, smul_zero]

end JanetCartan.Sampling.RetainedBackground
