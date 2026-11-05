module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Periodization.Derivatives
public import JanetCartan.Analysis.Fourier.SeparatedSampling.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Basic

import Mathlib.Tactic.Linarith

/-!
# Joint periodization of the original Hermitian kernel

Consumer: `PhysicalMean.originalBackgroundQuadratureForcing_source_profile`,
`app:ch_mean_pairs:eq:comparison-input` and `new:eq:mean-source`. The actual
physical Hermitian kernel and its derivative budget are inputs produced by the
original-data construction. This file proves the independent periodization
step from its primitive joint smoothness and a uniform physical support gap.

The construction uses the literal centered representative, without any new
cutoff. Its lift agrees with the physical kernel on a joint neighborhood of
every point above the closed fundamental cell, including the boundary. Thus
all mixed physical/carrier Fréchet derivatives agree exactly, with neither an
order loss nor a numerical loss. The carrier `SeparatedSampling.Point` keeps
its sup norm, and no positive-dimension assumption is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

open Filter
open scoped Topology ContDiff

namespace JanetCartan.PhysicalMean

open SeparatedSampling

variable {n : ℕ}

/-- Literal periodization of the physical Hermitian kernel in
`app:ch_mean_pairs:eq:comparison-input`; no additional cutoff is inserted. -/
def jointHermitianPeriodization (H : Euclidean n × Point → Euclidean n) :
    Torus n × Point → Euclidean n :=
  fun w ↦ H (AmplitudeBound.centeredTorusRepresentative w.1, w.2)

/-- A support gap gives equality on the larger open physical box, uniformly
in the carrier. This is the local input for `new:eq:mean-source`. -/
theorem jointHermitianPeriodization_lift_eq_of_lt {r : ℝ} (hr : r < 1 / 2)
    {H : Euclidean n × Point → Euclidean n}
    (hs : ∀ z x, H (x, z) ≠ 0 → ∀ i, |x i| ≤ r)
    {x : Euclidean n} (hx : ∀ i, |x i| < 1 - r) (z : Point) :
    jointHermitianPeriodization H (torusQuotient x, z) = H (x, z) := by
  ext i
  have hsi : AmplitudeBound.SupportedInCenteredBox r
      (fun y : Euclidean n ↦ (H (y, z) i : ℂ)) := by
    intro y hy
    apply hs z y
    intro hzero
    apply hy
    simp [hzero]
  have he := AmplitudeBound.periodicLift_amplitudePeriodization_eq_of_lt hr hsi hx
  simpa only [periodicLift, AmplitudeBound.amplitudePeriodization, Function.comp_apply,
    Complex.ofReal_re, jointHermitianPeriodization] using congrArg Complex.re he

/-- Joint neighborhood equality above the entire closed physical cell,
including its faces (`app:ch_mean_pairs:eq:comparison-input`). Uniform support
for all carrier points is essential here; no regularity hypothesis is needed. -/
theorem jointHermitianPeriodization_lift_eventuallyEq {r : ℝ} (hr : r < 1 / 2)
    {H : Euclidean n × Point → Euclidean n}
    (hs : ∀ z x, H (x, z) ≠ 0 → ∀ i, |x i| ≤ r)
    {x : Euclidean n} (hx : x ∈ fundamentalCell n) (z : Point) :
    (fun w : Euclidean n × Point ↦
      jointHermitianPeriodization H (torusQuotient w.1, w.2)) =ᶠ[𝓝 (x, z)] H := by
  have hmem : ∀ᶠ w : Euclidean n × Point in 𝓝 (x, z),
      ∀ i, |w.1 i| < 1 - r := by
    apply eventually_all.mpr
    intro i
    apply (isOpen_lt (((EuclideanSpace.proj i).continuous.comp continuous_fst).abs)
      continuous_const).mem_nhds
    exact (abs_le.mpr (hx i)).trans_lt (by linarith)
  exact hmem.mono fun w hw ↦ jointHermitianPeriodization_lift_eq_of_lt hr hs hw w.2

/-- Exact values on the closed fundamental cell, with no boundary exception
(`app:ch_mean_pairs:eq:comparison-input`). -/
theorem jointHermitianPeriodization_lift_eq {r : ℝ} (hr : r < 1 / 2)
    {H : Euclidean n × Point → Euclidean n}
    (hs : ∀ z x, H (x, z) ≠ 0 → ∀ i, |x i| ≤ r)
    {x : Euclidean n} (hx : x ∈ fundamentalCell n) (z : Point) :
    jointHermitianPeriodization H (torusQuotient x, z) = H (x, z) :=
  (jointHermitianPeriodization_lift_eventuallyEq hr hs hx z).self_of_nhds

/-- The literal periodized kernel has a globally smooth joint lift, as
required by `originalBackgroundQuadratureForcing_source_profile`. Smoothness
comes from physical joint smoothness and the support gap, not from a false
continuity assertion about centered representatives at cell boundaries. -/
theorem contDiff_jointHermitianPeriodization_lift {r : ℝ} (hr : r < 1 / 2)
    {H : Euclidean n × Point → Euclidean n}
    (hs : ∀ z x, H (x, z) ≠ 0 → ∀ i, |x i| ≤ r)
    (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦
      jointHermitianPeriodization H (torusQuotient w.1, w.2)) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨x, z⟩
  obtain ⟨y, hy, k, rfl⟩ := exists_mem_fundamentalCell_add_integerTranslation x
  have hlocal := hH.contDiffAt.congr_of_eventuallyEq
    (jointHermitianPeriodization_lift_eventuallyEq hr hs hy z)
  have hlocal' : ContDiffAt ℝ ∞
      (fun w : Euclidean n × Point ↦
        jointHermitianPeriodization H (torusQuotient w.1, w.2))
      ((y + integerTranslation k) - integerTranslation k, z) := by
    simpa only [add_sub_cancel_right] using hlocal
  have hcomp := hlocal'.comp (y + integerTranslation k, z)
    ((contDiffAt_fst.sub (contDiffAt_const (c := integerTranslation k))).prodMk contDiffAt_snd)
  convert hcomp using 1
  funext w
  have hq : torusQuotient w.1 = torusQuotient (w.1 - integerTranslation k) := by
    simpa only [sub_add_cancel] using
      torusQuotient_add_integerTranslation (w.1 - integerTranslation k) k
  exact congrArg (fun t ↦ jointHermitianPeriodization H (t, w.2)) hq

/-- All joint iterated Fréchet derivatives, hence all mixed physical/carrier
orders, agree on the closed cell with exactly the same order and constant
(`app:ch_mean_pairs:eq:comparison-input`). Even this identity requires no
smoothness assumption, since joint neighborhood equality suffices. -/
theorem iteratedFDeriv_jointHermitianPeriodization_lift_eq {r : ℝ} (hr : r < 1 / 2)
    {H : Euclidean n × Point → Euclidean n}
    (hs : ∀ z x, H (x, z) ≠ 0 → ∀ i, |x i| ≤ r)
    (k : ℕ) {x : Euclidean n} (hx : x ∈ fundamentalCell n) (z : Point) :
    iteratedFDeriv ℝ k (fun w : Euclidean n × Point ↦
      jointHermitianPeriodization H (torusQuotient w.1, w.2)) (x, z) =
        iteratedFDeriv ℝ k H (x, z) :=
  ((jointHermitianPeriodization_lift_eventuallyEq hr hs hx z).iteratedFDeriv ℝ k).self_of_nhds

/-- The exact weighted identity in the joint-jet premise of
`originalBackgroundQuadratureForcing_source_profile`. The original carrier
weight is retained, with no additional cutoff or derivative-order loss
(`app:ch_mean_pairs:eq:comparison-input`). -/
theorem iteratedFDeriv_weighted_jointHermitianPeriodization_lift_eq {r : ℝ}
    (hr : r < 1 / 2) {H : Euclidean n × Point → Euclidean n}
    (hs : ∀ z x, H (x, z) ≠ 0 → ∀ i, |x i| ≤ r)
    (ψ : Point → ℝ) (k : ℕ) {x : Euclidean n}
    (hx : x ∈ fundamentalCell n) (z : Point) :
    iteratedFDeriv ℝ k (fun w : Euclidean n × Point ↦
      ψ w.2 • jointHermitianPeriodization H (torusQuotient w.1, w.2)) (x, z) =
        iteratedFDeriv ℝ k (fun w : Euclidean n × Point ↦ ψ w.2 • H w) (x, z) := by
  have he : (fun w : Euclidean n × Point ↦
      ψ w.2 • jointHermitianPeriodization H (torusQuotient w.1, w.2)) =ᶠ[𝓝 (x, z)]
        (fun w : Euclidean n × Point ↦ ψ w.2 • H w) :=
    (jointHermitianPeriodization_lift_eventuallyEq hr hs hx z).mono
      (fun w hw ↦ congrArg (fun v : Euclidean n ↦ ψ w.2 • v) hw)
  exact (he.iteratedFDeriv ℝ k).self_of_nhds

end JanetCartan.PhysicalMean
