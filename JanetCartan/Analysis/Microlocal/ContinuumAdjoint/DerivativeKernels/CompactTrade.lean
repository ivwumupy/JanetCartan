module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Transport

/-!
# Compact measurement-support derivative trades

The one-step integration-by-parts calculation following
`app:ch_background:eq:bg-derivative-trade`. These are Euclidean chart integrals,
with Lebesgue measurement measure. Identifying them with the literal torus
adjoint requires the chart integral identity; no measure identification is made
here. The full amplitude includes the measurement and angular cutoffs and scalar
transport. In particular its derivatives must not be omitted.

The consumer is the iterated expansion for
`app:ch_background:prop:bg-adjoint`. Smoothness, common compact measurement
support, and the exact phase velocity identity are the only analytic inputs to
the parameter trade. Integrability and differentiation under the integral are
proved by the shared compact transport theorem.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels

open NormalComparison

variable {n : ℕ}

/-- The scalar component of the adjoint chart integral in
`app:ch_background:prop:bg-adjoint`, with the conjugated phase and physical η
convention. No initial-variable cutoff is included. -/
def chartAdjoint (φ : Euclidean n → ℝ) (a v : Euclidean n → ℂ) : ℂ :=
  ∫ x, oscillatoryFactor (-1) (φ x) * (a x * v x)

/-- Compact measurement support supplies convergence of the literal chart
integral in `app:ch_background:prop:bg-adjoint`, without a physical initial cutoff. -/
theorem integrable_chartAdjoint {φ : Euclidean n → ℝ} {a v : Euclidean n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (ha : Continuous a) (hv : Continuous v)
    (hs : HasCompactSupport a) :
    Integrable (fun x ↦ oscillatoryFactor (-1) (φ x) * (a x * v x)) :=
  (((CompactTransport.contDiff_oscillatoryFactor hφ (-1)).continuous).mul
    (ha.mul hv)).integrable_of_hasCompactSupport hs.mul_right.mul_left

/-- The actual zero-data-derivative amplitude after one carrier derivative,
`∂z a - divₓ(V a)` (`app:ch_background:eq:bg-derivative-trade`). -/
def carrierZeroAmplitude (az a : Euclidean n → ℂ)
    (V : Euclidean n → Euclidean n) : Euclidean n → ℂ :=
  transportCoefficient az (fun j x ↦ V x j • a x)

/-- The amplitude accompanying `∂xⱼ v` after one carrier derivative in
`app:ch_background:prop:bg-adjoint`. -/
def carrierFirstAmplitude (a : Euclidean n → ℂ)
    (V : Euclidean n → Euclidean n) (j : Fin n) (x : Euclidean n) : ℂ :=
  -(V x j • a x)

/-- The divergence expansion retains the complex datum and its physical
derivatives, for `app:ch_background:prop:bg-adjoint`. -/
theorem transportCoefficient_mul_datum
    (az a v : Euclidean n → ℂ) (V : Euclidean n → Euclidean n)
    (ha : ContDiff ℝ ∞ a) (hv : ContDiff ℝ ∞ v) (hV : ContDiff ℝ ∞ V)
    (x : Euclidean n) :
    transportCoefficient (fun y ↦ az y * v y)
      (fun j y ↦ V y j • (a y * v y)) x =
      carrierZeroAmplitude az a V x * v x +
        ∑ j, carrierFirstAmplitude a V j x * partialDeriv v x j := by
  have hB (j : Fin n) : DifferentiableAt ℝ (fun y ↦ V y j • a y) x :=
    (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp hV).smul
      ha).differentiable (by simp) x
  have hp (j : Fin n) :
      partialDeriv (fun y ↦ V y j • (a y * v y)) x j =
        partialDeriv (fun y ↦ V y j • a y) x j * v x +
          (V x j • a x) * partialDeriv v x j := by
    simp only [← smul_mul_assoc]
    simp only [partialDeriv, fderiv_fun_mul (hB j) (hv.differentiable (by simp) x),
      add_apply, smul_apply, smul_eq_mul]
    ring
  simp only [transportCoefficient, carrierZeroAmplitude, carrierFirstAmplitude, hp,
    Finset.sum_add_distrib, sub_mul, Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]
  ring

/-- The actual carrier derivative, split by the number of derivatives on the
complex output datum (`app:ch_background:prop:bg-adjoint`). This follows from the
phase identity `∂z Φ = V · dₓ Φ`; no differentiated integral is assumed. The
support hypothesis is solely in the measurement variable, uniformly near `s`.
-/
theorem hasDerivAt_chartAdjoint_carrier
    {U : Set ℝ} {S : Set (Euclidean n)}
    (hU : IsOpen U) (hS : IsCompact S)
    {Φ : ℝ × Euclidean n → ℝ} {A : ℝ × Euclidean n → ℂ}
    {V : Euclidean n → Euclidean n} {v : Euclidean n → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hA : ContDiff ℝ ∞ A)
    (hV : ContDiff ℝ ∞ V) (hv : ContDiff ℝ ∞ v)
    (hs : ∀ t ∈ U, tsupport (fun x ↦ A (t, x)) ⊆ S)
    {s : ℝ} (hsU : s ∈ U)
    (hphase : ∀ x, A (s, x) ≠ 0 → deriv (fun t ↦ Φ (t, x)) s =
      fderiv ℝ (fun y ↦ Φ (s, y)) x (V x)) :
    HasDerivAt (fun t ↦ chartAdjoint (fun x ↦ Φ (t, x)) (fun x ↦ A (t, x)) v)
      (∫ x, oscillatoryFactor (-1) (Φ (s, x)) *
        (carrierZeroAmplitude (fun y ↦ deriv (fun t ↦ A (t, y)) s)
            (fun y ↦ A (s, y)) V x * v x +
          ∑ j, carrierFirstAmplitude (fun y ↦ A (s, y)) V j x *
            partialDeriv v x j)) s := by
  have hAv : ContDiff ℝ ∞ (fun p : ℝ × Euclidean n ↦ A p * v p.2) :=
    hA.mul (hv.comp contDiff_snd)
  have hsAv : ∀ t ∈ U, tsupport (fun x ↦ A (t, x) * v x) ⊆ S :=
    fun t ht ↦ tsupport_mul_subset_left.trans (hs t ht)
  have hd := hasDerivAt_compact_transport_on_support hU isOpen_univ hS (subset_univ _)
    hΦ hAv hV.contDiffOn (contDiff_const (c := (1 : ℝ))).contDiffOn hsAv hsU (-1)
    (fun x _ hx ↦ hphase x (fun hz ↦ hx (by simp [hz])))
  have hconst (x : Euclidean n) (j : Fin n) :
      partialDeriv (fun _ : Euclidean n ↦ (1 : ℝ)) x j = 0 := by
    simp [partialDeriv]
  dsimp only at hd
  simp only [one_smul, hconst, zero_smul, Finset.sum_const_zero,
    add_zero, setIntegral_univ] at hd
  have hder (x : Euclidean n) :
      deriv (fun t ↦ A (t, x) * v x) s =
        deriv (fun t ↦ A (t, x)) s * v x :=
    ((hA.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) s).hasDerivAt.mul_const
      (v x) |>.deriv
  simp only [hder] at hd
  apply hd.congr_deriv
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  exact transportCoefficient_mul_datum _ _ _ V
    (hA.comp (contDiff_const.prodMk contDiff_id)) hv hV x

end JanetCartan.ContinuumAdjoint.DerivativeKernels
