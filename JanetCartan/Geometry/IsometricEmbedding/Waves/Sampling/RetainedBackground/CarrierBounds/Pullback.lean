module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.CarrierBounds.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.PullbackGrades

/-!
# Joint budgets through the retained carrier substitution

Compact fixed geometry and the actual supported tensor give all joint jets,
including derivatives of the prescribed sampling weight. The concrete retained
polynomial is inserted in `CarrierBounds`; these transfer lemmas do not assume
any derivative bound for its carrier pullback.
Consumer: `app:ch_waves:eq:background-quadrature` and its physical rough bound.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.RetainedBackground
open ActualCarriers FrozenMenu CurrentFullPhase MeasuredAmplitude
open RawPrimary.AmplitudeGrades.Polynomial RawPrimary.SliceBounds
open FourierIntegral.NormalOneHigh

/-- The fixed carrier graph and original smooth sampling weight preserve the
full reserve. The graph jets are proved by compactness and smoothness of the
actual extension. No resulting carrier bound is an input. The only tensor
inputs are supplied by `exists_retained_supportedBackground_budgets`
(`app:ch_waves:eq:background-quadrature`,
`app:ch_waves:eq:background-quadrature-rough`). -/
theorem exists_retainedCarrierPullback_budgets
    {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    (χ : Euclidean (m + 1) → ℝ)
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧
      ∀ (H : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ),
      ContDiff ℝ ∞ (supportedJointTensor a hρ χ H) →
      ∀ (L : ℝ) (rpar : ℕ), 1 ≤ L →
      (∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w, ∀ j,
        ‖iteratedFDeriv ℝ j (supportedJointTensor a hρ χ H) (τ, w)‖ ≤
          A j * L ^ (j - rpar)) →
      let f := fun q : ℝ × (SeparatedSampling.Point × Euclidean (m + 1)) ↦
        retainedCarrierPullback T a hρ χ H q.1 q.2.1 q.2.2
      ContDiff ℝ ∞ f ∧
      ContDiff ℝ ∞ (fun q ↦ ψ q.2.1 • f q) ∧
      ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x j,
        ‖iteratedFDeriv ℝ j f (τ, (z, x))‖ ≤ B j * L ^ (j - rpar) ∧
        ‖iteratedFDeriv ℝ j (fun q ↦ ψ q.2.1 • f q) (τ, (z, x))‖ ≤
          B j * L ^ (j - rpar) := by
  let S := Icc (-1 : ℝ) 1 ×ˢ retainedCarrierSupport a (ρ := ρ)
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_retainedCarrierSupport a)
  let g := retainedCarrierPoint T a hρ
  have hg : ContDiff ℝ ∞ g := contDiff_retainedCarrierPoint T a hρ hP hcarrier
  let mask := fun q : ℝ × (SeparatedSampling.Point × Euclidean (m + 1)) ↦ ψ q.2.1
  have hm : ContDiff ℝ ∞ mask := hψ.comp (contDiff_fst.comp contDiff_snd)
  let b := fun j ↦ cNorm S j g
  let d := fun j ↦ cNorm S j mask
  have hb (j) : 0 ≤ b j := cNorm_nonneg _ _ _
  have hd (j) : 0 ≤ d j := cNorm_nonneg _ _ _
  let D := compositionBudget A b
  have hD : ∀ j, 0 ≤ D j := compositionBudget_nonneg hA hb
  let M := ContinuousLinearMap.lsmul ℝ ℝ (E := Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
  let W := productProfile M d D
  have hW : ∀ j, 0 ≤ W j := productProfile_nonneg M hd hD
  refine ⟨fun j ↦ 1 + D j + W j, fun j ↦ by linarith [hD j, hW j], ?_⟩
  intro H hH L rpar hL hjet f
  have hf : ContDiff ℝ ∞ f := hH.comp hg
  refine ⟨hf, hm.smul hf, ?_⟩
  intro τ hτ z x j
  let q : ℝ × (SeparatedSampling.Point × Euclidean (m + 1)) := (τ, (z, x))
  have hpow : 0 ≤ L ^ (j - rpar) := pow_nonneg (zero_le_one.trans hL) _
  by_cases hq : (z, x) ∈ retainedCarrierSupport a (ρ := ρ)
  · have hqS : q ∈ S := ⟨hτ, hq⟩
    have hj (k : ℕ) : ‖iteratedFDeriv ℝ k f q‖ ≤ D k * L ^ (k - rpar) := by
      exact norm_iteratedFDeriv_comp_le_sliceGrade hg.contDiffAt hH.contDiffAt
        (fun i _ ↦ hA i) hL (fun i _ ↦ hjet τ hτ _ i)
        (fun i _ _ ↦ norm_iteratedFDeriv_le_cNorm hS (hg.of_le (by simp)) hqS le_rfl)
    have hmj (k : ℕ) : ‖iteratedFDeriv ℝ k mask q‖ ≤ d k * L ^ (k - rpar) :=
      (norm_iteratedFDeriv_le_cNorm hS (hm.of_le (by simp)) hqS le_rfl).trans
        (le_mul_of_one_le_right (hd k) (one_le_pow₀ hL))
    have hwj := jet_bilinear_le M isOpen_univ hm.contDiffOn hf.contDiffOn
      (mem_univ q) hL hd hD hmj hj j
    exact ⟨(hj j).trans (mul_le_mul_of_nonneg_right (by linarith [hW j]) hpow),
      hwj.trans (mul_le_mul_of_nonneg_right (by linarith [hD j]) hpow)⟩
  · have hz : f =ᶠ[𝓝 q] 0 :=
      retainedCarrierPullback_eventuallyEq_zero T a hρ hP hcarrier χ H hq
    have hwz : (fun p ↦ mask p • f p) =ᶠ[𝓝 q] 0 := by
      filter_upwards [hz] with p hp
      simp only [hp, Pi.zero_apply, smul_zero]
    rw [(hz.iteratedFDeriv ℝ j).eq_of_nhds,
      (hwz.iteratedFDeriv ℝ j).eq_of_nhds]
    simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
    constructor <;> exact mul_nonneg (by linarith [hD j, hW j]) hpow

end JanetCartan.Sampling.RetainedBackground
