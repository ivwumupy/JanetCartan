module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.NormalizedPullback

/-!
# The original masks on the normalized measured polynomial

The normalized angular/high-pass masks have exactly three profiles. Their
joint multiplication with the fixed carrier weight therefore has bounds
independent of the band count. Combined with the literal WKB substitution,
this preserves all retained joint grades and the common zero endpoint.
Consumer: the actual amplitude jets in `app:ch_waves:setup:oscillatory`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open RawKernel FullNormalGeometry FullNormalGeometry.PhaseJets
open MeanNormalBound.NormalizedFullPhase ContinuumRow ContinuumRow.CanonicalConic
open RawPrimary.MaskProfiles RawPrimary.SliceBounds FourierIntegral.NormalOneHigh

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The original carrier weight and normalized half-weighted smooth band.
The sharp annular Hilbert refinements do not enter this function
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def normalizedRetainedMask (ψ : SeparatedSampling.Point → ℝ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (j : ℕ) (q : ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) : ℂ :=
  (ψ (carrierSamplingEquiv ((inputCoordinates T q.2.2.2).1, q.2.1)) : ℂ) *
    normalizedMask (n := m + 1) angular highPass j (inputCoordinates T q.2.2.2).2

/-- Smoothness includes incidence, both spectators, and epsilon. The
high-pass transition is unchanged (`app:ch_waves:setup:oscillatory`). -/
theorem contDiff_normalizedRetainedMask
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hH : ContDiff ℝ ∞ highPass) (j : ℕ) :
    ContDiff ℝ ∞ (normalizedRetainedMask T ψ angular highPass j) := by
  have hc : ContDiff ℝ ∞ (fun q : ℝ ×
      (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1))) ↦
      carrierSamplingEquiv ((inputCoordinates T q.2.2.2).1, q.2.1)) := by
    have heq (s : ℝ) (v : Euclidean 2) :
        carrierSamplingEquiv (s, v) = (carrierParameters (v, s)).ofLp := by
      rw [carrierParameters_eq_sampling]
    simp only [heq]
    exact PiLp.contDiff_ofLp.comp (by fun_prop)
  exact (Complex.ofRealCLM.contDiff.comp (hψ.comp hc)).mul
    ((contDiff_normalizedMask angular highPass ha hH j).comp (by fun_prop))

/-- One finite geometric mask budget for every band label. The constants
are chosen before all raw fields and frequencies, using the proved three
profiles (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_normalizedRetainedMask_budgets
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    (hH : ContDiff ℝ ∞ highPass) (hH₁ : ∀ η, 2 ≤ ‖η‖ → highPass η = 1)
    {S : Set (ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1))))}
    (hS : IsCompact S) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧ ∀ j, ∀ q ∈ S, ∀ k,
      ‖iteratedFDeriv ℝ k (normalizedRetainedMask T ψ angular highPass j) q‖ ≤ B k := by
  let A (j k : ℕ) := cNorm S k (normalizedRetainedMask T ψ angular highPass j)
  have hA (j k : ℕ) : 0 ≤ A j k := cNorm_nonneg _ _ _
  refine ⟨fun k ↦ ∑ i ∈ Finset.range 3, A i k,
    fun k ↦ Finset.sum_nonneg (fun i _ ↦ hA i k), ?_⟩
  intro j q hq k
  have heq : normalizedRetainedMask T ψ angular highPass j =
      normalizedRetainedMask T ψ angular highPass (min j 2) := by
    funext w
    unfold normalizedRetainedMask
    rw [normalizedMask_eq_min angular highPass hah hH₁ j]
  rw [heq]
  exact (norm_iteratedFDeriv_le_cNorm hS
    ((contDiff_normalizedRetainedMask T ψ hψ angular highPass ha hH _).of_le (by simp)) hq le_rfl).trans
      (Finset.single_le_sum (fun i _ ↦ hA i k) (Finset.mem_range.mpr (by omega)))

/-- The literal masked substitution for a retained measured polynomial.
Only the smooth wide band is used here (`app:ch_waves:setup:oscillatory`). -/
def normalizedMeasuredPullback (ψ : SeparatedSampling.Point → ℝ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (f : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
      EuclideanSpace ℂ (Fin (m + 1)))
    (j : ℕ) (q : ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) :
    EuclideanSpace ℂ (Fin (m + 1)) :=
  normalizedRetainedMask T ψ angular highPass j q •
    f (normalizedRetainedPoint T ((2 : ℝ) ^ j)⁻¹ q)

/-- Full joint grades for the original masks times the literal pullback.
The supplied raw bounds are precisely the already proved globally supported
polynomial bounds; every substitution and mask constant is constructed here.
This is the analytic connection used below on the actual polynomial, not an
assumed normal-operator bound (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_normalizedMeasuredPullback_budgets
    {c C : ℝ} (hP : P.IsValid c C) (M : ℝ) {e : ℝ} (he : e ≤ 1)
    {H : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))}
    (hH : IsCompact H) (hHM : H ⊆ tripleDomain T M)
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    (hhigh : ContDiff ℝ ∞ highPass) (hhigh₁ : ∀ η, 2 ≤ ‖η‖ → highPass η = 1)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧
      ∀ (f : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
        EuclideanSpace ℂ (Fin (m + 1))), ContDiff ℝ ∞ f →
      ∀ (L : ℝ) (rpar : ℕ), 1 ≤ L →
      (∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w, ∀ k,
        ‖iteratedFDeriv ℝ k f (τ, w)‖ ≤ A k * L ^ (k - rpar)) →
      ∀ j,
        ContDiffOn ℝ ∞ (normalizedMeasuredPullback T ψ angular highPass f j)
          (univ ×ˢ tripleDomain T M) ∧
        ∀ q ∈ Icc (-e) e ×ˢ H, ∀ k,
          ‖iteratedFDeriv ℝ k (normalizedMeasuredPullback T ψ angular highPass f j) q‖ ≤
            B k * L ^ (k - rpar) := by
  obtain ⟨b, hb, hcomp⟩ := exists_normalizedRetainedPoint_composition_budgets T hP M he
    hH hHM A hA
  obtain ⟨d, hd, hmask⟩ := exists_normalizedRetainedMask_budgets T ψ hψ angular highPass
    ha hah hhigh hhigh₁ (S := Icc (-e) e ×ˢ H) (isCompact_Icc.prod hH)
  refine ⟨sliceMaskJetConstant d b, sliceMaskJetConstant_nonneg hd hb, ?_⟩
  intro f hf L rpar hL hfjet j
  have hs : ContDiffOn ℝ ∞ (f ∘ normalizedRetainedPoint T ((2 : ℝ) ^ j)⁻¹)
      (univ ×ˢ tripleDomain T M) := hf.comp_contDiffOn
    ((normalizedRetainedPoint_smooth T hP M).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun q hq ↦ ⟨mem_univ _, hq⟩))
  have hm : ContDiffOn ℝ ∞ (normalizedRetainedMask T ψ angular highPass j)
      (univ ×ˢ tripleDomain T M) :=
    (contDiff_normalizedRetainedMask T ψ hψ angular highPass ha hhigh j).contDiffOn
  refine ⟨hm.smul hs, ?_⟩
  intro q hq k
  exact norm_iteratedFDeriv_mask_smul_le_sliceGrade
    (isOpen_univ.prod (isOpen_tripleDomain T M)) hm hs ⟨mem_univ _, hHM hq.2⟩
    hL (fun i _ ↦ hd i) (fun i _ ↦ hb i)
    (fun i _ ↦ hmask j q hq i) (fun i _ ↦ hcomp f hf L rpar hL hfjet j q hq i)

end JanetCartan.Sampling.MeasuredAmplitude
