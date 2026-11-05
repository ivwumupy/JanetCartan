module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.JetComposition
public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import JanetCartan.Analysis.Matrix.InverseBounds
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Bounds for the actual metric and inverse metric

First-jet formulas for `app:ch_background:eq:bg-frame-tame` and
`app:ch_waves:eq:joint-tame`. A compact set of nonsingular first jets supplies
all inverse gaps. The polynomial estimate follows directly from the chain rule;
the general compact-domain one-high estimate keeps scalar interpolation explicit.
On closed balls, proved interpolation removes that premise and yields shift one.
The second form is treated in `Profile.SecondForm`.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.GeometricProfile

private def metricTensorOfEntries (n : ℕ) : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
  { LinearMap.id with cont := continuous_id }

/-- `app:ch_background:eq:bg-frame-tame`: the actual Gram metric as a function of
the first jet, in the Frobenius matrix norm. -/
def firstJetMetric {n N : ℕ} (L : Euclidean n →L[ℝ] Euclidean N) : MetricTensor n :=
  fun i j ↦ inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))

/-- `app:ch_background:eq:bg-frame-tame`: the metric is a smooth quadratic jet formula. -/
theorem contDiff_firstJetMetric {n N : ℕ} :
    ContDiff ℝ ∞ (@firstJetMetric n N) := by
  apply (metricTensorOfEntries n).contDiff.comp
  exact contDiff_pi.mpr fun i ↦ contDiff_pi.mpr fun j ↦
    (contDiff_id.clm_apply contDiff_const).inner ℝ (contDiff_id.clm_apply contDiff_const)

/-- `app:ch_background:eq:bg-frame-tame`: the jet formula agrees with the existing
induced metric, without any additional geometric hypothesis. -/
theorem inducedMetric_eq_firstJetMetric_comp {n N : ℕ} (f : Euclidean n → Euclidean N) :
    inducedMetric f = firstJetMetric ∘ fderiv ℝ f := rfl

/-- `app:ch_background:eq:bg-frame-tame`: inverse-metric coefficients are smooth
on the open nonsingular first-jet domain. -/
theorem contDiffAt_firstJetMetric_inv {n N : ℕ}
    {L : Euclidean n →L[ℝ] Euclidean N} (hL : IsUnit (firstJetMetric L)) :
    ContDiffAt ℝ ∞ (fun J ↦ (firstJetMetric J)⁻¹) L := by
  have hopen : IsOpen {J : Euclidean n →L[ℝ] Euclidean N | IsUnit (firstJetMetric J)} :=
    Units.isOpen.preimage contDiff_firstJetMetric.continuous
  exact (contDiffOn_matrix_inv contDiff_firstJetMetric.contDiffOn
    (fun _ hJ ↦ hJ)).contDiffAt (hopen.mem_nhds hL)

/-- `app:ch_background:eq:bg-frame-tame`: an unconditional finite-order polynomial
bound for the actual metric and inverse metric. Compact nonsingular first jets provide
the low-order gap; the coefficient norms on that compact set are independent of the map.
This polynomial bound alone is not the manuscript's one-high tame estimate. -/
theorem cNorm_metric_and_inverse_le_polynomial
    {n N : ℕ} {s : Set (Euclidean n)}
    {t : Set (Euclidean n →L[ℝ] Euclidean N)} (hs : IsCompact s) (ht : IsCompact t)
    (htinv : ∀ L ∈ t, IsUnit (firstJetMetric L))
    {r : ℕ} {f : Euclidean n → Euclidean N} (hf : ContDiff ℝ (r + 1) f)
    (hft : Set.MapsTo (fderiv ℝ f) s t) :
    cNorm s r (inducedMetric f) + cNorm s r (fun x ↦ (inducedMetric f x)⁻¹) ≤
      compositionMultiplicity r *
        (cNorm t r firstJetMetric + cNorm t r (fun J ↦ (firstJetMetric J)⁻¹)) *
          (1 + cNorm s (r + 1) f) ^ r := by
  have h₁ := cNorm_firstJet_comp_le_polynomial hs ht
    (fun L _ ↦ (contDiff_firstJetMetric.of_le (by simp : (r : ℕ∞ω) ≤ ∞)).contDiffAt) hf hft
  have h₂ := cNorm_firstJet_comp_le_polynomial hs ht
    (fun L hL ↦ (contDiffAt_firstJetMetric_inv (htinv L hL)).of_le
      (by simp : (r : ℕ∞ω) ≤ ∞)) hf hft
  simpa only [← add_mul, ← mul_add, inducedMetric_eq_firstJetMetric_comp, Function.comp_def]
    using add_le_add h₁ h₂

/-- `app:ch_background:eq:bg-frame-tame` and `app:ch_waves:eq:joint-tame`: the actual
metric and inverse metric admit one high map norm with the fixed shift two. The
constant is uniform over maps with the given compact jet range and low bound.
This general compact-domain variant retains precisely the displayed scalar
interpolation premise; the closed-ball theorem below discharges it. -/
theorem exists_cNorm_metric_and_inverse_le_of_interpolation
    {n N : ℕ} {s : Set (Euclidean n)}
    {t : Set (Euclidean n →L[ℝ] Euclidean N)} (hs : IsCompact s) (ht : IsCompact t)
    (htinv : ∀ L ∈ t, IsUnit (firstJetMetric L))
    (r : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hinterp : ∀ j, 0 < j → j < r + 1 → ∃ C : ℝ, 0 < C ∧
      ∀ u : Euclidean n → (Euclidean n →L[ℝ] Euclidean N), ContDiff ℝ ∞ u →
        cNorm s j u ≤ C * (cNorm s 0 u) ^ (1 - (j : ℝ) / (r + 1)) *
          (cNorm s (r + 1) u) ^ ((j : ℝ) / (r + 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Euclidean n → Euclidean N, ContDiff ℝ ∞ f →
      Set.MapsTo (fderiv ℝ f) s t → cNorm s 1 f ≤ M →
        cNorm s r (inducedMetric f) + cNorm s r (fun x ↦ (inducedMetric f x)⁻¹) ≤
          C * (1 + cNorm s (r + 2) f) := by
  have hI : ∀ j, 0 < j → j < r + 1 → ∃ C : ℝ, 0 < C ∧
      ∀ u : Euclidean n → (Euclidean n →L[ℝ] Euclidean N), ContDiff ℝ ∞ u →
        cNorm s j u ≤ C * (cNorm s 0 u) ^ (1 - (j : ℝ) / (r + 1 : ℕ)) *
          (cNorm s (r + 1) u) ^ ((j : ℝ) / (r + 1 : ℕ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hinterp
  obtain ⟨C₁, hC₁, h₁⟩ := exists_cNorm_firstJet_comp_le_of_interpolation hs ht
    (Nat.succ_pos r) (Nat.le_succ r)
    (fun L _ ↦ (contDiff_firstJetMetric.of_le (by simp : (r : ℕ∞ω) ≤ ∞)).contDiffAt)
    hM hI
  obtain ⟨C₂, hC₂, h₂⟩ := exists_cNorm_firstJet_comp_le_of_interpolation hs ht
    (Nat.succ_pos r) (Nat.le_succ r)
    (fun L hL ↦ (contDiffAt_firstJetMetric_inv (htinv L hL)).of_le
      (by simp : (r : ℕ∞ω) ≤ ∞)) hM hI
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro f hf hft hfM
  simpa only [← add_mul, inducedMetric_eq_firstJetMetric_comp, Function.comp_def, Nat.succ_eq_add_one,
    Nat.add_assoc] using add_le_add (h₁ f hf hft hfM) (h₂ f hf hft hfM)

/-- `app:ch_background:eq:bg-frame-tame`: unconditional one-high estimates for
the actual metric and inverse metric on a closed ball. Compact nonsingular
first jets supply the inverse gap and low bound. The derivative loss is one. -/
theorem exists_cNorm_metric_and_inverse_le_closedBall
    {n N : ℕ} (x : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (Euclidean n →L[ℝ] Euclidean N)} (ht : IsCompact t)
    (htinv : ∀ L ∈ t, IsUnit (firstJetMetric L)) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Euclidean n → Euclidean N, ContDiff ℝ ∞ f →
      Set.MapsTo (fderiv ℝ f) (Metric.closedBall x ρ) t →
        cNorm (Metric.closedBall x ρ) r (inducedMetric f) +
          cNorm (Metric.closedBall x ρ) r (fun y ↦ (inducedMetric f y)⁻¹) ≤
            C * (1 + cNorm (Metric.closedBall x ρ) (r + 1) f) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_cNorm_firstJet_comp_le_closedBall x hρ ht
    (fun L _ ↦ (contDiff_firstJetMetric.of_le (by simp : (r : ℕ∞ω) ≤ ∞)).contDiffAt)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_cNorm_firstJet_comp_le_closedBall x hρ ht
    (fun L hL ↦ (contDiffAt_firstJetMetric_inv (htinv L hL)).of_le
      (by simp : (r : ℕ∞ω) ≤ ∞))
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, fun f hf hft ↦ ?_⟩
  simpa only [← add_mul, inducedMetric_eq_firstJetMetric_comp, Function.comp_def]
    using add_le_add (h₁ f hf hft) (h₂ f hf hft)

end JanetCartan.GeometricProfile
