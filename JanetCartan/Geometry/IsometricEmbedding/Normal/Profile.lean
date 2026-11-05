module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Assembly
public import JanetCartan.Analysis.ContDiff.Norm.JointBudget

/-!
# Fixed-shift profiles for geometric coefficients

On positive-radius closed balls, this module proves one-high estimates and
profile transfer for the actual metric, inverse metric, second fundamental
form, stress projector and frame, inverse stress Gram matrix, reduced-operator
coefficients, normal completion, and reconstruction. A compact second-jet
range in the cube-reference neighborhood supplies every geometric rank and
Gram condition. Scalar interpolation is discharged, and all coefficients use
one common reserve of two, independent of differentiation order.

`Assembly` gives the combined estimate for
`app:ch_background:eq:bg-frame-tame` and the geometric reconstruction part of
`app:ch_waves:eq:joint-tame`. The latter source statement also contains phase
and transported-amplitude estimates, which belong to the leading-wave task.
The general compact-domain interpolation-conditional variants remain explicit.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.GeometricProfile

/-- `app:cor:fixed-profile-transfer`, applied to the actual metric coefficients in
`app:ch_background:eq:bg-frame-tame`: one fixed reserve of two transfers the map profile
to its metric and inverse metric. Constants precede the map, scale, and baseline orders.
The scalar interpolation input is explicit; no geometric coefficient estimate is assumed. -/
theorem exists_metric_and_inverse_profiles_of_interpolation
    {n N : ℕ} {s : Set (Euclidean n)}
    {t : Set (Euclidean n →L[ℝ] Euclidean N)} (hs : IsCompact s) (ht : IsCompact t)
    (htinv : ∀ L ∈ t, IsUnit (firstJetMetric L)) {M : ℝ} (hM : 0 ≤ M)
    (hinterp : ∀ k j, 0 < j → j < k → ∃ C : ℝ, 0 < C ∧
      ∀ u : Euclidean n → (Euclidean n →L[ℝ] Euclidean N), ContDiff ℝ ∞ u →
        cNorm s j u ≤ C * (cNorm s 0 u) ^ (1 - (j : ℝ) / k) *
          (cNorm s k u) ^ ((j : ℝ) / k)) :
    ∃ C : ℕ → ℝ, (∀ r, 0 < C r) ∧
      ∀ (f : Euclidean n → Euclidean N), ContDiff ℝ ∞ f →
      Set.MapsTo (fderiv ℝ f) s t → cNorm s 1 f ≤ M →
      ∀ (R ν : ℕ) (T : ℝ) (A : ℕ → ℝ),
      HasDerivativeProfile s f R T A → 1 ≤ T → (∀ r, 0 ≤ A r) → 2 + ν ≤ R →
        HasDerivativeProfile s (inducedMetric f) ν T (fun r ↦ C r * (1 + A (r + 2))) ∧
        HasDerivativeProfile s (fun x ↦ (inducedMetric f x)⁻¹) ν T
          (fun r ↦ C r * (1 + A (r + 2))) := by
  have hbound := fun r ↦ exists_cNorm_metric_and_inverse_le_of_interpolation hs ht htinv r hM
    (by simpa only [Nat.cast_add, Nat.cast_one] using hinterp (r + 1))
  choose C hC hCf using hbound
  refine ⟨C, hC, ?_⟩
  intro f hf hft hfM R ν T A hp hT hA hloss
  constructor
  · apply hp.transfer hT hA (fun r ↦ (hC r).le) hloss
    intro r
    exact (le_add_of_nonneg_right (cNorm_nonneg s r (fun x ↦ (inducedMetric f x)⁻¹))).trans
      (hCf r f hf hft hfM)
  · apply hp.transfer hT hA (fun r ↦ (hC r).le) hloss
    intro r
    exact (le_add_of_nonneg_left (cNorm_nonneg s r (inducedMetric f))).trans
      (hCf r f hf hft hfM)

/-- `app:cor:fixed-profile-transfer` and `app:ch_background:eq:bg-frame-tame`:
profiles of the actual metric and its inverse on a closed ball, with a single
reserve of one and no undischarged scalar interpolation premise. -/
theorem exists_metric_and_inverse_profiles_closedBall
    {n N : ℕ} (x : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (Euclidean n →L[ℝ] Euclidean N)} (ht : IsCompact t)
    (htinv : ∀ L ∈ t, IsUnit (firstJetMetric L)) :
    ∃ C : ℕ → ℝ, (∀ r, 0 < C r) ∧
      ∀ f : Euclidean n → Euclidean N, ContDiff ℝ ∞ f →
      Set.MapsTo (fderiv ℝ f) (Metric.closedBall x ρ) t →
      ∀ (R ν : ℕ) (T : ℝ) (A : ℕ → ℝ),
      HasDerivativeProfile (Metric.closedBall x ρ) f R T A →
      1 ≤ T → (∀ r, 0 ≤ A r) → 1 + ν ≤ R →
        HasDerivativeProfile (Metric.closedBall x ρ) (inducedMetric f) ν T
          (fun r ↦ C r * (1 + A (r + 1))) ∧
        HasDerivativeProfile (Metric.closedBall x ρ) (fun y ↦ (inducedMetric f y)⁻¹) ν T
          (fun r ↦ C r * (1 + A (r + 1))) := by
  have hbound := exists_cNorm_metric_and_inverse_le_closedBall x hρ ht htinv
  choose C hC hCf using hbound
  refine ⟨C, hC, ?_⟩
  intro f hf hft R ν T A hp hT hA hloss
  constructor
  · apply hp.transfer hT hA (fun r ↦ (hC r).le) hloss
    intro r
    exact (le_add_of_nonneg_right (cNorm_nonneg _ r (fun y ↦ (inducedMetric f y)⁻¹))).trans
      (hCf r f hf hft)
  · apply hp.transfer hT hA (fun r ↦ (hC r).le) hloss
    intro r
    exact (le_add_of_nonneg_left (cNorm_nonneg _ r (inducedMetric f))).trans
      (hCf r f hf hft)

/-- `app:cor:fixed-profile-transfer` and `app:ch_background:eq:bg-frame-tame`:
profiles of each actual second-form coefficient use the fixed reserve two.
The only geometric restriction is the compact immersive second-jet range. -/
theorem exists_secondFundamentalForm_profiles_closedBall
    {n N : ℕ} (x : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    {t : Set (SecondJet (Euclidean n) (Euclidean N))} (ht : IsCompact t)
    (htimm : ∀ J ∈ t, Function.Injective J.1) (i j : Fin n) :
    ∃ C : ℕ → ℝ, (∀ r, 0 < C r) ∧
      ∀ f : Euclidean n → Euclidean N, ContDiff ℝ ∞ f →
      Set.MapsTo (secondJet f) (Metric.closedBall x ρ) t →
      ∀ (R ν : ℕ) (T : ℝ) (A : ℕ → ℝ),
      HasDerivativeProfile (Metric.closedBall x ρ) f R T A →
      1 ≤ T → (∀ r, 0 ≤ A r) → 2 + ν ≤ R →
        HasDerivativeProfile (Metric.closedBall x ρ)
          (fun y ↦ secondFundamentalForm f y i j) ν T
          (fun r ↦ C r * (1 + A (r + 2))) := by
  have hbound := fun r ↦ exists_cNorm_secondFundamentalForm_le_closedBall x hρ ht htimm r i j
  choose C hC hCf using hbound
  refine ⟨C, hC, ?_⟩
  intro f hf hft R ν T A hp hT hA hloss
  exact hp.transfer hT hA (fun r ↦ (hC r).le) hloss (fun r ↦ hCf r f hf hft)

end JanetCartan.GeometricProfile
