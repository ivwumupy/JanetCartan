module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.Conic
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PencilContinuity
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbol.Basic

/-!
# The finite masks for the original coefficient pencil

The frozen characteristic cover supplies fixed masks. Joint continuity of the
literal determinant on a compact coefficient/covector set then constructs a
coefficient radius before any varying field. The complete complementary mask
has a positive determinant gap for every field taking values in that ball.
No scalar-symbol closeness or current characteristic coverage is assumed.

Consumer: the elliptic part of the finite solver in
`app:ch_regular_base:thm:sector` and the complete low/angular complement in
`app:ch_regular_base:prop:complete-residual`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteMasks
open ActualCarriers CompatibleResponse
variable {n : ℕ} {ι : Type*}

/-- On the fixed angular compact, closeness of the original coefficient value
implies uniform closeness of its literal determinant. The radius precedes the
variable field (`app:ch_regular_base:thm:sector`, finite neighborhood). -/
theorem exists_pencil_determinant_neighborhood
    (A₀ : Fin n → MetricTensor n) {K : Set (Euclidean n)} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > (0 : ℝ), ∀ A : Fin n → MetricTensor n, ‖A - A₀‖ ≤ ε →
      ∀ ξ ∈ K, |determinant A ξ - determinant A₀ ξ| < δ := by
  have hc := (isCompact_closedBall A₀ 1).prod hK
  obtain ⟨d, hd, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hc.uniformContinuousOn_of_continuous contDiff_determinant.continuous.continuousOn) δ hδ
  refine ⟨min 1 (d / 2), lt_min zero_lt_one (by positivity), ?_⟩
  intro A hA ξ hξ
  have hAb : A ∈ closedBall A₀ 1 := by
    rw [mem_closedBall, dist_eq_norm]
    exact hA.trans (min_le_left _ _)
  have hdist : dist (A, ξ) (A₀, ξ) < d := by
    simp only [dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self,
      norm_zero, max_eq_left (norm_nonneg _)]
    exact hA.trans_lt ((min_le_right 1 (d / 2)).trans_lt (by linarith : d / 2 < d))
  simpa only [Real.dist_eq] using hclose (A, ξ) ⟨hAb, hξ⟩
    (A₀, ξ) ⟨mem_closedBall_self zero_le_one, hξ⟩ hdist

/-- The actual coefficient pencil supplies the ellipticity and coverage
properties of the fixed masks. All masks, the coefficient radius and the
determinant gap are chosen before the current field, its physical domain and
any accuracy. The given open charts cover only the frozen zeros; no additional
regularity of unprotected directions is used (`sector-theorem-identity`). -/
theorem exists_finite_pencil_masks
    (A₀ : Fin n → MetricTensor n) {K : Set (Euclidean n)} (hK : IsCompact K)
    (O : ι → Set (Euclidean n)) (hO : ∀ i, IsOpen (O i))
    (hcover : ∀ ξ ∈ K, determinant A₀ ξ = 0 → ∃ i, ξ ∈ O i) :
    ∃ (s : Finset ι) (χ : s → Euclidean n → ℝ),
      ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ i ξ, χ i ξ ∈ Icc (0 : ℝ) 1) ∧
      (∀ i, HasCompactSupport (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆ O i) ∧
      (∀ ξ, ∑ i, χ i ξ ≤ 1) ∧
      (∀ (Q : Euclidean n → Fin n → MetricTensor n) (X : Set (Euclidean n)),
        (∀ x ∈ X, ‖Q x - A₀‖ ≤ ε) →
        (∀ x ∈ X, ∀ ξ ∈ K ∩ tsupport (fun η ↦ 1 - ∑ i, χ i η),
          δ ≤ |determinant (Q x) ξ|) ∧
        (∀ x ∈ X, ∀ ξ ∈ K, determinant (Q x) ξ = 0 →
          ξ ∈ interior {η | ∑ i, χ i η = 1})) := by
  have hf : Continuous (determinant A₀) :=
    contDiff_determinant.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨s, χ, δ, hδ, hsmooth, hrange, hcompact, hsupp, hsum, hstable⟩ :=
    exists_finite_characteristic_masks hK hf.continuousOn O hO hcover
  obtain ⟨ε, hε, he⟩ := exists_pencil_determinant_neighborhood A₀ hK hδ
  refine ⟨s, χ, ε, hε, δ, hδ, hsmooth, hrange, hcompact, hsupp, hsum, ?_⟩
  intro Q X hQ
  exact ⟨fun x hx ↦ (hstable (determinant (Q x)) (he (Q x) (hQ x hx))).1,
    fun x hx ↦ (hstable (determinant (Q x)) (he (Q x) (hQ x hx))).2⟩

/-- The complementary normalized gap has its exact degree-dependent radial
power on every positive ray. This is the actual off-characteristic inverse
region; the low-frequency term is still retained separately
(`app:ch_regular_base:prop:complete-residual`). -/
theorem determinant_gap_on_conic_complement
    {κ : Type*} [Fintype κ] (χ : κ → Euclidean n → ℝ)
    (A : Fin n → MetricTensor n) {K : Set (Euclidean n)} {δ : ℝ}
    (hgap : ∀ η ∈ K ∩ tsupport (fun η ↦ 1 - ∑ i, χ i η),
      δ ≤ |determinant A η|)
    {ξ : Euclidean n} (hξ : NormedSpace.normalize ξ ∈ K)
    (hs : ξ ∈ tsupport (conicMask (fun η ↦ 1 - ∑ i, χ i η))) :
    δ * ‖ξ‖ ^ n ≤ |determinant A ξ| := by
  have h := hgap _ ⟨hξ, (conicMask_tsupport_subset _ hs).2⟩
  have he : determinant A ξ = ‖ξ‖ ^ n * determinant A (NormedSpace.normalize ξ) := by
    conv_lhs => rw [← NormedSpace.norm_smul_normalize ξ]
    exact determinant_smul _ _ _
  rw [he, abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left h (pow_nonneg (norm_nonneg ξ) n)

end JanetCartan.RegularSector.FiniteMasks
