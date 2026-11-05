module

public import JanetCartan.Analysis.Sobolev.Local.Comparison.SmoothBounds.Integrability
public import JanetCartan.Analysis.Microlocal.Localization.Source

/-!
# Sobolev bounds for the inward ball smoother

This is the fixed-support step in
`app:ch_regular_base:eq:ball-extension-sobolev` of `paper-v2.tex`.
The Sobolev norm is the existing Cartesian norm of Section 3.1, with each
multiindex counted once. Smoothness and the fixed support prove actual `L²`
membership of the jets; the existing finite-support squared-integral bound
then gives the estimate. The final profile is fixed before the output, scale,
and input size. Its consumer supplies the actual kernel and cutoff derivative
bounds with input size `‖f‖_{C⁰}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.BallSmoothing

open LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem memLp_cartesian_jet
    {u : E → F} (hu : ContDiff ℝ ∞ u) (hs : HasCompactSupport u)
    (α : Fin n → ℕ) :
    MemLp (cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j u) α) 2 volume := by
  have hJ := memLp_iteratedFDeriv_of_contDiff_hasCompactSupport hu hs (∑ i, α i)
  simpa only [Measure.restrict_univ] using
    memLp_cartesianJetDerivative (U := univ) α (by
      simpa only [Measure.restrict_univ] using hJ)

private theorem support_cartesian_jet_subset
    (u : E → F) (α : Fin n → ℕ) :
    Function.support (cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j u) α) ⊆
      tsupport u := by
  intro x hx
  apply support_iteratedFDeriv_subset (𝕜 := ℝ) (f := u) (sobolevDerivativeList α).length
  intro hz
  apply hx
  simp only [cartesianJetDerivative, hz, zero_apply]

/-- A common bound for the actual output jets through order `r` bounds its
Cartesian Sobolev norm by the square root of the number of multiindices times
the support volume. This is the fixed-support conversion in
`app:ch_regular_base:eq:ball-extension-sobolev`. -/
theorem cartesianJetNorm_le_of_compact_jet_bound
    {K : Set E} (hK : IsCompact K) (r : ℕ)
    {u : E → F} (hu : ContDiff ℝ ∞ u) (hs : tsupport u ⊆ K)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤ B) :
    cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j u) ≤
      Real.sqrt ((sobolevMultiindices n r).card * volume.real K) * B := by
  have hus : HasCompactSupport u := hK.of_isClosed_subset (isClosed_tsupport u) hs
  have henergy : cartesianJetEnergy univ r (fun j ↦ iteratedFDeriv ℝ j u) ≤
      ((sobolevMultiindices n r).card : ℝ) * volume.real K * B ^ 2 := by
    unfold cartesianJetEnergy
    calc
      _ ≤ ∑ _α ∈ sobolevMultiindices n r, B ^ 2 * volume.real K := by
        apply Finset.sum_le_sum
        intro α hα
        have horder : ∑ i, α (some i) ≤ r := by
          have := mem_sobolevMultiindices.mp hα
          omega
        have hcart := memLp_cartesian_jet hu hus (fun i ↦ α (some i))
        simpa only [Measure.restrict_univ] using
          Localization.integral_norm_sq_le_of_bounded_support hK.measurableSet
            hK.measure_ne_top hcart.aestronglyMeasurable
            ((support_cartesian_jet_subset u (fun i ↦ α (some i))).trans hs)
            (fun x ↦ (norm_cartesianJetDerivative_le
              (fun j ↦ iteratedFDeriv ℝ j u) (fun i ↦ α (some i)) x).trans
                (hb _ horder x))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  change Real.sqrt (cartesianJetEnergy univ r (fun j ↦ iteratedFDeriv ℝ j u)) ≤ _
  apply (Real.sqrt_le_sqrt henergy).trans_eq
  rw [Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg), Real.sqrt_sq hB]

/-- The scale profile needed by the actual inward smoother in
`app:ch_regular_base:eq:ball-extension-sobolev`. Its constants depend only on
the fixed compact output support, dimension, order, and supplied derivative
profile. Every derivative and Cartesian energy integral in the conclusion is
genuinely integrable. No derivative bound on the input is assumed: the actual
construction takes `M` to be its input's `C⁰` norm. -/
theorem exists_cartesianSobolev_profile_of_fixed_support
    {K : Set E} (hK : IsCompact K) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) :
    ∃ C : ℕ → ℝ, (∀ r, 0 ≤ C r) ∧
      ∀ (r : ℕ) (R M : ℝ) (u : E → F), 1 ≤ R → 0 ≤ M →
        ContDiff ℝ ∞ u → tsupport u ⊆ K →
        (∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤ B j * R ^ j * M) →
        (∀ j ≤ r, MemLp (iteratedFDeriv ℝ j u) 2 volume) ∧
        (∀ α ∈ sobolevMultiindices n r,
          Integrable (fun x ↦ ‖cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j u)
            (fun i ↦ α (some i)) x‖ ^ 2) volume) ∧
        cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j u) ≤ C r * R ^ r * M := by
  let C (r : ℕ) := Real.sqrt ((sobolevMultiindices n r).card * volume.real K) *
    ∑ j ∈ Finset.range (r + 1), B j
  have hsum (r : ℕ) : 0 ≤ ∑ j ∈ Finset.range (r + 1), B j :=
    Finset.sum_nonneg (fun j _ ↦ hB j)
  refine ⟨C, fun r ↦ mul_nonneg (Real.sqrt_nonneg _) (hsum r), ?_⟩
  intro r R M u hR hM hu hs hb
  have hus : HasCompactSupport u := hK.of_isClosed_subset (isClosed_tsupport u) hs
  refine ⟨fun j _ ↦ memLp_iteratedFDeriv_of_contDiff_hasCompactSupport hu hus j, ?_, ?_⟩
  · intro α _
    exact (memLp_cartesian_jet hu hus (fun i ↦ α (some i))).integrable_norm_pow (by decide)
  · have hR0 : 0 ≤ R := zero_le_one.trans hR
    have hbound (j : ℕ) (hj : j ≤ r) (x : E) :
        ‖iteratedFDeriv ℝ j u x‖ ≤
          (∑ k ∈ Finset.range (r + 1), B k) * R ^ r * M := by
      apply (hb j hj x).trans
      apply mul_le_mul_of_nonneg_right _ hM
      apply mul_le_mul
        (Finset.single_le_sum (fun k _ ↦ hB k) (Finset.mem_range.mpr (by omega)))
        (pow_le_pow_right₀ hR hj) (pow_nonneg hR0 _) (hsum r)
    have hnorm := cartesianJetNorm_le_of_compact_jet_bound hK r hu hs
      (mul_nonneg (mul_nonneg (hsum r) (pow_nonneg hR0 r)) hM) hbound
    simpa only [C, mul_assoc] using hnorm

end JanetCartan.BallSmoothing
