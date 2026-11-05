module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.OperatorDifference.Algebra
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CurrentTransfer

/-!
# The reflected-amplitude tolerance required for the uniform gap

The literal reflected normal already includes the two real quadratures.
The finite sum below therefore uses no further factor four. The PDO estimate
uses exactly `2 * (n + 1)` physical derivatives. Actual normal identifications
and primitive amplitude bounds are still supplied by the same-row producers.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProduct Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ContinuumRow CarrierVariation AmplitudeBound Pseudodifferential PeriodicLocalL2

variable {n : ℕ} {ι : Type} [Fintype ι]

/-- The precise full-amplitude smallness that preserves half the frozen
augmented gap. The tolerance precedes all varying rows and densities. Every
carrier normal is identified with its SAME reflected PDO, with its existing
factor four. The fixed exterior square cancels, and the image comparison
uses the remaining quarter of the gap.

Consumer: actual normalized coercivity and `PositiveBackground.SourceInverse`.
Sources: `app:ch_background:prop:bg-normalized`, `bg-global-bound`, and
`app:ch_osc:prop:osc-normal`, Step 4'. This is the checked PDO deduction;
it does not construct the row or its analytic inputs. -/
theorem exists_reflected_amplitude_half_gap_tolerance
    (hn : 0 < n) (R : ℝ) {gap : ℝ} (hgap : 0 < gap) :
    ∃ η > 0,
      ∀ (b : Fin 2 → ι → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
      (hb : ∀ t a, ContDiff ℝ ∞ (Function.uncurry (b t a)))
      (hs : ∀ t a ξ i j, SupportedInCenteredBox R (fun z ↦ b t a ξ z i j))
      (B : Fin 2 → ι → ℝ)
      (hB : ∀ t a i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b t a ξ z i j)
        (2 * (n + 1)) (B t a))
      (image : Fin 2 → OutputL2 n →L[ℝ] OutputL2 n)
      (T : Fin 2 → ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
      (ψ : C(Torus n, ℝ)),
      (∀ t a, carrierChannel (T t a) ∘L (carrierChannel (T t a)).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator hn R (b t a) (hb t a) (hs t a) (B t a) (hB t a)))) →
      (∀ a i j, HasAmplitudeDerivativeBound (fun ξ z ↦ (b 0 a - b 1 a) ξ z i j)
        (2 * (n + 1)) η) →
      ‖NormalPerturbation.normal (image 0) - NormalPerturbation.normal (image 1)‖ ≤ gap / 4 →
      (∀ f, gap * ‖f‖ ^ 2 ≤ inner ℝ (augmentedNormal (image 1) (T 1) ψ f) f) →
      (‖augmentedNormal (image 0) (T 0) ψ - augmentedNormal (image 1) (T 1) ψ‖ ≤ gap / 2) ∧
      ∀ f, (gap / 2) * ‖f‖ ^ 2 ≤ inner ℝ (augmentedNormal (image 0) (T 0) ψ f) f := by
  let K := (Fintype.card ι : ℝ) * ((n : ℝ) ^ 2 * fixedBoxAmplitudeConstant n R)
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (sq_nonneg _) (fixedBoxAmplitudeConstant_nonneg _ _))
  let η := gap / (4 * (K + 1))
  have hη : 0 < η := div_pos hgap (by positivity)
  have hbudget : K * η ≤ gap / 4 := by
    have hcancel : (4 * (K + 1)) * η = gap := mul_div_cancel₀ gap (by positivity)
    nlinarith
  refine ⟨η, hη, ?_⟩
  intro b hb hs B hB image T ψ hnormal hdiff himage hfrozen
  have hcarrier (a : ι) :
      ‖carrierChannel (T 0 a) ∘L (carrierChannel (T 0 a)).adjoint -
        carrierChannel (T 1 a) ∘L (carrierChannel (T 1 a)).adjoint‖ ≤
          (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n R * η) := by
    rw [hnormal 0 a, hnormal 1 a]
    have hsupport : ∀ ξ i j, SupportedInCenteredBox R
        (fun z ↦ (b 0 a - b 1 a) ξ z i j) := by
      intro ξ i j z hz
      by_cases hzero : b 0 a ξ z i j = 0
      · exact hs 1 a ξ i j z (by
          simpa only [Pi.sub_apply, Matrix.sub_apply, hzero, zero_sub, neg_ne_zero] using hz)
      · exact hs 0 a ξ i j z hzero
    exact (vectorTwoPositionL2Operator_sub_bounds hn R (b 0 a) (b 1 a)
      (hb 0 a) (hb 1 a) ((hb 0 a).sub (hb 1 a)) (hs 0 a) (hs 1 a) hsupport
      (B 0 a) (B 1 a) η (hB 0 a) (hB 1 a) (2 * (n + 1)) le_rfl (hdiff a)).2.2
  have hclose : ‖augmentedNormal (image 0) (T 0) ψ -
      augmentedNormal (image 1) (T 1) ψ‖ ≤ gap / 2 := by
    have heq : augmentedNormal (image 0) (T 0) ψ - augmentedNormal (image 1) (T 1) ψ =
        (NormalPerturbation.normal (image 0) - NormalPerturbation.normal (image 1)) +
          ∑ a, (carrierChannel (T 0 a) ∘L (carrierChannel (T 0 a)).adjoint -
            carrierChannel (T 1 a) ∘L (carrierChannel (T 1 a)).adjoint) := by
      rw [augmentedNormal_eq_sum, augmentedNormal_eq_sum]
      simp only [Finset.sum_sub_distrib, NormalPerturbation.normal]
      abel
    rw [heq]
    apply (norm_add_le _ _).trans
    have hsum := (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun a _ ↦ hcarrier a))
    have hsum' : ‖∑ a, (carrierChannel (T 0 a) ∘L (carrierChannel (T 0 a)).adjoint -
        carrierChannel (T 1 a) ∘L (carrierChannel (T 1 a)).adjoint)‖ ≤ K * η := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, K, mul_assoc] using hsum
    linarith
  refine ⟨hclose, ?_⟩
  intro f
  exact augmented_half_gap_of_normal_comparison (image 0) (image 1) (T 0) (T 1) ψ univ
    (fun f _ ↦ hfrozen f) hclose le_rfl f (mem_univ f)

/-- A finite family of primitive errors tending to zero has one positive
source cap for all reflected-amplitude budgets. The cap precedes the source
scale and any density: the errors are the coefficient/inverse/Jacobian/ODE
errors, which are independent of the permitted density. The given source cap
is retained. Consumer: `exists_fullAmplitude_sqrtFootpoints_sub_bounds` and
the half-gap tolerance above, for `app:ch_background:prop:bg-normalized`. -/
theorem exists_common_source_cap_for_reflected_budgets
    (C : ι → ℝ) (error : ι → ℝ → ℝ)
    (herror : ∀ a, Tendsto (error a) (𝓝 0) (𝓝 0))
    {sourceCap η : ℝ} (hsourceCap : 0 < sourceCap) (hη : 0 < η) :
    ∃ cap > 0, cap ≤ sourceCap ∧ ∀ σ ∈ Ioc (0 : ℝ) cap,
      ∀ a, (4 * C a) * error a σ ≤ η := by
  have hevent : ∀ᶠ σ in 𝓝 (0 : ℝ), ∀ a, (4 * C a) * error a σ < η := by
    apply eventually_all.mpr
    intro a
    have ht : Tendsto (fun σ ↦ (4 * C a) * error a σ) (𝓝 0) (𝓝 0) := by
      simpa only [mul_zero] using (herror a).const_mul (4 * C a)
    exact ht.eventually (gt_mem_nhds hη)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨min sourceCap (r / 2), lt_min hsourceCap (half_pos hr), min_le_left _ _, ?_⟩
  intro σ hσ a
  apply (hball ?_ a).le
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ.1]
  exact (hσ.2.trans (min_le_right _ _)).trans_lt (half_lt_self hr)

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
