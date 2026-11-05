module
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedAmplitudes
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.SourceSize

/-!
# Carrier-scale jets for the complete reduced signed sources

The physical size estimate in Step 2 of `app:ch_pairs:prop:pairs-lag-sum`
requires the original reduced source to have order-`r` size `lam^r`.
The complete row multiplier and both cutoffs have the slow scale, while
all true pair frequencies are bounded by a fixed multiple of `lam`.
No inverse separation or proof-accuracy factor enters this estimate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open ResponseTransfer ResponseTransfer.SourceNegative ResponseTransfer.LowEnvelope
open Sampling.BackgroundModulation RawPrimary.AmplitudeGrades.Polynomial
variable {n N : ℕ}

/-- The literal reduced plus/minus oscillations have jets of order `lam^r`
(`app:ch_pairs:eq:pairs-lag-sum-size`). The full tensor, half stress contraction
and both cutoffs are retained. The constant profile precedes the varying
phases, row, samples and scales; it supplies the strong source-size input
for the SAME fixed inverse. -/
theorem exists_reduced_signed_modulated_source_jet_constants
    (P X Y CQ C : ℕ → ℝ) (hP : ∀ r, 0 ≤ P r) (hX : ∀ r, 0 ≤ X r)
    (hY : ∀ r, 0 ≤ Y r) (hCQ : ∀ r, 0 ≤ CQ r) (hC : ∀ r, 0 ≤ C r)
    {Cfreq : ℝ} (hCfreq : 0 ≤ Cfreq) :
    ∃ J : ℕ → ℝ, (∀ r, 0 ≤ J r) ∧
      ∀ (U : Set (Euclidean n)), IsOpen U → ∀ L lam ρp ρm : ℝ,
      1 ≤ L → L ≤ lam → 0 ≤ ρp → 0 ≤ ρm →
      ρp ≤ Cfreq * lam → ρm ≤ Cfreq * lam →
      ∀ (χ η φp φm : Euclidean n → ℝ) (Q : Euclidean n → Fin n → MetricTensor n)
        (A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ),
      ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ η U → ContDiffOn ℝ ∞ Q U →
      ContDiffOn ℝ ∞ φp U → ContDiffOn ℝ ∞ φm U →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      (∀ x ∈ U, ∀ r, 1 ≤ r → ‖iteratedFDeriv ℝ r φp x‖ ≤ P r * L ^ (r - 1)) →
      (∀ x ∈ U, ∀ r, 1 ≤ r → ‖iteratedFDeriv ℝ r φm x‖ ≤ P r * L ^ (r - 1)) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ x‖ ≤ X r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r η x‖ ≤ Y r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r Q x‖ ≤ CQ r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r A x‖ ≤ C r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r B x‖ ≤ C r * L ^ r) →
      ∀ x ∈ U, ∀ r,
        ‖iteratedFDeriv ℝ r (modulatedSource χ φp (fun y ↦ η y • ((1 / 2 : ℝ) •
          complexStressContraction (Q y) (symmetricBilinearTensor (A y) (B y)))) ρp) x‖ ≤
          J r * lam ^ r ∧
        ‖iteratedFDeriv ℝ r (modulatedSource χ φm (fun y ↦ η y • ((1 / 2 : ℝ) •
          complexStressContraction (Q y) (symmetricBilinearTensor (A y) ((B y).map conj)))) ρm) x‖ ≤
          J r * lam ^ r := by
  obtain ⟨J, hJ, hj⟩ := exists_cutoff_reduced_signed_jet_constants (n := n) (N := N)
    X Y CQ C hX hY hCQ hC
  let O := outputOscillationGrade (fun r ↦ Cfreq * P r)
  have hO : ∀ r, 0 ≤ O r := outputOscillationGrade_nonneg _ (fun r ↦ mul_nonneg hCfreq (hP r))
  let M := (ContinuousLinearMap.lsmul ℝ ℂ :
    ℂ →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n))
  refine ⟨productProfile M O J, productProfile_nonneg _ hO hJ, ?_⟩
  intro U hU L lam ρp ρm hL hLlam hρp hρm hρpL hρmL χ η φp φm Q A B
    hχ hη hQ hφp hφm hA hB hp hm hχb hηb hQb hAb hBb x hx r
  obtain ⟨haps, hams⟩ := contDiffOn_reduced_signed_amplitudes hQ hη hA hB
  have hjets := hj U hU L hL χ η Q A B hχ hη hQ hA hB hχb hηb hQb hAb hBb
  have hfull (φ : Euclidean n → ℝ) (a : Euclidean n → EuclideanSpace ℂ (Fin n))
      (ρ : ℝ) (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U)
      (hρ : 0 ≤ ρ) (hρL : ρ ≤ Cfreq * lam)
      (hphase : ∀ j, 1 ≤ j → ‖iteratedFDeriv ℝ j φ x‖ ≤ P j * L ^ (j - 1))
      (haj : ∀ j, ‖iteratedFDeriv ℝ j (fun y ↦ χ y • a y) x‖ ≤ J j * L ^ j) :
      ‖iteratedFDeriv ℝ r (modulatedSource χ φ a ρ) x‖ ≤ productProfile M O J r * lam ^ r := by
    have hc : ContDiffOn ℝ ∞ (carrier ρ φ) U := by
      change ContDiffOn ℝ ∞ (fun y ↦ Complex.exp (Complex.I * ((ρ * φ y : ℝ) : ℂ))) U
      exact (contDiffOn_const.mul
        (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul hφ))).cexp
    have ht := jet_bilinear_le M (f := carrier ρ φ) (g := fun y ↦ χ y • a y)
      hU hc (hχ.smul ha) hx (b := 0) (hL.trans hLlam) hO hJ
      (fun j ↦ norm_iteratedFDeriv_signed_carrier_le hU hφ P hP hL hLlam
        hρ hCfreq hρL hx hphase j)
      (fun j ↦ (haj j).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans hL) hLlam j) (hJ j))) r
    have he : (fun y ↦ M (carrier ρ φ y) (χ y • a y)) = modulatedSource χ φ a ρ := by
      funext y
      change carrier ρ φ y • (χ y • a y) = χ y • (carrier ρ φ y • a y)
      exact smul_comm _ _ _
    rw [he] at ht
    simpa only [Nat.sub_zero] using ht
  exact ⟨hfull φp _ ρp hφp haps hρp hρpL (hp x hx) (fun j ↦ (hjets x hx j).1),
    hfull φm _ ρm hφm hams hρm hρmL (hm x hx) (fun j ↦ (hjets x hx j).2)⟩

end JanetCartan.SignedProductEstimates
