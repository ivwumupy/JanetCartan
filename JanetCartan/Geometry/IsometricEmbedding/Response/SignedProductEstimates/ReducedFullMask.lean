module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedAmplitudes
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.Kernel

/-!
# The complete complementary mask on reduced signed sources

The full-gap source estimate in Step 1 of
`app:ch_pairs:prop:pairs-lag-sum` is applied to the actual reduced vector amplitudes, with the original row contraction.
Every nonzero point of the original complementary mask must satisfy the
primitive phase gap, including angular shoulders and bounded frequencies.
Leibniz bounds for the complete source cutoff and amplitudes are derived here;
no Fourier tail or estimate for a response is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.SignedProductEstimates
open Sampling.BackgroundModulation

open JanetCartan.Localization ResponseTransfer ResponseTransfer.SourceNegative
open ResponseTransfer.Complement.InactiveSource

variable {n N : ℕ}

/-- The entire complementary mask has the source-shell estimate for both
actual reduced signed amplitudes (`app:ch_pairs:prop:pairs-lag-sum`, Step 1).
The constant precedes the source, phases, samples, history, scales and mask
realization. The inputs are the original phase gap, individual amplitude
jets and the original row/cutoff jets. The same theorem applies to doubled plus carriers. -/
theorem exists_reduced_signed_full_mask_tail_constant
    {S : Set (Euclidean n)} (hS : IsCompact S)
    {c : ℝ} (hc : 0 < c) (G W : ℝ) (hW : 0 ≤ W)
    (P X Y CQ C : ℕ → ℝ) (hP : ∀ r, 0 ≤ P r) (hX : ∀ r, 0 ≤ X r)
    (hY : ∀ r, 0 ≤ Y r) (hCQ : ∀ r, 0 ≤ CQ r) (hC : ∀ r, 0 ≤ C r)
    {s : ℝ} (hs : 0 ≤ s) (k : ℕ) (hk : s + (n : ℝ) / 2 < k) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (U : Set (Euclidean n)), IsOpen U → S ⊆ U →
      ∀ (χ ψ φ : Euclidean n → ℝ) (Q : Euclidean n → Fin n → MetricTensor n)
        (A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
        (L ρ : ℝ) (m : BoundedMask n),
      ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ Q U →
      ContDiffOn ℝ ∞ φ U →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      tsupport χ ⊆ S → 1 ≤ L → 1 ≤ ρ → m.bound ≤ W →
      (∀ η, m.symbol η ≠ 0 → ∀ x ∈ U,
        c * (ρ + ‖η‖) ≤ ‖ρ • fderiv ℝ φ x - InnerProductSpace.toDual ℝ (Euclidean n) η‖) →
      (∀ x ∈ U, ‖fderiv ℝ φ x‖ ≤ G) →
      (∀ x ∈ S, ∀ r, 1 ≤ r → ‖iteratedFDeriv ℝ (r + 1) φ x‖ ≤ P r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ x‖ ≤ X r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r ψ x‖ ≤ Y r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r Q x‖ ≤ CQ r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r A x‖ ≤ C r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r B x‖ ≤ C r * L ^ r) →
      let Hp := fun η : Euclidean n ↦ m.symbol η • physicalFourierIntegral volume
        (modulatedSource χ φ (fun x ↦ ψ x • ((1 / 2 : ℝ) •
          complexStressContraction (Q x) (symmetricBilinearTensor (A x) (B x)))) ρ)
          (InnerProductSpace.toDual ℝ (Euclidean n) η)
      let Hm := fun η : Euclidean n ↦ m.symbol η • physicalFourierIntegral volume
        (modulatedSource χ φ (fun x ↦ ψ x • ((1 / 2 : ℝ) •
          complexStressContraction (Q x) (symmetricBilinearTensor (A x) ((B x).map conj)))) ρ)
          (InnerProductSpace.toDual ℝ (Euclidean n) η)
      (Integrable (fun η ↦ (1 + ‖η‖ ^ 2) ^ s * ‖Hp η‖ ^ 2) ∧
        fourierWeightedL2Norm volume s Hp ≤ D * (ρ ^ (s + (n : ℝ) / 2) * (L / ρ) ^ k)) ∧
      (Integrable (fun η ↦ (1 + ‖η‖ ^ 2) ^ s * ‖Hm η‖ ^ 2) ∧
        fourierWeightedL2Norm volume s Hm ≤ D * (ρ ^ (s + (n : ℝ) / 2) * (L / ρ) ^ k)) := by
  obtain ⟨J, hJ, hjet⟩ := exists_cutoff_reduced_signed_jet_constants (n := n) (N := N)
    X Y CQ C hX hY hCQ hC
  let D := W * gapKernelConstant n c G P J k * volume.real S *
    Real.sqrt (∫ η : Euclidean n, (1 + ‖η‖) ^ (-(2 * (k : ℝ) - 2 * s)))
  have hker := gapKernelConstant_nonneg (d := n) c G P J hJ k
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro U hU hSU χ ψ φ Q A B L ρ m hχ hη hQ hφ hA hB hχs hL hρ hm hgap hupper hphase
    hχb hηb hQb hAb hBb
  have hj := hjet U hU L hL χ ψ Q A B hχ hη hQ hA hB hχb hηb hQb hAb hBb
  obtain ⟨hps, hms⟩ := contDiffOn_reduced_signed_amplitudes hQ hη hA hB
  have hfull (a : Euclidean n → EuclideanSpace ℂ (Fin n))
      (ha : ContDiffOn ℝ ∞ a U)
      (haj : ∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r (fun y ↦ χ y • a y) x‖ ≤ J r * L ^ r) :
      let H := fun η : Euclidean n ↦ m.symbol η • physicalFourierIntegral volume
        (modulatedSource χ φ a ρ) (InnerProductSpace.toDual ℝ (Euclidean n) η)
      Integrable (fun η ↦ (1 + ‖η‖ ^ 2) ^ s * ‖H η‖ ^ 2) ∧
        fourierWeightedL2Norm volume s H ≤ D * (ρ ^ (s + (n : ℝ) / 2) * (L / ρ) ^ k) := by
    have hsupport : tsupport (fun x ↦ χ x • a x) ⊆ S :=
      (tsupport_smul_subset_left χ a).trans hχs
    have he : (fun x ↦ carrier ρ φ x • (χ x • a x)) = modulatedSource χ φ a ρ := by
      funext x
      exact smul_comm _ _ _
    obtain ⟨hi, hb⟩ := masked_carrier_spectral_tail hU hS hSU m φ
      (fun x ↦ χ x • a x) k hφ (hχ.smul ha) hsupport hc zero_le_one
      (zero_le_one.trans hL) hρ hs hk hgap hupper hP hJ
      (fun x hx r hr ↦ hphase x (hsupport hx) r hr)
      (fun x hx r ↦ by simpa only [one_mul] using haj x (hSU (hsupport hx)) r)
    rw [he] at hi hb
    refine ⟨hi, hb.trans ?_⟩
    dsimp only [D]
    simp only [mul_one]
    gcongr
  exact ⟨hfull _ hps (fun x hx r ↦ (hj x hx r).1),
    hfull _ hms (fun x hx r ↦ (hj x hx r).2)⟩

end JanetCartan.SignedProductEstimates
