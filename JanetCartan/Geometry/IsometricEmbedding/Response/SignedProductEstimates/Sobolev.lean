module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.Amplitudes
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Sobolev.Fourier
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Admission.Supported

/-!
# Sobolev profiles of the complete signed tensor amplitudes

Step 1 of `app:ch_pairs:prop:pairs-lag-sum` requires the actual Frobenius
Fourier–Sobolev profile, not merely pointwise jets. The compact tensor estimate
from `PrimarySources` supplies that profile without a derivative or frequency
loss. The same fixed cutoff and the same complete amplitudes occur throughout.
The cutoff can be the source cutoff, or the fixed envelope cutoff that is one
on the original source support; the exact source substitution is in `Sources`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.SignedProductEstimates

open ResponseTransfer.SourceNegative PrimarySourceAdmission ResponsePrimarySources

variable {n N : ℕ}

private theorem cutoff_jet_bound_global
    {χ : Euclidean n → ℝ} {f : Euclidean n → Matrix (Fin n) (Fin n) ℂ}
    {U : Set (Euclidean n)} (hs : tsupport χ ⊆ U)
    {P : ℕ → ℝ} (hP : ∀ r, 0 ≤ P r) {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r (fun y ↦ χ y • f y) x‖ ≤ P r * L ^ r) :
    ∀ x r, ‖iteratedFDeriv ℝ r (fun y ↦ χ y • f y) x‖ ≤ P r * L ^ r := by
  intro x r
  by_cases hx : x ∈ U
  · exact hb x hx r
  · have hz : iteratedFDeriv ℝ r (fun y ↦ χ y • f y) x = 0 := by
      by_contra hn
      exact hx (hs ((tsupport_smul_subset_left χ f)
        (support_iteratedFDeriv_subset r hn)))
    rw [hz, norm_zero]
    exact mul_nonneg (hP r) (pow_nonneg hL r)

/-- The complete signed amplitudes satisfy the existing
`SourceNegative.SobolevEnvelopeBounds` at scale `L`, with amplitude one and
constants fixed before all samples, target/history, cutoffs and scales
(`app:ch_pairs:eq:pairs-lag-envelope`). Smoothness, compact support and
Lebesgue `L²` membership are proved here from the actual local amplitudes.
Both signs have the SAME profile, and the plus diagonal is permitted. -/
theorem exists_cutoff_signed_tensor_sobolev_constants
    {S : Set (Euclidean n)} (hS : IsCompact S)
    (X C : ℕ → ℝ) (hX : ∀ r, 0 ≤ X r) (hC : ∀ r, 0 ≤ C r) :
    ∃ P : ℕ → ℝ, (∀ r, 0 ≤ P r) ∧
      ∀ (U : Set (Euclidean n)), IsOpen U → ∀ L : ℝ, 1 ≤ L →
      ∀ (χ : Euclidean n → ℝ) (A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ),
        ContDiff ℝ ∞ χ → tsupport χ ⊆ S → tsupport χ ⊆ U →
        ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
        (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ x‖ ≤ X r * L ^ r) →
        (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r A x‖ ≤ C r * L ^ r) →
        (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r B x‖ ≤ C r * L ^ r) →
        let p := fun x ↦ χ x • symmetricBilinearTensor (A x) (B x)
        let m := fun x ↦ χ x • symmetricBilinearTensor (A x) ((B x).map conj)
        ∃ hp : MemLp p 2 volume, ∃ hm : MemLp m 2 volume,
          SobolevEnvelopeBounds p hp 1 L P ∧ SobolevEnvelopeBounds m hm 1 L P := by
  obtain ⟨J, hJ, hjets⟩ := exists_cutoff_signed_tensor_jet_constants (n := n) (N := N)
    X C hX hC
  obtain ⟨P, hP, hfourier⟩ := exists_primary_tensor_sobolev_constants hS J hJ
  refine ⟨P, hP, ?_⟩
  intro U hU L hL χ A B hχ hs hsu hA hB hχb hAb hBb
  dsimp only
  let p := fun x ↦ χ x • symmetricBilinearTensor (A x) (B x)
  let m := fun x ↦ χ x • symmetricBilinearTensor (A x) ((B x).map conj)
  obtain ⟨hps, hms⟩ := contDiffOn_signed_tensor_amplitudes hA hB
  have hp : ContDiff ℝ ∞ p := contDiff_cutoff_of_support_subset hχ hU hps hsu
  have hm : ContDiff ℝ ∞ m := contDiff_cutoff_of_support_subset hχ hU hms hsu
  have hpc : tsupport p ⊆ S := (tsupport_smul_subset_left χ _).trans hs
  have hmc : tsupport m ⊆ S := (tsupport_smul_subset_left χ _).trans hs
  have hpm : MemLp p 2 volume := hp.continuous.memLp_of_hasCompactSupport
    (hS.of_isClosed_subset (isClosed_tsupport _) hpc)
  have hmm : MemLp m 2 volume := hm.continuous.memLp_of_hasCompactSupport
    (hS.of_isClosed_subset (isClosed_tsupport _) hmc)
  have hj := hjets U hU L hL χ A B hχ.contDiffOn hA hB hχb hAb hBb
  have hpb := cutoff_jet_bound_global hsu hJ (zero_le_one.trans hL)
    (fun x hx r ↦ (hj x hx r).1)
  have hmb := cutoff_jet_bound_global hsu hJ (zero_le_one.trans hL)
    (fun x hx r ↦ (hj x hx r).2)
  refine ⟨hpm, hmm, hfourier p hpm 1 L zero_le_one hL hp hpc ?_,
    hfourier m hmm 1 L zero_le_one hL hm hmc ?_⟩
  · simpa only [mul_one] using hpb
  · simpa only [mul_one] using hmb

end JanetCartan.SignedProductEstimates
