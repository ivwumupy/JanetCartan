module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedSourceSize
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.Sobolev
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector

/-!
# Sobolev profiles of the literal reduced signed amplitudes

Step 1 of `app:ch_pairs:prop:pairs-lag-sum` needs the complete tensor product
after the original row contraction and both cutoffs. Compact spatial jets
supply the existing scalar Fourier envelope in every channel, with power
`L^r` and no derivative loss. The measures and Fourier normalization remain
those of `SourceNegative` and the fixed inverse. The complete oscillatory
sources also have their positive-order vector Sobolev profiles at carrier
scale, using only the true-frequency upper bound.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory FourierTransform
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open ResponseTransfer.SourceNegative ResponseTransfer.LowEnvelope Pseudodifferential AmplitudeBound
open Sampling.BackgroundModulation ResponseSourceExtension PrimarySourceAdmission
variable {n N : ℕ}

/-- Convert the reduced vector's compact jets to its literal scalar-channel
Fourier envelopes (`app:ch_pairs:eq:pairs-lag-envelope`). The constants are
fixed before the vector function, with no added derivative order. -/
private theorem exists_compact_channel_sobolev_constants
    {S : Set (Euclidean n)} (hS : IsCompact S)
    (J : ℕ → ℝ) (hJ : ∀ j, 0 ≤ J j) :
    ∃ C : ℕ → ℝ, (∀ p, 0 ≤ C p) ∧
      ∀ (f : Euclidean n → EuclideanSpace ℂ (Fin n)) (hf : MemLp f 2 volume)
        (L : ℝ), 1 ≤ L → ContDiff ℝ ∞ f → tsupport f ⊆ S →
        (∀ x j, ‖iteratedFDeriv ℝ j f x‖ ≤ J j * L ^ j) →
        ∀ i, SobolevEnvelopeBounds (fun x ↦ f x i) (hf.eval_piLp i) 1 L C := by
  let C := fun p ↦ compactCoordinateSobolevConstant n p * Real.sqrt (volume.real S) *
    ∑ j ∈ Finset.range (p + 1), J j
  have hC (p) : 0 ≤ C p := mul_nonneg
    (mul_nonneg (compactCoordinateSobolevConstant_pos n p).le (Real.sqrt_nonneg _))
    (Finset.sum_nonneg (fun j _ ↦ hJ j))
  refine ⟨C, hC, ?_⟩
  intro f hf L hL hsm hs hb i
  let π := (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ
  have hπ : ‖π‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa [π] using PiLp.norm_apply_le z i
  have hc : ContDiff ℝ ∞ (fun x ↦ f x i) := π.contDiff.comp hsm
  have hsc : Function.support (fun x ↦ f x i) ⊆ S :=
    (subset_tsupport _).trans ((tsupport_comp_subset π.map_zero f).trans hs)
  have hresult (p : ℕ) :
      MemFourierSobolev (p : ℝ) ((hf.eval_piLp i).toLp (fun x ↦ f x i)) ∧
      fourierSobolevNorm (p : ℝ) ((hf.eval_piLp i).toLp (fun x ↦ f x i)) ≤ C p * L ^ p := by
    obtain ⟨hm, hmem, hbound⟩ := exists_compactCoordinateSobolev p (fun x ↦ f x i)
      hc hS hsc (B := (∑ j ∈ Finset.range (p + 1), J j) * L ^ p)
      (mul_nonneg (Finset.sum_nonneg (fun j _ ↦ hJ j)) (pow_nonneg (zero_le_one.trans hL) _))
      (fun α hα x ↦ (norm_euclideanCoordinateDerivList_le_iteratedFDeriv hc α x).trans
        ((π.norm_iteratedFDeriv_comp_left hsm.contDiffAt (by simp)).trans
          ((mul_le_of_le_one_left (norm_nonneg _) hπ).trans
            ((hb x α.length).trans (mul_le_mul
              (Finset.single_le_sum (fun j _ ↦ hJ j) (Finset.mem_range_succ_iff.mpr hα))
              (pow_le_pow_right₀ hL hα) (pow_nonneg (zero_le_one.trans hL) _)
              (Finset.sum_nonneg (fun j _ ↦ hJ j)))))))
    exact ⟨hmem, hbound.trans_eq (by dsimp [C]; ring)⟩
  refine ⟨hc, zero_le_one, hL, hC, fun p ↦ (hresult p).1, ?_⟩
  intro p
  change fourierSobolevNorm (p : ℝ) ((hf.eval_piLp i).toLp (fun x ↦ f x i)) ≤ C p * 1 * L ^ p
  simpa only [mul_one] using (hresult p).2

/-- The complete source-cutoff jets vanish off their chart, so the local
profile is global (`app:ch_pairs:prop:pairs-lag-sum`, Step 1). -/
private theorem reduced_cutoff_jet_bound_global
    {χ : Euclidean n → ℝ} {f : Euclidean n → EuclideanSpace ℂ (Fin n)}
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

/-- Each channel of the complete reduced signed amplitudes has the actual
Fourier Sobolev envelope `C_r * L^r` (`app:ch_pairs:prop:pairs-lag-sum`, Step 1).
Smoothness and vector/scalar L² membership are proved from local data and the
compact source buffer. The original row and both cutoffs stay fixed, and the
profile is chosen before varying scales, amplitudes, samples and histories.
Consumed by `exists_reduced_signed_negative_source_constants`. -/
theorem exists_cutoff_reduced_signed_sobolev_constants
    {S : Set (Euclidean n)} (hS : IsCompact S)
    (X Y CQ C : ℕ → ℝ) (hX : ∀ r, 0 ≤ X r) (hY : ∀ r, 0 ≤ Y r)
    (hCQ : ∀ r, 0 ≤ CQ r) (hC : ∀ r, 0 ≤ C r) :
    ∃ P : ℕ → ℝ, (∀ r, 0 ≤ P r) ∧
      ∀ (U : Set (Euclidean n)), IsOpen U → ∀ L : ℝ, 1 ≤ L →
      ∀ (χ η : Euclidean n → ℝ) (Q : Euclidean n → Fin n → MetricTensor n)
        (A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ),
      ContDiff ℝ ∞ χ → tsupport χ ⊆ S → tsupport χ ⊆ U →
      ContDiffOn ℝ ∞ η U → ContDiffOn ℝ ∞ Q U →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ x‖ ≤ X r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r η x‖ ≤ Y r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r Q x‖ ≤ CQ r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r A x‖ ≤ C r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r B x‖ ≤ C r * L ^ r) →
      let p := fun x ↦ χ x • (η x • ((1 / 2 : ℝ) •
        complexStressContraction (Q x) (symmetricBilinearTensor (A x) (B x))))
      let m := fun x ↦ χ x • (η x • ((1 / 2 : ℝ) •
        complexStressContraction (Q x) (symmetricBilinearTensor (A x) ((B x).map conj))))
      ∃ hp : MemLp p 2 volume, ∃ hm : MemLp m 2 volume,
        ∀ i : Fin n,
          SobolevEnvelopeBounds (fun x ↦ p x i) (hp.eval_piLp i) 1 L P ∧
          SobolevEnvelopeBounds (fun x ↦ m x i) (hm.eval_piLp i) 1 L P := by
  obtain ⟨J, hJ, hjets⟩ := exists_cutoff_reduced_signed_jet_constants (n := n) (N := N)
    X Y CQ C hX hY hCQ hC
  obtain ⟨P, hP, hfourier⟩ := exists_compact_channel_sobolev_constants hS J hJ
  refine ⟨P, hP, ?_⟩
  intro U hU L hL χ η Q A B hχ hs hsu hη hQ hA hB hχb hηb hQb hAb hBb
  dsimp only
  let p := fun x ↦ χ x • (η x • ((1 / 2 : ℝ) •
    complexStressContraction (Q x) (symmetricBilinearTensor (A x) (B x))))
  let m := fun x ↦ χ x • (η x • ((1 / 2 : ℝ) •
    complexStressContraction (Q x) (symmetricBilinearTensor (A x) ((B x).map conj))))
  obtain ⟨hps, hms⟩ := contDiffOn_reduced_signed_amplitudes hQ hη hA hB
  have hp : ContDiff ℝ ∞ p := contDiff_cutoff_of_support_subset hχ hU hps hsu
  have hm : ContDiff ℝ ∞ m := contDiff_cutoff_of_support_subset hχ hU hms hsu
  have hpc : tsupport p ⊆ S := (tsupport_smul_subset_left χ _).trans hs
  have hmc : tsupport m ⊆ S := (tsupport_smul_subset_left χ _).trans hs
  have hpm : MemLp p 2 volume := hp.continuous.memLp_of_hasCompactSupport
    (hS.of_isClosed_subset (isClosed_tsupport _) hpc)
  have hmm : MemLp m 2 volume := hm.continuous.memLp_of_hasCompactSupport
    (hS.of_isClosed_subset (isClosed_tsupport _) hmc)
  have hj := hjets U hU L hL χ η Q A B hχ.contDiffOn hη hQ hA hB hχb hηb hQb hAb hBb
  exact ⟨hpm, hmm, fun i ↦
    ⟨hfourier p hpm L hL hp hpc
      (reduced_cutoff_jet_bound_global hsu hJ (zero_le_one.trans hL) (fun x hx r ↦ (hj x hx r).1)) i,
    hfourier m hmm L hL hm hmc
      (reduced_cutoff_jet_bound_global hsu hJ (zero_le_one.trans hL) (fun x hx r ↦ (hj x hx r).2)) i⟩⟩



/-- The original reduced signed oscillations satisfy the actual vector
Fourier Sobolev bound `D_r * lam^r` (`app:ch_pairs:eq:pairs-lag-sum-size`, Step 2).
This proves the complete source input for the strong tame inverse estimate;
it does not assume or assert the physical response bound. The same row,
half factor, cutoffs and full amplitudes are retained, with constants before
all varying data and no inverse separation or accuracy loss. -/
theorem exists_reduced_signed_modulated_source_sobolev_constants
    {S : Set (Euclidean n)} (hS : IsCompact S)
    (P X Y CQ C : ℕ → ℝ) (hP : ∀ r, 0 ≤ P r) (hX : ∀ r, 0 ≤ X r)
    (hY : ∀ r, 0 ≤ Y r) (hCQ : ∀ r, 0 ≤ CQ r) (hC : ∀ r, 0 ≤ C r)
    {Cfreq : ℝ} (hCfreq : 0 ≤ Cfreq) :
    ∃ D : ℕ → ℝ, (∀ r, 0 ≤ D r) ∧
      ∀ (U : Set (Euclidean n)), IsOpen U → ∀ L lam ρp ρm : ℝ,
      1 ≤ L → L ≤ lam → 0 ≤ ρp → 0 ≤ ρm →
      ρp ≤ Cfreq * lam → ρm ≤ Cfreq * lam →
      ∀ (χ η φp φm : Euclidean n → ℝ) (Q : Euclidean n → Fin n → MetricTensor n)
        (A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ),
      ContDiff ℝ ∞ χ → tsupport χ ⊆ S → tsupport χ ⊆ U →
      ContDiffOn ℝ ∞ η U → ContDiffOn ℝ ∞ Q U →
      ContDiffOn ℝ ∞ φp U → ContDiffOn ℝ ∞ φm U →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      (∀ x ∈ U, ∀ r, 1 ≤ r → ‖iteratedFDeriv ℝ r φp x‖ ≤ P r * L ^ (r - 1)) →
      (∀ x ∈ U, ∀ r, 1 ≤ r → ‖iteratedFDeriv ℝ r φm x‖ ≤ P r * L ^ (r - 1)) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ x‖ ≤ X r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r η x‖ ≤ Y r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r Q x‖ ≤ CQ r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r A x‖ ≤ C r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r B x‖ ≤ C r * L ^ r) →
      let p := modulatedSource χ φp (fun x ↦ η x • ((1 / 2 : ℝ) •
        complexStressContraction (Q x) (symmetricBilinearTensor (A x) (B x)))) ρp
      let m := modulatedSource χ φm (fun x ↦ η x • ((1 / 2 : ℝ) •
        complexStressContraction (Q x) (symmetricBilinearTensor (A x) ((B x).map conj)))) ρm
      ∃ hp : MemLp p 2 volume, ∃ hm : MemLp m 2 volume, ∀ r : ℕ,
        (MemVectorFourierSobolev (r : ℝ) (hp.toLp p) ∧
          vectorFourierSobolevNorm (r : ℝ) (hp.toLp p) ≤ D r * lam ^ r) ∧
        (MemVectorFourierSobolev (r : ℝ) (hm.toLp m) ∧
          vectorFourierSobolevNorm (r : ℝ) (hm.toLp m) ≤ D r * lam ^ r) := by
  obtain ⟨J, hJ, hjets⟩ := exists_reduced_signed_modulated_source_jet_constants
    (n := n) (N := N) P X Y CQ C hP hX hY hCQ hC hCfreq
  obtain ⟨D, hD, hfourier⟩ := exists_compact_channel_sobolev_constants hS J hJ
  refine ⟨fun r ↦ (n : ℝ) * D r, fun r ↦ mul_nonneg (Nat.cast_nonneg _) (hD r), ?_⟩
  intro U hU L lam ρp ρm hL hLlam hρp hρm hρpL hρmL χ η φp φm Q A B
    hχ hs hsu hη hQ hφp hφm hA hB hp hm hχb hηb hQb hAb hBb
  dsimp only
  obtain ⟨haps, hams⟩ := contDiffOn_reduced_signed_amplitudes hQ hη hA hB
  have hj := hjets U hU L lam ρp ρm hL hLlam hρp hρm hρpL hρmL χ η φp φm Q A B
    hχ.contDiffOn hη hQ hφp hφm hA hB hp hm hχb hηb hQb hAb hBb
  have hfull (φ : Euclidean n → ℝ) (a : Euclidean n → EuclideanSpace ℂ (Fin n))
      (ρ : ℝ) (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U)
      (haj : ∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r (modulatedSource χ φ a ρ) x‖ ≤ J r * lam ^ r) :
      ∃ hf : MemLp (modulatedSource χ φ a ρ) 2 volume, ∀ r : ℕ,
        MemVectorFourierSobolev (r : ℝ) (hf.toLp (modulatedSource χ φ a ρ)) ∧
        vectorFourierSobolevNorm (r : ℝ) (hf.toLp (modulatedSource χ φ a ρ)) ≤
          ((n : ℝ) * D r) * lam ^ r := by
    let f := modulatedSource χ φ a ρ
    have hc : ContDiffOn ℝ ∞ (ResponseTransfer.carrier ρ φ) U := by
      change ContDiffOn ℝ ∞ (fun y ↦ Complex.exp (Complex.I * ((ρ * φ y : ℝ) : ℂ))) U
      exact (contDiffOn_const.mul
        (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul hφ))).cexp
    have hfs : ContDiff ℝ ∞ f := contDiff_cutoff_of_support_subset hχ hU (hc.smul ha) hsu
    have hfc : tsupport f ⊆ S := (tsupport_smul_subset_left χ _).trans hs
    have hfm : MemLp f 2 volume := hfs.continuous.memLp_of_hasCompactSupport
      (hS.of_isClosed_subset (isClosed_tsupport _) hfc)
    have hfb := reduced_cutoff_jet_bound_global hsu hJ
      ((zero_le_one.trans hL).trans hLlam) haj
    have henv := hfourier f hfm lam (hL.trans hLlam) hfs hfc hfb
    refine ⟨hfm, fun r ↦ ⟨?_, ?_⟩⟩
    · change ∀ i, MemFourierSobolev (r : ℝ) (finiteL2CoordinateIsometry volume (hfm.toLp f) i)
      rw [finiteL2CoordinateIsometry_toLp]
      intro i
      exact (henv i).fourier_memLp r
    · unfold vectorFourierSobolevNorm
      rw [finiteL2CoordinateIsometry_toLp]
      calc
        _ ≤ ∑ i : Fin n, fourierSobolevNorm (r : ℝ)
            ((hfm.eval_piLp i).toLp (fun x ↦ f x i)) :=
          matrixFourierSobolevNorm_le_sum (r : ℝ)
            (WithLp.toLp 2 (fun i ↦ (hfm.eval_piLp i).toLp (fun x ↦ f x i)))
        _ ≤ ∑ _i : Fin n, D r * lam ^ r := Finset.sum_le_sum (fun i _ ↦ by
          have hi := (henv i).fourier_bound r
          change fourierSobolevNorm (r : ℝ) ((hfm.eval_piLp i).toLp (fun x ↦ f x i)) ≤
            D r * 1 * lam ^ r at hi
          simpa only [mul_one] using hi)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_assoc]
  obtain ⟨hps, hpb⟩ := hfull φp _ ρp hφp haps (fun x hx r ↦ (hj x hx r).1)
  obtain ⟨hms, hmb⟩ := hfull φm _ ρm hφm hams (fun x hx r ↦ (hj x hx r).2)
  exact ⟨hps, hms, fun r ↦ ⟨hpb r, hmb r⟩⟩

end JanetCartan.SignedProductEstimates
