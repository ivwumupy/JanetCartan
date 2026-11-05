module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.Sobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.OutputJets.Grades.Oscillation

/-!
# Physical source profiles without a separation loss

The size argument in Step 2 of `app:ch_pairs:prop:pairs-lag-sum` uses the full
oscillatory source at carrier scale `lam`. The actual normalized phase jets,
true-frequency upper bound and complete tensor amplitudes imply this profile.
The source cutoff is retained. All constants precede the frequencies, samples,
targets and finite histories, and no proof accuracy enters them.

These are inputs to the original solver's strong tame estimates. They do not
assert a physical response-size estimate or a residual-chain bound.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.SignedProductEstimates
open ResponseTransfer ResponseTransfer.SourceNegative ResponseTransfer.LowEnvelope
variable {n N : ℕ}

/-- Local normalized phase jets imply carrier-scale jets for the actual
oscillation, using only `rho ≤ Cfreq * lam` and `L ≤ lam`
(`app:ch_pairs:eq:pairs-lag-sum-size`, Step 2). No global phase extension bound
or inverse power of the pair separation is used. This is the oscillatory
factor in `exists_signed_modulated_source_jet_constants`. -/
theorem norm_iteratedFDeriv_signed_carrier_le {U : Set (Euclidean n)} (hU : IsOpen U)
    {φ : Euclidean n → ℝ} (hφ : ContDiffOn ℝ ∞ φ U)
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    {L lam ρ Cfreq : ℝ} (hL : 1 ≤ L) (hLlam : L ≤ lam)
    (hρ : 0 ≤ ρ) (hCfreq : 0 ≤ Cfreq) (hρlam : ρ ≤ Cfreq * lam)
    {x : Euclidean n} (hx : x ∈ U)
    (hphase : ∀ j, 1 ≤ j → ‖iteratedFDeriv ℝ j φ x‖ ≤ P j * L ^ (j - 1))
    (r : ℕ) :
    ‖iteratedFDeriv ℝ r (carrier ρ φ) x‖ ≤
      outputOscillationGrade (fun j ↦ Cfreq * P j) r * lam ^ r := by
  let M := 1 + ∑ j ∈ Finset.range (r + 1), Cfreq * P j
  have hM : 1 ≤ M := le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ ↦ mul_nonneg hCfreq (hP j))
  have hlam : 0 ≤ lam := (zero_le_one.trans hL).trans hLlam
  have hscaled : ContDiffOn ℝ ∞ (fun y ↦ ρ * φ y) U := contDiffOn_const.mul hφ
  have hb (j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r) :
      ‖iteratedFDeriv ℝ j (fun y ↦ ρ * φ y) x‖ ≤ (M * lam) ^ j := by
    have hPM : Cfreq * P j ≤ M := by
      have hs := Finset.single_le_sum (s := Finset.range (r + 1))
        (f := fun j ↦ Cfreq * P j) (fun i _ ↦ mul_nonneg hCfreq (hP i))
        (show j ∈ Finset.range (r + 1) by simp; omega)
      dsimp [M]
      linarith
    have hpow : Cfreq * P j ≤ M ^ j :=
      hPM.trans (by simpa using pow_le_pow_right₀ hM hj)
    rw [show (fun y ↦ ρ * φ y) = ρ • φ from rfl,
      iteratedFDeriv_const_smul_apply ((hφ.contDiffAt (hU.mem_nhds hx)).of_le (by simp)),
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ]
    calc
      _ ≤ (Cfreq * lam) * (P j * L ^ (j - 1)) :=
        mul_le_mul hρlam (hphase j hj) (norm_nonneg _) (mul_nonneg hCfreq hlam)
      _ ≤ (Cfreq * lam) * (P j * lam ^ (j - 1)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans hL) hLlam _) (hP j))
        (mul_nonneg hCfreq hlam)
      _ = (Cfreq * P j) * (lam * lam ^ (j - 1)) := by ring
      _ = (Cfreq * P j) * lam ^ j := by rw [← pow_succ', Nat.sub_add_cancel hj]
      _ ≤ M ^ j * lam ^ j := mul_le_mul_of_nonneg_right hpow (pow_nonneg hlam j)
      _ = (M * lam) ^ j := (mul_pow _ _ _).symm
  have hout : ContDiff ℝ ∞ (fun t : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I)) :=
    contDiff_outputOscillation contDiff_id
  have hh := norm_iteratedFDerivWithin_comp_le hout.contDiffOn hscaled
    (by simp : (r : ℕ∞ω) ≤ ∞) uniqueDiffOn_univ hU.uniqueDiffOn
    (mapsTo_univ _ _) hx (C := 1) (D := M * lam)
    (fun j _ ↦ by simpa only [iteratedFDerivWithin_univ] using
      (norm_iteratedFDeriv_outputUnitOscillation j (ρ * φ x)).le)
    (fun j hj hjr ↦ by simpa only [iteratedFDerivWithin_of_isOpen _ hU hx] using hb j hj hjr)
  rw [iteratedFDerivWithin_of_isOpen _ hU hx] at hh
  change ‖iteratedFDeriv ℝ r (fun y ↦ Complex.exp (Complex.I * ((ρ * φ y : ℝ) : ℂ))) x‖ ≤ _
  simpa only [mul_comm Complex.I, Function.comp_def, mul_one, mul_pow,
    mul_assoc, outputOscillationGrade, M] using hh

/-- Complete plus/minus oscillatory sources have jets of order `lam^r`,
including the original cutoff and all tensor amplitudes
(`app:ch_pairs:eq:pairs-lag-sum-size`, Step 2). The profile precedes the source,
normalized phases and both true frequencies. The plus diagonal is permitted;
for actual phases use the exact substitutions in `Sources`. -/
theorem exists_signed_modulated_source_jet_constants
    (P X C : ℕ → ℝ) (hP : ∀ r, 0 ≤ P r) (hX : ∀ r, 0 ≤ X r)
    (hC : ∀ r, 0 ≤ C r) {Cfreq : ℝ} (hCfreq : 0 ≤ Cfreq) :
    ∃ J : ℕ → ℝ, (∀ r, 0 ≤ J r) ∧
      ∀ (U : Set (Euclidean n)), IsOpen U → ∀ L lam ρp ρm : ℝ,
      1 ≤ L → L ≤ lam → 0 ≤ ρp → 0 ≤ ρm →
      ρp ≤ Cfreq * lam → ρm ≤ Cfreq * lam →
      ∀ (χ φp φm : Euclidean n → ℝ) (A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ),
      ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ φp U → ContDiffOn ℝ ∞ φm U →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      (∀ x ∈ U, ∀ r, 1 ≤ r → ‖iteratedFDeriv ℝ r φp x‖ ≤ P r * L ^ (r - 1)) →
      (∀ x ∈ U, ∀ r, 1 ≤ r → ‖iteratedFDeriv ℝ r φm x‖ ≤ P r * L ^ (r - 1)) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ x‖ ≤ X r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r A x‖ ≤ C r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r B x‖ ≤ C r * L ^ r) →
      ∀ x ∈ U, ∀ r,
        ‖iteratedFDeriv ℝ r (modulatedSource χ φp
          (fun y ↦ symmetricBilinearTensor (A y) (B y)) ρp) x‖ ≤ J r * lam ^ r ∧
        ‖iteratedFDeriv ℝ r (modulatedSource χ φm
          (fun y ↦ symmetricBilinearTensor (A y) ((B y).map conj)) ρm) x‖ ≤ J r * lam ^ r := by
  obtain ⟨J, hJ, hj⟩ := exists_cutoff_signed_tensor_jet_constants (n := n) (N := N) X C hX hC
  let O := outputOscillationGrade (fun r ↦ Cfreq * P r)
  have hO : ∀ r, 0 ≤ O r := outputOscillationGrade_nonneg _ (fun r ↦ mul_nonneg hCfreq (hP r))
  let smulMap := (ContinuousLinearMap.lsmul ℝ ℂ :
    ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
  refine ⟨RawPrimary.AmplitudeGrades.Polynomial.productProfile smulMap O J,
    RawPrimary.AmplitudeGrades.Polynomial.productProfile_nonneg _ hO hJ, ?_⟩
  intro U hU L lam ρp ρm hL hLlam hρp hρm hρpL hρmL χ φp φm A B
    hχ hφp hφm hA hB hp hm hχb hAb hBb x hx r
  obtain ⟨haps, hams⟩ := contDiffOn_signed_tensor_amplitudes hA hB
  have hjets := hj U hU L hL χ A B hχ hA hB hχb hAb hBb
  have hfull (φ : Euclidean n → ℝ) (a : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
      (ρ : ℝ) (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U)
      (hρ : 0 ≤ ρ) (hρL : ρ ≤ Cfreq * lam)
      (hphase : ∀ j, 1 ≤ j → ‖iteratedFDeriv ℝ j φ x‖ ≤ P j * L ^ (j - 1))
      (haj : ∀ j, ‖iteratedFDeriv ℝ j (fun y ↦ χ y • a y) x‖ ≤ J j * L ^ j) :
      ‖iteratedFDeriv ℝ r (modulatedSource χ φ a ρ) x‖ ≤
        RawPrimary.AmplitudeGrades.Polynomial.productProfile smulMap O J r * lam ^ r := by
    have hc : ContDiffOn ℝ ∞ (carrier ρ φ) U := by
      change ContDiffOn ℝ ∞ (fun y ↦ Complex.exp (Complex.I * ((ρ * φ y : ℝ) : ℂ))) U
      exact (contDiffOn_const.mul
        (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul hφ))).cexp
    have ht := RawPrimary.AmplitudeGrades.Polynomial.jet_bilinear_le
      smulMap (f := carrier ρ φ) (g := fun y ↦ χ y • a y) hU hc (hχ.smul ha) hx (b := 0) (hL.trans hLlam) hO hJ
      (fun j ↦ norm_iteratedFDeriv_signed_carrier_le hU hφ P hP
        hL hLlam hρ hCfreq hρL hx hphase j)
      (fun j ↦ (haj j).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans hL) hLlam _) (hJ j))) r
    have he : (fun y ↦ smulMap (carrier ρ φ y) (χ y • a y)) = modulatedSource χ φ a ρ := by
      funext y
      simpa only [smulMap, ContinuousLinearMap.lsmul_apply, modulatedSource] using
        smul_comm (carrier ρ φ y) (χ y) (a y)
    rw [he] at ht
    simpa only [Nat.sub_zero] using ht
  exact ⟨hfull φp _ ρp hφp haps hρp hρpL (hp x hx) (fun j ↦ (hjets x hx j).1),
    hfull φm _ ρm hφm hams hρm hρmL (hm x hx) (fun j ↦ (hjets x hx j).2)⟩

/-- The full oscillatory signed sources satisfy the existing genuine
Frobenius Fourier–Sobolev profile at carrier scale, with power `lam^r`
(`app:ch_pairs:eq:pairs-lag-sum-size`, Step 2). Smoothness and Lebesgue L²
membership follow from the SAME cutoff and local phases. These source
profiles feed the original fixed solver's tame bounds; no output estimate is
assumed. The constants precede all phase, cutoff, frequency and sample choices
and do not depend on the requested residual accuracy. -/
theorem exists_signed_modulated_source_sobolev_constants
    {S : Set (Euclidean n)} (hS : IsCompact S)
    (P X C : ℕ → ℝ) (hP : ∀ r, 0 ≤ P r) (hX : ∀ r, 0 ≤ X r)
    (hC : ∀ r, 0 ≤ C r) {Cfreq : ℝ} (hCfreq : 0 ≤ Cfreq) :
    ∃ J : ℕ → ℝ, (∀ r, 0 ≤ J r) ∧
      ∀ (U : Set (Euclidean n)), IsOpen U → ∀ L lam ρp ρm : ℝ,
      1 ≤ L → L ≤ lam → 0 ≤ ρp → 0 ≤ ρm →
      ρp ≤ Cfreq * lam → ρm ≤ Cfreq * lam →
      ∀ (χ φp φm : Euclidean n → ℝ) (A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ),
      ContDiff ℝ ∞ χ → tsupport χ ⊆ S → tsupport χ ⊆ U →
      ContDiffOn ℝ ∞ φp U → ContDiffOn ℝ ∞ φm U →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      (∀ x ∈ U, ∀ r, 1 ≤ r → ‖iteratedFDeriv ℝ r φp x‖ ≤ P r * L ^ (r - 1)) →
      (∀ x ∈ U, ∀ r, 1 ≤ r → ‖iteratedFDeriv ℝ r φm x‖ ≤ P r * L ^ (r - 1)) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ x‖ ≤ X r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r A x‖ ≤ C r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r B x‖ ≤ C r * L ^ r) →
      let p := modulatedSource χ φp (fun y ↦ symmetricBilinearTensor (A y) (B y)) ρp
      let m := modulatedSource χ φm (fun y ↦ symmetricBilinearTensor (A y) ((B y).map conj)) ρm
      ∃ hp : MemLp p 2 volume, ∃ hm : MemLp m 2 volume,
        SobolevEnvelopeBounds p hp 1 lam J ∧ SobolevEnvelopeBounds m hm 1 lam J := by
  obtain ⟨J, hJ, hjet⟩ := exists_signed_modulated_source_jet_constants (n := n) (N := N)
    P X C hP hX hC hCfreq
  obtain ⟨D, hD, hsob⟩ := ResponsePrimarySources.exists_primary_tensor_sobolev_constants hS J hJ
  refine ⟨D, hD, ?_⟩
  intro U hU L lam ρp ρm hL hLlam hρp hρm hρpL hρmL χ φp φm A B
    hχ hχS hχU hφp hφm hA hB hp hm hχb hAb hBb
  dsimp only
  obtain ⟨haps, hams⟩ := contDiffOn_signed_tensor_amplitudes hA hB
  have hjets := hjet U hU L lam ρp ρm hL hLlam hρp hρm hρpL hρmL
    χ φp φm A B hχ.contDiffOn hφp hφm hA hB hp hm hχb hAb hBb
  have hfull (φ : Euclidean n → ℝ) (a : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
      (ρ : ℝ) (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U)
      (haj : ∀ x ∈ U, ∀ j, ‖iteratedFDeriv ℝ j (modulatedSource χ φ a ρ) x‖ ≤ J j * lam ^ j) :
      ∃ hmem : MemLp (modulatedSource χ φ a ρ) 2 volume,
        SobolevEnvelopeBounds (modulatedSource χ φ a ρ) hmem 1 lam D := by
    have hc : ContDiffOn ℝ ∞ (carrier ρ φ) U := by
      change ContDiffOn ℝ ∞ (fun y ↦ Complex.exp (Complex.I * ((ρ * φ y : ℝ) : ℂ))) U
      exact (contDiffOn_const.mul
        (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul hφ))).cexp
    have hf : ContDiff ℝ ∞ (modulatedSource χ φ a ρ) :=
      PrimarySourceAdmission.contDiff_cutoff_of_support_subset hχ hU (hc.smul ha) hχU
    have hs : tsupport (modulatedSource χ φ a ρ) ⊆ tsupport χ :=
      tsupport_smul_subset_left χ (fun y ↦ carrier ρ φ y • a y)
    have hmem : MemLp (modulatedSource χ φ a ρ) 2 volume :=
      hf.continuous.memLp_of_hasCompactSupport
        (hS.of_isClosed_subset (isClosed_tsupport _) (hs.trans hχS))
    refine ⟨hmem, hsob _ hmem 1 lam zero_le_one (hL.trans hLlam) hf (hs.trans hχS) ?_⟩
    intro x j
    simp only [mul_one]
    by_cases hx : x ∈ U
    · exact haj x hx j
    · have hz : iteratedFDeriv ℝ j (modulatedSource χ φ a ρ) x = 0 := by
        by_contra hn
        exact hx (hχU (hs (support_iteratedFDeriv_subset j hn)))
      rw [hz, norm_zero]
      exact mul_nonneg (hJ j) (pow_nonneg ((zero_le_one.trans hL).trans hLlam) j)
  obtain ⟨hpm, hps⟩ := hfull φp _ ρp hφp haps (fun x hx j ↦ (hjets x hx j).1)
  obtain ⟨hmm, hms⟩ := hfull φm _ ρm hφm hams (fun x hx j ↦ (hjets x hx j).2)
  exact ⟨hpm, hmm, hps, hms⟩

end JanetCartan.SignedProductEstimates
