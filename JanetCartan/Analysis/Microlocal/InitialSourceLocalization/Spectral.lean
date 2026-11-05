module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.FourierKernel
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.CompactIntegral

/-!
# Weighted Fourier bounds for the initial source defect

The actual complementary amplitude has compact source support. This gives
smoothness of its Fourier kernel, and the proved nonstationary estimate gives
weighted integrability and the exact factor `rho^(s+n/2) (L/rho)^q`.
The loss `L^b` remains fixed before the requested accuracy.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.InitialSourceLocalization

open FiniteChain.Graph JanetCartan.Localization
open FiniteChain.Retarded.KernelDecay

variable {n : ℕ} {F : Type} [NormedAddCommGroup F]
  [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
local notation "E" => Euclidean n

/-- Smoothness of the literal complementary Fourier kernel is derived from
the original compact amplitude and its phase neighborhood
(`app:ch_regular:eq:source-tail`). -/
theorem contDiff_complementarySourceFourierKernel
    (m : LocalizerSymbol n) (hm : ContDiff ℝ ∞ m) (φ : E → ℝ) (a : E → F)
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hs : tsupport a ⊆ K) (ρ : ℝ) :
    ContDiff ℝ ∞ (complementarySourceFourierKernel m φ a ρ) := by
  let J : E × E → F := fun p ↦
    phaseOscillation (fourierPhase φ ρ (InnerProductSpace.toDual ℝ E p.1)) p.2 •
      complementarySourceAmplitude m a (ρ⁻¹ • p.1) p.2
  have hphase : ContDiffOn ℝ ∞ (fun p : E × E ↦
      ρ * φ p.2 - inner ℝ p.1 p.2) (univ ×ˢ U) :=
    ((hφ.comp contDiffOn_snd (fun _ hp ↦ hp.2)).const_smul ρ).sub
      (contDiff_fst.inner ℝ contDiff_snd).contDiffOn
  have hJ : ContDiffOn ℝ ∞ J (univ ×ˢ U) := by
    exact (((Complex.ofRealCLM.contDiff.comp_contDiffOn hphase).mul
      contDiffOn_const).cexp.smul
      ((contDiff_const.sub (Complex.ofRealCLM.contDiff.comp
        (hm.comp (contDiff_snd.prodMk (contDiff_fst.const_smul ρ⁻¹))))).contDiffOn.smul
        (ha.comp contDiffOn_snd (fun _ hp ↦ hp.2))))
  have hsupport : tsupport J ⊆ Prod.snd ⁻¹' tsupport a := by
    apply closure_minimal _ ((isClosed_tsupport a).preimage continuous_snd)
    intro p hp
    apply subset_tsupport a
    intro hz
    exact hp (by simp [J, complementarySourceAmplitude, hz])
  have hJglobal : ContDiff ℝ ∞ J :=
    contDiff_of_contDiffOn_support_neighborhood (isOpen_univ.prod hU) hJ
      (fun p hp ↦ ⟨mem_univ _, hKU (hs (hsupport hp))⟩)
  exact contDiff_integral_commonCarrier (μ := volume) hJglobal hK (fun ξ y hy ↦ by
    have hz : a y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hs h))
    simp [J, complementarySourceAmplitude, hz])

/-- The constant in the initial-source integration-by-parts estimate,
chosen before masks, phases, amplitudes and scales
(`app:ch_regular:eq:source-tail`). -/
def sourceLocalizationKernelConstant (K : Set E) (δ G : ℝ)
    (P D C : ℕ → ℝ) (q : ℕ) : ℝ :=
  transposeDerivativeConstant (EuclideanSpace.basisFun (Fin n) ℝ)
    (phaseCoefficientDerivativeBound (EuclideanSpace.basisFun (Fin n) ℝ)
      ((δ / 2 / (1 + G + δ / 2)) ^ 2) (max G 1) P)
    (derivativeConvolution (fun j ↦ 1 + D j) C) q 0 * volume.real K

/-- Nonnegative primitive profiles give a nonnegative source constant
(`app:ch_regular:eq:source-tail`). -/
theorem sourceLocalizationKernelConstant_nonneg (K : Set E) (δ G : ℝ)
    (P D C : ℕ → ℝ) (hD : ∀ j, 0 ≤ D j) (hC : ∀ j, 0 ≤ C j) (q : ℕ) :
    0 ≤ sourceLocalizationKernelConstant K δ G P D C q :=
  mul_nonneg (transposeDerivativeConstant_nonneg (EuclideanSpace.basisFun (Fin n) ℝ)
    (phaseCoefficientDerivativeBound_nonneg _ _ _ _)
    (derivativeConvolution_nonneg (A := fun j ↦ 1 + D j)
      (fun j ↦ by linarith [hD j]) hC) q 0) measureReal_nonneg

/-- The physical Fourier kernel has integrable Sobolev energy and the
pre-absorption bound with fixed exponents `s+n/2` and `b`. No spectral tail,
wavefront inclusion or Sobolev estimate is an input
(`app:ch_regular:eq:source-tail`, `app:ch_osc:prop:osc-source-shell`). -/
theorem complementarySourceFourierKernel_sobolev_bound
    (m : LocalizerSymbol n) (hm : ContDiff ℝ ∞ m) (φ : E → ℝ) (a : E → F)
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U) (hs : tsupport a ⊆ K)
    {S : Set (E × E)} {δ G A L ρ : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A)
    (hL : 1 ≤ L) (hρ : 1 ≤ ρ) (b : ℕ)
    (hgraph : ∀ y ∈ tsupport a, (y, gradient φ y) ∈ S)
    (hplateau : cthickening δ S ⊆ interior {p | m p = 1})
    (hupper : ∀ y ∈ U, ‖fderiv ℝ φ y‖ ≤ G)
    (P D C : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (hD : ∀ j, 0 ≤ D j)
    (hC : ∀ j, 0 ≤ C j)
    (hmjet : ∀ j p, ‖iteratedFDeriv ℝ j m p‖ ≤ D j)
    (hp : ∀ y ∈ tsupport a, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) φ y‖ ≤ P j * L ^ j)
    (hajet : ∀ y ∈ tsupport a, ∀ j,
      ‖iteratedFDeriv ℝ j a y‖ ≤ C j * ((A * L ^ b) * L ^ j))
    {s : ℝ} (hszero : 0 ≤ s) (q : ℕ) (hq : s + (n : ℝ) / 2 < q) :
    Integrable (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ s *
      ‖complementarySourceFourierKernel m φ a ρ ξ‖ ^ 2) ∧
    fourierWeightedL2Norm volume s (complementarySourceFourierKernel m φ a ρ) ≤
      (sourceLocalizationKernelConstant K δ G P D C q *
        Real.sqrt (∫ ξ : E, (1 + ‖ξ‖) ^ (-(2 * (q : ℝ) - 2 * s)))) *
          (A * L ^ b) * (ρ ^ (s + (n : ℝ) / 2) * (L / ρ) ^ q) := by
  have hdecay ξ := norm_complementarySourceFourierKernel_le m hm φ a hU hK hKU
    hφ ha hs hδ hA hL (zero_lt_one.trans_le hρ) b hgraph hplateau hupper
    P D C hP hD hC hmjet hp hajet q ξ
  have hmeas := (contDiff_complementarySourceFourierKernel m hm φ a hU hK hKU
    hφ ha hs ρ).continuous.aestronglyMeasurable (μ := volume)
  have hq' : s + (Module.finrank ℝ E : ℝ) / 2 < q := by simpa [Euclidean] using hq
  refine ⟨integrable_sobolevEnergy_of_scaleRatio hρ hszero hq' hmeas hdecay, ?_⟩
  have hnonneg : 0 ≤ sourceLocalizationKernelConstant K δ G P D C q * (A * L ^ b) :=
    mul_nonneg (sourceLocalizationKernelConstant_nonneg K δ G P D C hD hC q)
      (mul_nonneg hA (pow_nonneg (zero_le_one.trans hL) b))
  have hb := fourierWeightedL2Norm_le_of_scaleRatio hρ (zero_le_one.trans hL)
    hszero hq' hnonneg hmeas hdecay
  apply hb.trans_eq
  simp only [Euclidean, finrank_euclideanSpace_fin]
  ring

end JanetCartan.InitialSourceLocalization
