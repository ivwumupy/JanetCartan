module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.Physical
public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.Spectral
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.Sobolev.Coordinates

/-!
# The actual bounded initial defect in Fourier Sobolev spaces

The primitive source estimate now applies to `u - M u`, where `M` is the
bounded realization of the SAME right quantization. The Fourier identity
proves the passage to L². The constants retain the original amplitude budget
and the fixed slow-scale offset, independently of the integration order.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory FourierTransform
open scoped ContDiff

namespace JanetCartan.InitialSourceLocalization

open FiniteChain.Graph JanetCartan.Localization Pseudodifferential
open ResponseTransfer.Complement.InactiveSource

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The source minus its first bounded right proof localizer obeys the
pre-absorption estimate in the genuine Hilbert Sobolev norm. The only inputs
are source regularity, support, phase/amplitude/mask profiles and the actual
physical graph plateau (`app:ch_regular:eq:source-tail`). -/
theorem bounded_initialSource_defect_sobolev_bound
    (m : LocalizerSymbol n) (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m)
    (φ : E → ℝ) (a : E → V)
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
    (M : H →L[ℂ] H)
    (hM : ∀ v : H, M v =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ m (fun y ↦ (v y).ofLp) x))
    (u : H) (hu : u =ᵐ[volume] fun y ↦ phaseOscillation (fun z ↦ ρ * φ z) y • a y)
    {s : ℝ} (hszero : 0 ≤ s) (q : ℕ) (hq : s + (n : ℝ) / 2 < q) :
    MemVectorFourierSobolev s (u - M u) ∧
      vectorFourierSobolevNorm s (u - M u) ≤
        ((r : ℝ) * sourceLocalizationKernelConstant K δ G P D C q *
          Real.sqrt (∫ ξ : E, (1 + ‖ξ‖) ^ (-(2 * (q : ℝ) - 2 * s)))) *
            (A * L ^ b) * (ρ ^ (s + (n : ℝ) / 2) * (L / ρ) ^ q) := by
  let J := fun ξ ↦ complementarySourceFourierKernel m φ a ρ ((2 * Real.pi) • ξ)
  have he := bounded_initialSource_defect_fourier_ae m hm hmc φ a hU hφ ha
    (hs.trans hKU) (hK.of_isClosed_subset (isClosed_tsupport _) hs)
    (zero_lt_one.trans_le hρ).ne' M hM u hu
  have hmeas : AEStronglyMeasurable J volume :=
    (Lp.memLp (𝓕 (u - M u) : H)).aestronglyMeasurable.congr he
  have hB : 0 ≤ sourceLocalizationKernelConstant K δ G P D C q * (A * L ^ b) :=
    mul_nonneg (sourceLocalizationKernelConstant_nonneg K δ G P D C hD hC q)
      (mul_nonneg hA (pow_nonneg (zero_le_one.trans hL) b))
  have hdecay ξ : ‖J ξ‖ ≤
      (sourceLocalizationKernelConstant K δ G P D C q * (A * L ^ b)) *
        (L / (ρ + ‖ξ‖)) ^ q := by
    have hb := norm_complementarySourceFourierKernel_le m hm φ a hU hK hKU hφ ha hs
      hδ hA hL (zero_lt_one.trans_le hρ) b hgraph hplateau hupper
      P D C hP hD hC hmjet hp hajet q ((2 * Real.pi) • ξ)
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ hB
    apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_left (zero_le_one.trans hL) (by positivity)
    have hπ : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    nlinarith [norm_nonneg ξ]
  have hq' : s + (Module.finrank ℝ E : ℝ) / 2 < q := by simpa [Euclidean] using hq
  have hi := integrable_sobolevEnergy_of_scaleRatio hρ hszero hq' hmeas hdecay
  obtain ⟨hmem, hnorm⟩ := vectorSobolev_of_fourier_energy s (u - M u) J hmeas he hi
  refine ⟨hmem, hnorm.trans ?_⟩
  have hb := fourierWeightedL2Norm_le_of_scaleRatio hρ (zero_le_one.trans hL)
    hszero hq' hB hmeas hdecay
  apply (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (Fintype.card (Fin r)))).trans_eq
  simp only [Euclidean, finrank_euclideanSpace_fin, Fintype.card_fin]
  ring

end JanetCartan.InitialSourceLocalization
