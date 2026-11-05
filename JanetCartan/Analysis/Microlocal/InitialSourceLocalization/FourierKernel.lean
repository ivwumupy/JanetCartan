module

public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.Amplitude
public import JanetCartan.Analysis.Microlocal.Localization.AveragedKernel

/-!
# Nonstationary decay of the initial right-localizer Fourier defect

The integrand is the original modulated amplitude times the single
complementary right symbol. Its derivative gap is proved from the physical
graph plateau. All constants below use only the fixed compact carrier,
thickening and phase/amplitude/mask profiles. The physical Fourier transform
and Sobolev realizations are the consumers of this leaf.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.InitialSourceLocalization

open FiniteChain.Graph JanetCartan.Localization
open FiniteChain.Retarded.KernelDecay

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
local notation "E" => Euclidean n

/-- The unnormalized physical Fourier kernel for the initial source minus
its actual right localizer. The factor `(2*pi)^(-n)` is inserted only when
identifying the manuscript's Fourier density
(`app:ch_regular:eq:source-tail`, `app:ch_regular:lem:finite-chain`). -/
def complementarySourceFourierKernel (m : LocalizerSymbol n) (φ : E → ℝ)
    (a : E → F) (ρ : ℝ) (ξ : E) : F :=
  ∫ y, phaseOscillation (fourierPhase φ ρ (InnerProductSpace.toDual ℝ E ξ)) y •
    complementarySourceAmplitude m a (ρ⁻¹ • ξ) y

/-- Repeated integration by parts for the literal complementary right
symbol. The support gap and reciprocal-coefficient derivatives are derived
from the physical graph plateau and primitive profiles. The single fixed
amplitude loss `L^b` is independent of `q`
(`app:ch_regular:eq:source-tail`, `app:ch_regular:eq:chain-tail`). -/
theorem norm_complementarySourceFourierKernel_le
    (m : LocalizerSymbol n) (hm : ContDiff ℝ ∞ m) (φ : E → ℝ) (a : E → F)
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ ∞ φ U) (ha : ContDiffOn ℝ ∞ a U) (hs : tsupport a ⊆ K)
    {S : Set (E × E)} {δ G A L ρ : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A)
    (hL : 1 ≤ L) (hρ : 0 < ρ) (b : ℕ)
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
    (q : ℕ) (ξ : E) :
    ‖complementarySourceFourierKernel m φ a ρ ξ‖ ≤
      (transposeDerivativeConstant (EuclideanSpace.basisFun (Fin n) ℝ)
        (phaseCoefficientDerivativeBound (EuclideanSpace.basisFun (Fin n) ℝ)
          ((δ / 2 / (1 + G + δ / 2)) ^ 2) (max G 1) P)
        (derivativeConvolution (fun j ↦ 1 + D j) C) q 0 * volume.real K) *
          (A * L ^ b) * (L / (ρ + ‖ξ‖)) ^ q := by
  have hLzero : 0 ≤ L := zero_le_one.trans hL
  by_cases hsupport : (tsupport a).Nonempty
  swap
  · have ha0 : a = 0 := by
      ext y
      exact image_eq_zero_of_notMem_tsupport (fun hy ↦ hsupport ⟨y, hy⟩)
    rw [ha0]
    simp only [complementarySourceFourierKernel, complementarySourceAmplitude,
      Pi.zero_apply, smul_zero, integral_zero, norm_zero]
    have hB := transposeDerivativeConstant_nonneg (EuclideanSpace.basisFun (Fin n) ℝ)
      (phaseCoefficientDerivativeBound_nonneg (EuclideanSpace.basisFun (Fin n) ℝ)
        ((δ / 2 / (1 + G + δ / 2)) ^ 2) (max G 1) P)
      (derivativeConvolution_nonneg (A := fun j ↦ 1 + D j)
        (fun j ↦ by linarith [hD j]) hC) q 0
    exact mul_nonneg (mul_nonneg (mul_nonneg hB measureReal_nonneg)
      (mul_nonneg hA (pow_nonneg hLzero b)))
      (pow_nonneg (div_nonneg hLzero (add_nonneg hρ.le (norm_nonneg ξ))) q)
  obtain ⟨y₀, hy₀⟩ := hsupport
  have hG : 0 ≤ G := (norm_nonneg _).trans (hupper y₀ (hKU (hs hy₀)))
  let η := ρ⁻¹ • ξ
  let a' := complementarySourceAmplitude m a η
  let V := U ∩ {y | δ / 2 < ‖gradient φ y - η‖}
  let γ := δ / 2 / (1 + G + δ / 2)
  let C' := derivativeConvolution (fun j ↦ 1 + D j) C
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hC' j : 0 ≤ C' j :=
    derivativeConvolution_nonneg (fun j ↦ by linarith [hD j]) hC j
  have hgcont : ContinuousOn (fun y ↦ ‖gradient φ y - η‖) U :=
    (((InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
      (hφ.continuousOn_fderiv_of_isOpen hU (by simp))).sub continuousOn_const).norm
  have hV : IsOpen V := hgcont.isOpen_inter_preimage hU isOpen_Ioi
  have hVs : V ⊆ U := inter_subset_left
  have has : tsupport a' ⊆ tsupport a := tsupport_complementarySourceAmplitude_subset m a η
  have hsV : tsupport a' ⊆ V := by
    intro y hy
    refine ⟨hKU (hs (has hy)), ?_⟩
    have h := gradient_gap_on_complementarySourceAmplitude m a φ hgraph hplateau η y hy
    change δ / 2 < ‖gradient φ y - η‖
    linarith
  have hac : HasCompactSupport a' :=
    hK.of_isClosed_subset (isClosed_tsupport _) (has.trans hs)
  have ha' : ContDiffOn ℝ ∞ a' V :=
    (contDiffOn_complementarySourceAmplitude m hm a ha η).mono hVs
  have hψ : ContDiffOn ℝ ∞ (fourierPhase φ ρ (InnerProductSpace.toDual ℝ E ξ)) V :=
    ((hφ.mono hVs).const_smul ρ).sub
      (InnerProductSpace.toDual ℝ E ξ).contDiff.contDiffOn
  have hj y (hy : y ∈ tsupport a') j :
      ‖iteratedFDeriv ℝ j a' y‖ ≤ C' j * ((A * L ^ b) * L ^ j) :=
    norm_iteratedFDeriv_complementarySourceAmplitude_le m hm a hU ha (hs.trans hKU)
      D C hD hmjet hL b η y (hajet y (has hy)) j
  have hgap' : ∀ y ∈ V, γ ^ 2 * (ρ + ‖ξ‖) ^ 2 ≤
      phaseGradientSquare (EuclideanSpace.basisFun (Fin n) ℝ)
        (fourierPhase φ ρ (InnerProductSpace.toDual ℝ E ξ)) y := by
    intro y hy
    rw [phaseGradientSquare_orthonormalBasis, fderiv_fourierPhase φ ρ _
      ((hφ.contDiffAt (hU.mem_nhds hy.1)).differentiableAt (by simp))]
    have hg := physical_fourier_gap_of_normalized_gradient_gap φ hρ (half_pos hδ)
      ξ y (hupper y hy.1) hy.2.le
    simpa only [mul_pow] using pow_le_pow_left₀
      (mul_nonneg hγ.le (add_nonneg hρ.le (norm_nonneg ξ))) hg 2
  have hupper' : ∀ y ∈ V,
      ‖fderiv ℝ (fourierPhase φ ρ (InnerProductSpace.toDual ℝ E ξ)) y‖ ≤
        max G 1 * (ρ + ‖ξ‖) := by
    intro y hy
    simpa only [LinearIsometryEquiv.norm_map] using norm_fderiv_fourierPhase_le
      hU φ (InnerProductSpace.toDual ℝ E ξ) hφ hρ.le hy.1 (hupper y hy.1)
  have hp' : ∀ y ∈ tsupport a', ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (fourierPhase φ ρ (InnerProductSpace.toDual ℝ E ξ)) y‖ ≤
        P j * (ρ + ‖ξ‖) * L ^ j := by
    intro y hy j hjpos
    rw [norm_iteratedFDeriv_fourierPhase hU φ ρ _ hφ (hKU (hs (has hy))) hjpos,
      abs_of_pos hρ]
    calc
      _ ≤ ρ * (P j * L ^ j) := mul_le_mul_of_nonneg_left (hp y (has hy) j hjpos) hρ.le
      _ ≤ P j * (ρ + ‖ξ‖) * L ^ j := by
        nlinarith [mul_nonneg (mul_nonneg (hP j) (norm_nonneg ξ))
          (pow_nonneg (zero_le_one.trans hL) j)]
  have hbound := norm_vector_oscillatory_integral_le (μ := volume) hV
    (EuclideanSpace.basisFun (Fin n) ℝ)
    (fourierPhase φ ρ (InnerProductSpace.toDual ℝ E ξ)) a' q hψ ha' hsV hac
    (sq_pos_of_pos hγ) (mul_nonneg hA (pow_nonneg hLzero b))
    hLzero (add_pos_of_pos_of_nonneg hρ (norm_nonneg ξ)) hgap' hupper' hC' hp' hj
  have hB := transposeDerivativeConstant_nonneg (EuclideanSpace.basisFun (Fin n) ℝ)
    (phaseCoefficientDerivativeBound_nonneg (EuclideanSpace.basisFun (Fin n) ℝ)
      (γ ^ 2) (max G 1) P) hC' q 0
  apply hbound.trans
  calc
    _ ≤ (transposeDerivativeConstant (EuclideanSpace.basisFun (Fin n) ℝ)
        (phaseCoefficientDerivativeBound (EuclideanSpace.basisFun (Fin n) ℝ)
          (γ ^ 2) (max G 1) P) C' q 0 *
          ((A * L ^ b) * (L / (ρ + ‖ξ‖)) ^ q)) * volume.real K :=
      mul_le_mul_of_nonneg_left (measureReal_mono (has.trans hs) hK.measure_lt_top.ne)
        (by positivity)
    _ = _ := by dsimp only [γ, C']; ring

end JanetCartan.InitialSourceLocalization
