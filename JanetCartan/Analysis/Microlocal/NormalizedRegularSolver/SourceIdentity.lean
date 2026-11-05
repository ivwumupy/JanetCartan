module

public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.Operators
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.PairedFourier

/-!
# The exact normalized source with its physical masks

The literal completed source is the multiplier of `gammaTotal`, at the
original physical frequency and low collar. Conjugation reflects the Fourier
symbol and preserves the order of the real position masks. No source mask
is commuted through a Fourier multiplier.
Consumers: the fixed inverse's `Bobs` and `resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory FourierTransform
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.NormalizedSolver
open FiniteMasks FiniteMasks.ActualFamily EllipticComplement FiniteAssembly Realization
open Characteristic.EvolutionIntegral FourierIntegral.LowBounds
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)

/-- Reflection preserves the order of whole physical factors
(`energy-complete-residual`). -/
private theorem boundedConjugate_comp (S T : H →L[ℂ] H) :
    boundedConjugate (S.comp T) = (boundedConjugate S).comp (boundedConjugate T) := by
  ext1 u
  change star (S (T (star u))) = star (S (star (star (T (star u)))))
  rw [star_star]

/-- The original real position masks are fixed by literal conjugation
(`energy-complete-residual`). -/
private theorem boundedConjugate_sourceCutMultiplier
    (χ : E → ℝ) (hc : Continuous χ) (hb : ∀ y, ‖χ y‖ ≤ 1) :
    boundedConjugate (sourceCutMultiplier (r := d+1) χ hc hb) = sourceCutMultiplier χ hc hb := by
  ext1 u
  change star (sourceCutMultiplier χ hc hb (star u)) = _
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (sourceCutMultiplier χ hc hb (star u)),
    sourceCutMultiplier_coeFn χ hc hb (star u), Lp.coeFn_star u,
    sourceCutMultiplier_coeFn χ hc hb u] with y hs hm hu hn
  rw [hs, Pi.star_apply, hm, hu, Pi.star_apply, hn]
  simp only [star_smul, star_star, Complex.star_def, Complex.conj_ofReal]

/-- The physical Fourier representative keeps the `2π` conversion
(`resolved-angular-tail`). -/
private theorem scalarPhysicalFrequencyOperator_fourier_ae
    (b : E → ℝ) (hb : Continuous b) (hbb : ∀ ξ, ‖b ξ‖ ≤ 1) (u : H) :
    (𝓕 (scalarPhysicalFrequencyOperator b hb hbb u) : H) =ᵐ[volume]
      fun ξ ↦ (b ((2*Real.pi) • ξ) : ℂ) • (𝓕 u : H) ξ := by
  simp only [scalarPhysicalFrequencyOperator, ContinuousLinearMap.comp_apply,
    fourierInvCLM_apply, fourierCLM_apply, fourier_fourierInv_eq]
  exact sourceCutMultiplier_coeFn _ _ _ _

/-- External half-normalization commutes with addition of the literal scalar
Fourier operators, including the low shoulder (`sector-theorem-identity`). -/
private theorem scalarPhysicalFrequencyOperator_average
    (b c a : E → ℝ) (hb : Continuous b) (hc : Continuous c) (ha : Continuous a)
    (hbb : ∀ ξ, ‖b ξ‖ ≤ 1) (hcb : ∀ ξ, ‖c ξ‖ ≤ 1) (hab : ∀ ξ, ‖a ξ‖ ≤ 1)
    (he : ∀ ξ, a ξ = (b ξ + c ξ)/2) :
    (1/2 : ℂ) • (scalarPhysicalFrequencyOperator (r := d+1) b hb hbb +
      scalarPhysicalFrequencyOperator c hc hcb) = scalarPhysicalFrequencyOperator a ha hab := by
  ext1 u
  apply (Lp.fourierTransformₗᵢ E V).injective
  simp only [smul_apply, add_apply, map_smul, map_add]
  change ((1/2 : ℂ) • (𝓕 (scalarPhysicalFrequencyOperator b hb hbb u) +
    𝓕 (scalarPhysicalFrequencyOperator c hc hcb u)) : H) =
      𝓕 (scalarPhysicalFrequencyOperator a ha hab u)
  apply Lp.ext
  filter_upwards [scalarPhysicalFrequencyOperator_fourier_ae b hb hbb u,
    scalarPhysicalFrequencyOperator_fourier_ae c hc hcb u,
    scalarPhysicalFrequencyOperator_fourier_ae a ha hab u,
    Lp.coeFn_smul (1/2 : ℂ)
      (𝓕 (scalarPhysicalFrequencyOperator b hb hbb u) +
        𝓕 (scalarPhysicalFrequencyOperator c hc hcb u)),
    Lp.coeFn_add (𝓕 (scalarPhysicalFrequencyOperator b hb hbb u))
      (𝓕 (scalarPhysicalFrequencyOperator c hc hcb u))]
    with ξ hbξ hcξ haξ hs hsum
  rw [hs, Pi.smul_apply, hsum, Pi.add_apply, hbξ, hcξ, haξ, he]
  simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat,
    ← add_smul, smul_smul]
  congr 1
  ring

variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- The scalar Fourier operator of the actual normalized source, using
the original physical-frequency convention (`resolved-angular-tail`). -/
def sourceFourierOperator (L : ℝ) : H →L[ℂ] H :=
  scalarPhysicalFrequencyOperator (normalizedSourceMask f hK L)
    (normalizedSourceMask_properties f hK L).1.continuous
    (fun ξ ↦ (Real.norm_of_nonneg ((normalizedSourceMask_properties f hK L).2 ξ).1).trans_le
      ((normalizedSourceMask_properties f hK L).2 ξ).2)

/-- The normalized full Fourier source has its literal representative at
physical covector `2πξ` (`resolved-angular-tail`). -/
theorem sourceFourierOperator_fourier_ae (L : ℝ) (u : H) :
    (𝓕 (sourceFourierOperator f hK L u) : H) =ᵐ[volume]
      fun ξ ↦ (normalizedSourceMask f hK L ((2*Real.pi) • ξ) : ℂ) • (𝓕 u : H) ξ :=
  scalarPhysicalFrequencyOperator_fourier_ae _ _ _ u

/-- Exact normalization of the actual full Fourier source, using the
published reflection leaf (`sector-theorem-identity`, `resolved-angular-tail`). -/
theorem normalizedPair_fullSourceFrequency (L : ℝ) :
    let b := dilatedConicMask (fullSourceAngularMask f hK) (2*L)
    let hb := (contDiff_dilatedConicMask (fullSourceAngularMask_properties f hK).1 (2*L)).continuous
    let hbb := fun ξ ↦ (Real.norm_of_nonneg
      (conicMask_mem_Icc (fullSourceAngularMask_properties f hK).2.1 ((2*L)⁻¹ • ξ)).1).trans_le
        (conicMask_mem_Icc (fullSourceAngularMask_properties f hK).2.1 ((2*L)⁻¹ • ξ)).2
    normalizedPair (scalarPhysicalFrequencyOperator (r := d+1) b hb hbb) =
      sourceFourierOperator f hK L := by
  intro b hb hbb
  rw [normalizedPair_eq, SignedProductEstimates.boundedConjugate_scalarPhysicalFrequencyOperator_reflection]
  exact scalarPhysicalFrequencyOperator_average b (fun ξ ↦ b (-ξ))
    (normalizedSourceMask f hK L) hb (hb.comp continuous_neg) _ hbb (fun ξ ↦ hbb (-ξ)) _
    (normalizedSourceMask_eq_average f hK L)

/-- The normalized paired source is EXACTLY the complete scalar Fourier
operator between the original physical masks. This equality holds on all
L² data, with no high-frequency or source-support assumption
(`sector-theorem-identity`, `resolved-angular-tail`). -/
theorem pairedSource_eq_fourier_composition {L : ℝ} (hL : f.radialThreshold ≤ L)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1) :
    pairedSource f hK L output ho hob =
      (sourceCutMultiplier output ho hob).comp
        ((sourceCutMultiplier f.outputMask f.outputMask_smooth.continuous
          (fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2)).comp
          ((sourceFourierOperator f hK L).comp
            (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous
              (fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2)))) := by
  let b := dilatedConicMask (fullSourceAngularMask f hK) (2*L)
  have hb : Continuous b :=
    (contDiff_dilatedConicMask (fullSourceAngularMask_properties f hK).1 _).continuous
  have hbb (ξ : E) : ‖b ξ‖ ≤ 1 :=
    (Real.norm_of_nonneg (conicMask_mem_Icc (fullSourceAngularMask_properties f hK).2.1
      ((2*L)⁻¹ • ξ)).1).trans_le
      (conicMask_mem_Icc (fullSourceAngularMask_properties f hK).2.1 ((2*L)⁻¹ • ξ)).2
  let F := scalarPhysicalFrequencyOperator (r := d+1) b hb hbb
  have he : selectedFiniteSourcePDO f L + ellipticSourcePDO f hK L =
      (sourceCutMultiplier f.outputMask f.outputMask_smooth.continuous
        (fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2)).comp
      (F.comp (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous
        (fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2))) := by
    rw [selectedFiniteSourcePDO_add_ellipticSourcePDO f hK hL]
    exact maskedPhysicalPDO_scalarFrequency_eq b hb hbb
      (hasTemperateGrowth_complex_dilatedConicMask (fullSourceAngularMask_properties f hK).1 _)
      _ _ f.outputMask_smooth.continuous f.inputMask_smooth _ _
  have hF : normalizedPair F = sourceFourierOperator f hK L := normalizedPair_fullSourceFrequency f hK L
  rw [pairedSource, he, ← hF]
  simp only [normalizedPair_eq, boundedConjugate_comp, boundedConjugate_sourceCutMultiplier]
  ext1 u
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, map_smul, map_add]

/-- Literal adjunction reverses the original masks while the real scalar
Fourier multiplier is self-adjoint (`measured-adjoint`). -/
theorem pairedSource_adjoint_eq_fourier_composition {L : ℝ} (hL : f.radialThreshold ≤ L)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1) :
    (pairedSource f hK L output ho hob).adjoint =
      (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous
        (fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2)).comp
        ((sourceFourierOperator f hK L).comp
          ((sourceCutMultiplier f.outputMask f.outputMask_smooth.continuous
            (fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2)).comp
            (sourceCutMultiplier output ho hob))) := by
  rw [pairedSource_eq_fourier_composition f hK hL output ho hob]
  simp only [ContinuousLinearMap.adjoint_comp, sourceCutMultiplier_adjoint,
    sourceFourierOperator, scalarPhysicalFrequencyOperator_adjoint,
    ContinuousLinearMap.comp_assoc]

end JanetCartan.RegularSector.NormalizedSolver
