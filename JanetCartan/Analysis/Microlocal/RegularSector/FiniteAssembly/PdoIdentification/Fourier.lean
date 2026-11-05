module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.PdoIdentification.Masking

/-!
# Fourier identification of the finite source

Only position multipliers and scalar Fourier multipliers are transported here.
The original source multiplier remains before Fourier transformation throughout.
Consumer: `selectedFiniteSourcePDO_commonOutput`, the source term and full
identity defect of `energy-complete-residual` and `prop:complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory FourierTransform
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral FiniteEvolution
open FourierIntegral LowBounds
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d q

/-- Scalar physical-frequency transport through the actual coordinate pullback,
with the explicit cycle-to-physical conversion `2πξ`. Consumer: each source
chart in `energy-complete-residual`. -/
theorem physicalPullbackL2_scalarPhysicalFrequencyOperator
    (i : Fin (d+1)) (b : E → ℝ) (hb : Continuous b) (hbb : ∀ ξ, ‖b ξ‖ ≤ 1) (u : H) :
    physicalPullbackL2 i (scalarPhysicalFrequencyOperator b hb hbb u) =
      scalarPhysicalFrequencyOperator (b ∘ physicalCoordinates i)
        (hb.comp (physicalCoordinates i).continuous) (fun _ ↦ hbb _) (physicalPullbackL2 i u) := by
  apply (Lp.fourierTransformₗᵢ E (EuclideanSpace ℂ (Fin q))).injective
  change 𝓕 (physicalPullbackL2 i (𝓕⁻ (sourceCutMultiplier
    (fun ξ ↦ b ((2*Real.pi) • ξ)) (by fun_prop) (fun _ ↦ hbb _) (𝓕 u)))) =
    𝓕 (𝓕⁻ (sourceCutMultiplier (fun ξ ↦ b (physicalCoordinates i ((2*Real.pi) • ξ)))
      (by fun_prop) (fun _ ↦ hbb _) (𝓕 (physicalPullbackL2 i u))))
  rw [physicalPullbackL2_fourier, fourier_fourierInv_eq, fourier_fourierInv_eq,
    physicalPullbackL2_sourceCutMultiplier, physicalPullbackL2_fourier]
  congr 2
  funext ξ
  exact congrArg b ((physicalCoordinates i).map_smul (2 * Real.pi) ξ).symm

/-- Conjugate a literal masked scalar Fourier composition. Both masks are
transported in their original order (`fixed-time-representation`,
`measured-adjoint`); no Fourier multiplier crosses a position mask. -/
theorem physicalOperator_scalarFourier_masks
    (i : Fin (d+1)) (output input b : E → ℝ)
    (ho : Continuous output) (hi : Continuous input) (hb : Continuous b)
    (hob : ∀ y, ‖output y‖ ≤ 1) (hib : ∀ y, ‖input y‖ ≤ 1) (hbb : ∀ ξ, ‖b ξ‖ ≤ 1) :
    physicalOperator (q := q) i
      ((sourceCutMultiplier (output ∘ physicalCoordinates i)
        (ho.comp (physicalCoordinates i).continuous) (fun _ ↦ hob _)).comp
        ((scalarPhysicalFrequencyOperator (b ∘ physicalCoordinates i)
          (hb.comp (physicalCoordinates i).continuous) (fun _ ↦ hbb _)).comp
          (sourceCutMultiplier (input ∘ physicalCoordinates i)
            (hi.comp (physicalCoordinates i).continuous) (fun _ ↦ hib _)))) =
      (sourceCutMultiplier output ho hob).comp
        ((scalarPhysicalFrequencyOperator b hb hbb).comp (sourceCutMultiplier input hi hib)) := by
  ext1 u
  apply (physicalPullbackL2 i).injective
  simp only [physicalOperator_apply, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.apply_symm_apply, physicalPullbackL2_sourceCutMultiplier,
    physicalPullbackL2_scalarPhysicalFrequencyOperator]

/-- Finite scalar Fourier sums are identified on their literal Lebesgue L²
representatives, rather than by assuming linearity of the canonical PDO.
Consumer: the finite source assembly (`prop:complete-residual`). -/
theorem scalarPhysicalFrequencyOperator_sum {ι : Type*} [Fintype ι]
    (b : ι → E → ℝ) (hb : ∀ p, Continuous (b p)) (hbb : ∀ p ξ, ‖b p ξ‖ ≤ 1)
    (hs : ∀ ξ, ‖∑ p, b p ξ‖ ≤ 1) :
    (∑ p, scalarPhysicalFrequencyOperator (r := q) (b p) (hb p) (hbb p)) =
      scalarPhysicalFrequencyOperator (fun ξ ↦ ∑ p, b p ξ)
        (continuous_finsetSum _ fun p _ ↦ hb p) hs := by
  classical
  ext1 u
  apply (Lp.fourierTransformₗᵢ E (EuclideanSpace ℂ (Fin q))).injective
  simp only [sum_apply, map_sum]
  change (∑ p, 𝓕 (𝓕⁻ (sourceCutMultiplier (fun ξ ↦ b p ((2*Real.pi) • ξ)) (by fun_prop) (fun _ ↦ hbb p _) (𝓕 u)))) =
    𝓕 (𝓕⁻ (sourceCutMultiplier (fun ξ ↦ ∑ p, b p ((2*Real.pi) • ξ)) (by fun_prop) (fun _ ↦ hs _) (𝓕 u)))
  simp only [fourier_fourierInv_eq]
  apply Lp.ext
  have hall := ae_all_iff.mpr fun p ↦ sourceCutMultiplier_coeFn
    (fun ξ ↦ b p ((2*Real.pi) • ξ)) (by fun_prop) (fun _ ↦ hbb p _) (𝓕 u)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun p ↦ sourceCutMultiplier (fun ξ ↦ b p ((2*Real.pi) • ξ))
        (by fun_prop) (fun _ ↦ hbb p _) (𝓕 u)), hall,
    sourceCutMultiplier_coeFn (fun ξ ↦ ∑ p, b p ((2*Real.pi) • ξ))
      (by fun_prop) (fun _ ↦ hs _) (𝓕 u)] with ξ hξ hp ht
  simp only [Finset.sum_apply] at hξ
  rw [hξ, ht]
  simp only [hp, Complex.ofReal_sum, Finset.sum_smul]

end JanetCartan.RegularSector.FiniteAssembly
