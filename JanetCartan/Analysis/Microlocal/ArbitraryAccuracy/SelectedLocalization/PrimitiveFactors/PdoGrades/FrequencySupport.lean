module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedFactors
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.Diagonal

/-!
# Frequency support of the selected complete-residual PDOs

All four literal symbols retain the original source multiplier, including
the full physical derivative of the algebraic symbol. The doubled threshold
is fixed independently of slow scale and source frequency.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral CharacteristicTransport.CompleteResidual
open RegularSector RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily RegularSector.FinitePdo
open RegularSector.FiniteAlgebraic
open RegularSector.Characteristic.ResidualCoordinates ResidualLocalization
variable {d q : ℕ}
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- The entire physical derivative still vanishes outside the original
source multiplier. No coefficient is removed and no frequency derivative
is confused with the physical derivative (`energy-complete-residual`).
Consumer: the frequency carrier input of `CompleteFactor`. -/
theorem directPDOSymbols_eq_zero_of_multiplier_eq_zero
    (A : (Euclidean (d+1)) → Fin (d+1) → Mat) (B : (Euclidean (d+1)) → Mat) (W : TwoTimeAmplitude d q)
    (bminus : (Euclidean (d+1)) → (Euclidean (d+1)) → Mat) (σ : (Euclidean (d+1)) → Euclidean d → ℂ) (β : (Euclidean (d+1)) → ℂ)
    {ξ : (Euclidean (d+1))} (hξ : β ξ = 0) (j : Fin 4) (x : (Euclidean (d+1))) :
    directPDOSymbols A B W bminus σ β j x ξ = 0 := by
  fin_cases j <;> simp [directPDOSymbols, directAlgebraicSymbol, hξ,
    physicalSymbolApply, partialDeriv]

variable {Ω : Set (Euclidean (d+1))} {x : (Euclidean (d+1))} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- The closed support of the SAME endpoint multiplier excludes zero at
the fixed doubled threshold. This is the support used in the PDO block of
`exists_completePhysicalResidual_restriction_bound`
(`app:ch_regular:lem:finite-chain`). -/
theorem zero_notMem_selectedEndpointMultiplier_tsupport
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {threshold : ℝ} (ht : 0 < threshold) :
    (0 : Euclidean (d+1)) ∉ tsupport (selectedEndpointMultiplier f p threshold) := by
  intro h
  have hreal := tsupport_comp_subset Complex.ofReal_zero
    (dilatedConicMask (f.angularMask p) (2*threshold) ∘ physicalCoordinates (f.chart p).index) h
  have hd := tsupport_comp_subset_preimage
    (dilatedConicMask (f.angularMask p) (2*threshold))
    (physicalCoordinates (f.chart p).index).continuous hreal
  have hn := (dilatedConicMask_tsupport_subset (f.angularMask p)
    (mul_pos (by norm_num) ht) hd).1
  simp only [map_zero, norm_zero] at hn
  linarith

/-- All selected branches, in both literal orientations, have the closed
frequency carrier of the actual doubled source multiplier. The common
physical masks are retained. Consumer: `hFp`, `hzerop`, `hAFp` of
`CompleteFactor` (`app:ch_regular:eq:chain-tail`). -/
theorem selected_directPDO_frequency_support
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {threshold : ℝ} (_ht : 0 < threshold)
    (A : (Euclidean (d+1)) → Fin (d+1) → Mat) (B : (Euclidean (d+1)) → Mat) (W : TwoTimeAmplitude d q)
    (bminus : (Euclidean (d+1)) → (Euclidean (d+1)) → Mat) (σ : (Euclidean (d+1)) → Euclidean d → ℂ)
    (output : (Euclidean (d+1)) → ℝ) :
    let F := tsupport (selectedEndpointMultiplier f p threshold)
    IsClosed F ∧ (0 : (Euclidean (d+1))) ∉ F ∧
      ∀ backward j x y ξ, ξ ∉ F →
        orientedMaskedPDOAmplitude backward (endpointOutputMask f p output) (chartInputMask f p)
          (directPDOSymbols A B W bminus σ (selectedEndpointMultiplier f p threshold) j) x y ξ = 0 := by
  refine ⟨isClosed_tsupport _, zero_notMem_selectedEndpointMultiplier_tsupport f p _ht, ?_⟩
  intro backward j x y ξ hξ
  have hz := directPDOSymbols_eq_zero_of_multiplier_eq_zero A B W bminus σ
    (selectedEndpointMultiplier f p threshold) (image_eq_zero_of_notMem_tsupport hξ) j x
  simp only [orientedMaskedPDOAmplitude, hz, smul_zero, Matrix.conjTranspose_zero, ite_self]

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
