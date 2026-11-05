module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.TailSymbols.SourceSlice
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SelectedPdoEnvelopeApplication.TailSymbols.Masks
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.LocalCalculus
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.AlgebraicSums

/-!
# Actual algebraic symbol inputs for the complete PDO tail

The selected inverse retains the normal certificate and original `j+1`
coordinate budget for both literal algebraic symbols. Recover the symbol
with its original chart output, multiply by the actual smaller output, and
use the supplied coefficient reserve. No frequency truncation is used.

Consumer: `FullEllipticResidualEnvelopes.completeDiagonalAnnularComplement_sobolev`
(`app:ch_response:eq:direct-envelope-profile`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
open TailSymbols ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteMasks.ActualFamily RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open RegularSector.FiniteAssembly RegularSector.Characteristic.PdoRealization
open RegularSector.Characteristic.ResidualCoordinates
open CharacteristicTransport.CompleteResidual FourierIntegral AmplitudeBound
open FiniteChain.Retarded.KernelDecay

variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- Global physical symbol profiles for both actual algebraic entries, using
the original retained normal and coordinate certificates. Their actual
producer is the `halgebraic` clause of the supplied selected inverse; the
both-entry extraction is `exists_supplied_algebraic_tail_coordinate_certificates`.
The one-derivative coefficient reserve suffices. The exact smaller output
is retained in the symbol, normal certificate and bounded operator
(`app:ch_regular_base:eq:energy-complete-residual`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_selected_algebraic_tail_symbol_profiles
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hos : tsupport output ⊆ ball x f.physicalRadius)
    (threshold : ℝ) (D AQ AB : ℕ → ℝ)
    (hD : ∀ j, 0 ≤ D j) (hAQ : ∀ j, 0 ≤ AQ j) (hAB : ∀ j, 0 ≤ AB j) :
    ∃ Bσ : ℕ → ℝ, (∀ j, 0 ≤ Bσ j) ∧
      ∀ Rcoef : ℕ, 1 ≤ Rcoef → ∀ L : ℝ, 1 ≤ L →
      ∀ (Q : E → Coeff) (B : E → Mat),
        (∀ j, cNorm (closedBall x RQ) j Q ≤ AQ j * L^(j-Rcoef)) →
        (∀ j, cNorm (closedBall x RQ) j B ≤ AB j * L^(j-Rcoef)) →
      ∀ (o : Fin 2) (R N : ℝ),
        GraphNormalAmplitudeBounds
          (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) Q B o)) R N →
        (∀ j ξ is, is.length ≤ j → ∀ z,
          (1+‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
            (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
              (selectedAlgebraicSymbol f p (2*threshold) Q B o) ξ) z‖ ≤
                D j * (1+cNorm (closedBall x RQ) (j+1) Q+cNorm (closedBall x RQ) (j+1) B)) →
        let σa := fun y ξ ↦ endpointOutputMask f p output y • selectedAlgebraicSymbol f p (2*threshold) Q B o y ξ
        ContDiff ℝ ∞ (Function.uncurry σa) ∧
        (∀ j ξ y, ‖iteratedFDeriv ℝ j (fun z ↦ σa z ξ) y‖ ≤ Bσ j * L^j) ∧
        (∃ R N, GraphNormalAmplitudeBounds
          (maskedPhysicalPDOCycleSymbol (chartInputMask f p) (chartInputMask f p) σa) R N) ∧
        maskedPhysicalPDO (chartInputMask f p) (chartInputMask f p) σa =
          maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
            (selectedAlgebraicSymbol f p (2*threshold) Q B o) := by
  obtain ⟨C, hC, hslice⟩ := exists_cycle_source_slice_constants (d := d) (q := d+1)
  obtain ⟨hout, hcout, _⟩ := endpointOutputMask_properties f p ho hoc hos
  choose A hA hmask using fun j ↦ hcout.exists_bound_iteratedFDeriv hout j
  let Ebound := fun j ↦ D j * (1 + AQ (j+1) + AB (j+1))
  have hEbound j : 0 ≤ Ebound j := mul_nonneg (hD j) (by linarith [hAQ (j+1), hAB (j+1)])
  let G := fun j ↦ C j * Ebound j
  have hG j : 0 ≤ G j := mul_nonneg (hC j) (hEbound j)
  let Bσ := derivativeConvolution A G
  have hBσ j : 0 ≤ Bσ j := derivativeConvolution_nonneg hA hG j
  refine ⟨Bσ, hBσ, ?_⟩
  intro Rcoef hR L hL Q B hQp hBp o R N hnormal hcoordinate σa
  let σ := selectedAlgebraicSymbol f p (2*threshold) Q B o
  have hscale j : 1 + cNorm (closedBall x RQ) (j+1) Q + cNorm (closedBall x RQ) (j+1) B ≤
      (1 + AQ (j+1) + AB (j+1)) * L^j := by
    have hp : L^(j+1-Rcoef) ≤ L^j := pow_le_pow_right₀ hL (by omega)
    have hq := (hQp (j+1)).trans (mul_le_mul_of_nonneg_left hp (hAQ _))
    have hb := (hBp (j+1)).trans (mul_le_mul_of_nonneg_left hp (hAB _))
    have h1 : (1 : ℝ) ≤ L^j := one_le_pow₀ hL
    nlinarith
  have hcoords j ξ is (his : is.length ≤ j) z :
      ‖matrixAmplitudeCoordinateDerivList is
        (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p) σ ξ) z‖ ≤ Ebound j * L^j := by
    apply (le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg ξ] : 1 ≤ 1+‖ξ‖)).trans
    apply (hcoordinate j ξ is his z).trans
    exact (mul_le_mul_of_nonneg_left (hscale j) (hD j)).trans_eq (by dsimp [Ebound]; ring)
  obtain ⟨hσb, hj⟩ := hslice (chartOutputMask f p) (chartInputMask f p)
    ((physicalCoordinates (f.chart p).index).symm x) (chartInputMask_eq_one_at_center f p)
    σ R N hnormal (fun j ↦ Ebound j * L^j)
    (fun j ↦ mul_nonneg (hEbound j) (pow_nonneg (zero_le_one.trans hL) j)) hcoords
  let σb := fun y ξ ↦ chartOutputMask f p y • σ y ξ
  have he : σa = fun y ξ ↦ endpointOutputMask f p output y • σb y ξ := by
    funext y ξ
    change endpointOutputMask f p output y • σ y ξ =
      endpointOutputMask f p output y • (chartOutputMask f p y • σ y ξ)
    rw [smul_smul, endpointOutputMask_mul_chartOutputMask f p hos]
  have hσa : ContDiff ℝ ∞ (Function.uncurry σa) := by
    rw [he]
    exact (hout.comp contDiff_fst).smul hσb
  have hjet j ξ y : ‖iteratedFDeriv ℝ j (fun z ↦ σa z ξ) y‖ ≤ Bσ j * L^j := by
    have hm k : ‖iteratedFDeriv ℝ k (endpointOutputMask f p output) y‖ ≤ A k * L^k :=
      (hmask k k le_rfl y).trans (le_mul_of_one_le_right (hA k) (one_le_pow₀ hL))
    have hb k : ‖iteratedFDeriv ℝ k (fun z ↦ σb z ξ) y‖ ≤ 1 * G k * L^k :=
      (hj k ξ y).trans_eq (by dsimp [G]; ring)
    rw [he]
    have hh := algebraic_norm_iteratedFDeriv_smul_grades
      (f := endpointOutputMask f p output) (g := fun z ↦ σb z ξ) hout.contDiffAt
      ((hσb.comp (contDiff_id.prodMk contDiff_const)).contDiffAt (x := y))
      hA (zero_le_one.trans hL) hm hb j
    simpa only [one_mul] using hh
  refine ⟨hσa, hjet, ?_, maskedPhysicalPDO_chartInput_output_absorption f p output hos _⟩
  exact exists_chartInput_normal_certificate_of_physical_jets f p σa hσa
    (fun j ↦ Bσ j * L^j) (fun j ↦ mul_nonneg (hBσ j)
      (pow_nonneg (zero_le_one.trans hL) j)) hjet

end JanetCartan.FixedDomainInverse.SelectedPdoEnvelopeApplication
