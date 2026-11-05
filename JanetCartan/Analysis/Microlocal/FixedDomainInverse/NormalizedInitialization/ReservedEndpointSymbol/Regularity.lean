module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReservedEndpointSymbol.Symbol
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.AdjointProfiles

/-!
# Global smoothness of the same masked endpoint

The original coefficient is smooth on its original physical domain. The
fixed output mask supplies the zero germ outside that domain. Thus the
literal normalized endpoint has global smoothness without replacing `Q₀`
or `W₁`. This regularity feeds the annular endpoint producer in
`app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization

open RegularSector RegularSector.FinitePdo RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic RegularSector.Characteristic
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.EndpointPdoBounds
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open ResidualLocalization ResponseTransfer

variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => E × E × E
local notation "Mat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

/-- The same normalized masked endpoint is globally smooth using only
local smoothness of its original coefficient and joint smoothness of the
supplied two-time amplitude (`energy-complete-residual`). -/
theorem contDiff_normalized_selected_endpoint_amplitude
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (threshold ρ : ℝ) (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (hQ : ContDiffOn ℝ ∞ Q Ω)
    (W : TwoTimeAmplitude d (d+1)) (hW : ContDiff ℝ ∞ (jointAmplitude W)) :
    ContDiff ℝ ∞ (normalizedFullAmplitude
      (orientedMaskedPDOAmplitude false (endpointOutputMask f p output)
        (chartInputMask f p) (selectedEndpointSymbol f p threshold Q W)) ρ) := by
  let o := endpointOutputMask f p output
  let i := chartInputMask f p
  let q := fun y ↦ (coefficient (f.chart p).index Q y 0).map Complex.ofReal
  have hos : ContDiff ℝ ∞ o := (endpointOutputMask_properties f p ho hoc hout).1
  have his : ContDiff ℝ ∞ i := (chartPhysicalMasks_properties f p).2.1
  have hβ : ContDiff ℝ ∞ (selectedEndpointMultiplier f p threshold) :=
    (selectedEndpointMultiplier_bounds f p threshold).1
  have hqs {y : E} (hy : y ∈ tsupport o) : ContDiffAt ℝ ∞ q y :=
    (contDiffOn_timeCoefficient (f.chart p).index hQ).contDiffAt
      ((hΩ.preimage (physicalCoordinates (f.chart p).index).continuous).mem_nhds
        (hball (selectedEndpoint_physical_ball_mapsTo f p
          ((endpointOutputMask_properties f p ho hoc hout).2.2 hy))))
  have hw : ContDiff ℝ ∞ (fun v : V ↦ W
      (v.1 0) (v.1 0) (spatialPart v.1) (spatialPart (ρ • v.2.2))) := by
    have hh := hW.comp
      (((diagonalLinear.contDiff.comp (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : V → E))).fst).prodMk
        (spatialProjection.contDiff.comp (contDiff_snd.snd.const_smul ρ)))
    exact hh
  apply contDiff_iff_contDiffAt.mpr
  intro v
  by_cases hv : v.1 ∈ tsupport o
  · exact ((hos.comp contDiff_fst).contDiffAt.mul
        (his.comp contDiff_snd.fst).contDiffAt).smul
      (((hβ.comp (contDiff_snd.snd.const_smul ρ)).contDiffAt).smul
        (((hqs hv).comp v contDiffAt_fst).mul hw.contDiffAt))
  · apply (contDiffAt_const (c := (0 : Mat))).congr_of_eventuallyEq
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hv).comp_tendsto
      (continuous_fst : Continuous (Prod.fst : V → E)).continuousAt
    filter_upwards [hz] with w hw
    change o w.1 = 0 at hw
    change (o w.1 * i w.2.1) • selectedEndpointSymbol f p threshold Q W w.1 (ρ • w.2.2) = 0
    rw [hw, zero_mul, zero_smul]

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
