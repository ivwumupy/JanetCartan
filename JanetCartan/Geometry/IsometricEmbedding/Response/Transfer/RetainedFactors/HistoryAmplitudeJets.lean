module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.AmplitudeJets

/-!
# Retained annular amplitude grades on the actual histories

Instantiate the original coefficient profiles, then the retained amplitude-jet
calculation. A history reserve of `Rstar + 10` pays the geometric shift two
and the amplitude shift ten, leaving exactly `L^(j+2-Rstar)`. No factor of
frequency or envelope scale is spent. This supplies the primitive `hαjet`
input of the direct envelope endpoint on a closed carrier.

The only amplitude estimate supplied below is the original unmodified
`twoTimeOrderSeminorm` output of `UniformAmplitudes.ConicConstruction`, for
these same `Q,B`. Common retained critical geometry, phase grades, and the
choice of its closed carriers remain to be instantiated. This is not the
literal transfer theorem. Source: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.RetainedFactors
open GeometricProfile ProtectedFlow CurrentCoefficientProfiles
open RegularSector.Characteristic RegularSector.Characteristic.UniformEvolution
open RegularSector.FiniteMasks
open RegularSector.Characteristic.EvolutionIntegral
open JanetCartan.RegularSector.Characteristic.ConicPhase
open JanetCartan.ResponseTransfer.DirectEvolution JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open SymbolBudgets

variable {d p : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean p
local notation "Joint" => (E × Par) × CarrierVariables (d + 1)

private theorem shifted_coefficient_pair_le
    {KQ : Set E} {Q : E → Fin (d + 1) → MetricTensor (d + 1)}
    {B : E → MetricTensor (d + 1)} {Rstar j : ℕ} {L : ℝ}
    {AQ AB : ℕ → ℝ} (hL : 1 ≤ L)
    (hAB : ∀ m, 0 ≤ AB m)
    (hQ : HasDerivativeProfile KQ Q (Rstar + 8) L AQ)
    (hB : HasDerivativeProfile KQ B (Rstar + 8) L AB) :
    1 + cNorm KQ (j + 10) Q + cNorm KQ (j + 9) B ≤
      (1 + AQ (j + 10) + AB (j + 9)) * L ^ (j + 2 - Rstar) := by
  have hq : cNorm KQ (j + 10) Q ≤ AQ (j + 10) * L ^ (j + 2 - Rstar) := by
    simpa only [show j + 10 - (Rstar + 8) = j + 2 - Rstar by omega] using hQ (j + 10)
  have hb := (hB (j + 9)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (show j + 9 - (Rstar + 8) ≤ j + 2 - Rstar by omega)) (hAB _))
  have h1 := one_le_pow₀ hL (n := j + 2 - Rstar)
  nlinarith

/-- For the SAME admissible history and prescribed extension, the actual
retained solver and full residual amplitudes have the direct theorem's
primitive joint grade. The constants precede the history, amplitude witnesses,
elapsed time, frequency and derivative order. All closed-carrier masks are
retained; orders zero and minus one use their original normalization.

`hbudget` is exactly the three-branch estimate already proved by
`UniformAmplitudes.exists_uniform_supported_conic_pencilAmplitudes_with_retarded_radii`.
It is not an envelope bound. The history profiles and their full reserve are
constructed here; no coefficient-grade premise is left. The remaining domain
premises place that producer's SAME amplitudes on the common critical carrier
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_admissible_history_retained_annular_jets
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar Rstar kMin : ℕ}
    (hreserve : Rstar + 10 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin)
    {KQ : Set E} (hKQ : IsCompact KQ) {K : Set Joint} (hK : IsCompact K)
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε ra rb : ℝ} (hε : 0 < ε)
    (hchart : ∀ v ∈ K, annularCarrierCoordinates v ∈ retainedGraphDomain ℓ z ε)
    (hband : ∀ v ∈ K, ℓ (spatialPart v.2.snd) ∈ Icc ra rb)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (mask : E → ℝ) (hm : ContDiff ℝ ∞ mask)
    {threshold : ℝ} (hthreshold : 1 ≤ threshold)
    (π : E → ℂ) (hπ : ContDiff ℝ ∞ π)
    (D : ℕ → ℝ) (hD : ∀ j, 0 ≤ D j) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ Aamp : ℕ → ℝ, (∀ j, 0 ≤ Aamp j) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      let Q := extendedProjectedStress ext F
      let B := reducedZerothProjection (d + 1) ∘ extendedReducedCoefficients ext (fun _ _ ↦ 0) F
      ∀ W : Fin 3 → TwoTimeAmplitude d (d + 1),
        (∀ i, ContDiff ℝ ∞ (jointAmplitude (W i))) →
        (∀ i : Fin 3, ∀ j,
          BoundedTwoTimeOrderSeminorm (if i = 0 then 0 else 1)
            (bufferedJetSet ℓ z ε ra rb) j (W i) ∧
          twoTimeOrderSeminorm (if i = 0 then 0 else 1)
            (bufferedJetSet ℓ z ε ra rb) j (W i) ≤
              D j * (1 + cNorm KQ (j + 10) Q + cNorm KQ (j + 9) B)) →
        ∀ t ∈ Icc 0 ε, ∀ lam : ℝ, 1 ≤ lam → ∀ j : ℕ,
          let β : E → ℂ := fun ξ ↦ (dilatedConicMask mask threshold ξ : ℂ)
          (∀ v ∈ K, ‖iteratedFDeriv ℝ j (Function.uncurry
            (normalizedAnnularElapsedAmplitude (P := Par) (W 0 + W 1)
              χout χsource β π t lam 0)) v‖ ≤
                Aamp j * currentCoefficientScale R₀ s ^ (j + 2 - Rstar)) ∧
          (∀ v ∈ K, ‖iteratedFDeriv ℝ j (Function.uncurry
            (normalizedAnnularElapsedAmplitude (P := Par) (W 2)
              χout χsource β π t lam (-1))) v‖ ≤
                Aamp j * currentCoefficientScale R₀ s ^ (j + 2 - Rstar)) := by
  obtain ⟨S, hS, AQ, AB, hAQ, hAB, hcoeff⟩ :=
    exists_admissible_history_retained_coefficient_profiles G hr hrR hR ext
      hextcenter hextradius (reserve := Rstar + 8) (by omega) (by omega) horder
  let cost := fun j ↦ annularMaskConstant K j χout χsource mask threshold π * D j
  have hcost j : 0 ≤ cost j := mul_nonneg
    (annularMaskConstant_nonneg _ _ _ _ _ _ _) (hD j)
  have hprofileNonneg j : 0 ≤ 1 + AQ (j + 10) + AB (j + 9) :=
    add_nonneg (add_nonneg zero_le_one (hAQ _)) (hAB _)
  refine ⟨S, hS, (fun j ↦ 2 * cost j * (1 + AQ (j + 10) + AB (j + 9))),
    (fun j ↦ mul_nonneg (mul_nonneg (by norm_num) (hcost j))
      (hprofileNonneg j)), ?_⟩
  intro R₀ hR₀ s u ell hu F Q B W hW hbudget t ht lam hlam j
  have hL := one_le_currentCoefficientScale (by linarith : 1 ≤ R₀) s
  obtain ⟨_, _, hp⟩ := hcoeff R₀ hR₀ s u ell hu
  obtain ⟨hq, hb⟩ := hp KQ hKQ
  have hpair := shifted_coefficient_pair_le (j := j) hL hAB hq hb
  have hjets := retained_solver_residual_annular_jets hK ℓ z hε hchart hband W hW
    χout χsource ho hs mask hm hthreshold π hπ KQ Q B D hbudget ht hlam j
  have hbound : cost j * (1 + cNorm KQ (j + 10) Q + cNorm KQ (j + 9) B) ≤
      (cost j * (1 + AQ (j + 10) + AB (j + 9))) *
        currentCoefficientScale R₀ s ^ (j + 2 - Rstar) :=
    (mul_le_mul_of_nonneg_left hpair (hcost j)).trans_eq (by ring)
  have hnonneg : 0 ≤ (cost j * (1 + AQ (j + 10) + AB (j + 9))) *
      currentCoefficientScale R₀ s ^ (j + 2 - Rstar) :=
    mul_nonneg (mul_nonneg (hcost j) (hprofileNonneg j))
      (pow_nonneg (zero_le_one.trans hL) _)
  constructor
  · intro v hv
    exact ((hjets.1 v hv).trans (mul_le_mul_of_nonneg_left hbound (by norm_num))).trans_eq
      (by ring)
  · intro v hv
    exact (hjets.2 v hv).trans (hbound.trans (by nlinarith))

end JanetCartan.ResponseTransfer.RetainedFactors
