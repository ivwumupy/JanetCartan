module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.ConicInverse

/-!
# The original multiplier lies in the constructed complement domain

The common interval/domain inclusion below is an OUTPUT of
`exists_conicBminus_fieldRoot_weighted_cNorm_bounds`. The remaining hypotheses
are original root/minor/transport data and explicit geometric support
containment for the SAME root branch. This connects the interval producer to
`ResidualCoordinates.contDiff_conicAlgebraicSymbol`; it does not infer the
spectral displacement bound from a root-uniqueness band.

Source: `app:ch_regular_base:eq:complement-inverse` and
`app:ch_regular_base:eq:complement-symbol` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
open ResidualCoordinates RootFamily ActualCarriers EvolutionIntegral
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "Coeff" => Fin (d + 1) → Mat

/-- Use the interval constructed from original primitive data to prove the
EXACT support containment required by the supported inverse-product producer.
The input `hinterval` is the published output of
`exists_conicBminus_fieldRoot_weighted_cNorm_bounds`, not a new completion-gap
hypothesis. Every remaining support condition refers to the actual normalized
covector and the SAME `fieldRoot`.
Consumer: `contDiff_conicAlgebraicSymbol` in `complement-symbol`. -/
theorem normalized_support_subset_complementDomain
    (ℓ : Euclidean d →L[ℝ] ℝ) (i r c : Fin (d + 1))
    {KA : Set Coeff} {Kη : Set (Euclidean d)} (H : Coeff × Euclidean d → ℝ)
    {M μ ν ε : ℝ}
    (hinterval : minorCoefficientClass r c M μ ν ×ˢ closedBall (0 : ℝ) ε ⊆
      minorComplementDomain r c)
    (hprimitive : ∀ p ∈ KA ×ˢ Kη,
      ‖coefficientRootPencil (coordinateSplit i) H p‖ ≤ M ∧
      ‖pencil p.1 ((coordinateSplit i).symm (1, 0))‖ ≤ M ∧
      (coefficientRootPencil (coordinateSplit i) H p).det = 0 ∧
      μ ≤ |(coefficientRootPencil (coordinateSplit i) H p).adjugate r c| ∧
      ν ≤ |minorTransportCoefficient (coefficientRootPencil (coordinateSplit i) H p)
        (pencil p.1 ((coordinateSplit i).symm (1, 0))) r c|)
    (Q : E → Coeff) {X : Set E} {D : Set (RootState (Euclidean d))}
    (hQrange : ∀ x ∈ X, Q (physicalCoordinates i x) ∈ KA)
    (β : E → ℂ)
    (hη : ∀ ξ ∈ tsupport β, spatialPart (normalizeCovector ℓ ξ) ∈ Kη)
    (hstate : ∀ x ∈ X, ∀ ξ ∈ tsupport β,
      rootState x (spatialPart (normalizeCovector ℓ ξ)) ∈ D)
    (hband : NormalizedSpectralSupport ℓ (fieldRoot (coordinateSplit i) Q H) X ε β) :
    X ×ˢ (normalizeCovector ℓ '' tsupport β) ⊆
      complementDomain i Q (fieldRoot (coordinateSplit i) Q H) r c D := by
  rintro ⟨x, ξ⟩ ⟨hx, η, hηβ, rfl⟩
  refine ⟨hstate x hx η hηβ, ?_⟩
  apply hinterval
  constructor
  · change (rootPencil (coordinateSplit i) Q (fieldRoot (coordinateSplit i) Q H)
        (rootState x (spatialPart (normalizeCovector ℓ η))),
      rootTimeCoefficient (coordinateSplit i) Q
        (rootState x (spatialPart (normalizeCovector ℓ η)))) ∈ minorCoefficientClass r c M μ ν
    exact hprimitive (Q (physicalCoordinates i x), spatialPart (normalizeCovector ℓ η))
      ⟨hQrange x hx, hη η hηβ⟩
  · simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs, complementData] using hband x hx η hηβ

end JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
