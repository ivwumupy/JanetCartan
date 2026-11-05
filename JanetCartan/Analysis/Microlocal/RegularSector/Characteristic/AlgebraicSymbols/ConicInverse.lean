module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.PrimitiveInverse

/-!
# Weighted physical jets of the literal conic inverse

The normalization and inverse are exactly `ResidualCoordinates.normalizeCovector`
and `ResidualCoordinates.conicBminus`. A positive radial lower bound and a
bounded normalized FULL covector convert degree minus one into the inhomogeneous
spacetime weight. These are geometric support conditions, not symbol estimates.
Consumer: the actual algebraic PDO in
`app:ch_regular_base:eq:complement-symbol` of `paper-v2.tex`.
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

/-- The precise order-minus-one conversion uses the SAME normalization.
Its two inputs will be discharged on the original multiplier's support by
its radial cutoff and compact normalized full-frequency buffer.
Source: `app:ch_regular_base:eq:complement-symbol`. -/
theorem conic_inverse_weight_le
    (ℓ : Euclidean d →L[ℝ] ℝ) {a Λ : ℝ} (ha : 0 < a) {ξ : E}
    (hr : a ≤ ℓ (spatialPart ξ)) (hn : ‖normalizeCovector ℓ ξ‖ ≤ Λ) :
    (1 + ‖ξ‖) * ‖(ℓ (spatialPart ξ))⁻¹‖ ≤ a⁻¹ + Λ := by
  have hp : 0 < ℓ (spatialPart ξ) := ha.trans_le hr
  have hi : (ℓ (spatialPart ξ))⁻¹ ≤ a⁻¹ := inv_anti₀ ha hr
  have hn' : ‖(ℓ (spatialPart ξ))⁻¹‖ * ‖ξ‖ ≤ Λ := by
    simpa only [normalizeCovector, norm_smul] using hn
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)] at hn' ⊢
  nlinarith

/-- Construct the common interval and weighted physical `cNorm` bounds for
`conicBminus` from original bounded normalized pencils and their minor/transport
gaps. Constants precede the varying coefficient field. The derivative reserve
is ZERO and the high coefficient norm is linear. No inverse or completion
budget is an input.

The parent's multiplier must satisfy `NormalizedSpectralSupport` with this
`ε`, together with the displayed radial and compact normalized-frequency
conditions. These are independent of root-band membership.
Source: `app:ch_regular_base:eq:complement-inverse` and `complement-symbol`. -/
theorem exists_conicBminus_fieldRoot_weighted_cNorm_bounds
    (ℓ : Euclidean d →L[ℝ] ℝ) (i r c : Fin (d + 1))
    (x : E) {ρ : ℝ} (hρ : 0 < ρ) (xQ : E) (RQ : ℝ)
    (hphysical : MapsTo (physicalCoordinates i) (closedBall x ρ) (closedBall xQ RQ))
    {KA : Set Coeff} (hKA : IsCompact KA) {Kη : Set (Euclidean d)} (hKη : IsCompact Kη)
    (H : Coeff × Euclidean d → ℝ)
    (hH : ∀ p ∈ KA ×ˢ Kη, ContDiffAt ℝ ∞ H p)
    (M : ℝ) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (hprimitive : ∀ p ∈ KA ×ˢ Kη,
      ‖coefficientRootPencil (coordinateSplit i) H p‖ ≤ M ∧
      ‖pencil p.1 ((coordinateSplit i).symm (1, 0))‖ ≤ M ∧
      (coefficientRootPencil (coordinateSplit i) H p).det = 0 ∧
      μ ≤ |(coefficientRootPencil (coordinateSplit i) H p).adjugate r c| ∧
      ν ≤ |minorTransportCoefficient (coefficientRootPencil (coordinateSplit i) H p)
        (pencil p.1 ((coordinateSplit i).symm (1, 0))) r c|)
    {a : ℝ} (ha : 0 < a) (Λ : ℝ) :
    ∃ ε > 0, ∃ δ > 0, ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      (∀ p ∈ minorCoefficientClass r c M μ ν, ∀ e : ℝ, |e| ≤ ε →
        δ ≤ |(pencilCompletion p.1 p.2 (minorRightNullvector p.1 r c)
          (minorLeftNullvector p.1 p.2 r c) e).det| ∧
        δ ≤ |(borderedPencil p.1 p.2 (minorRightNullvector p.1 r c)
          (minorLeftNullvector p.1 p.2 r c) e).det|) ∧
      (minorCoefficientClass r c M μ ν ×ˢ closedBall (0 : ℝ) ε ⊆
        minorComplementDomain r c) ∧
      ∀ (Ω : Set E), IsOpen Ω → closedBall xQ RQ ⊆ Ω →
        ∀ Q : E → Coeff, ContDiffOn ℝ ∞ Q Ω → MapsTo Q (closedBall xQ RQ) KA →
          ∀ ξ : E, a ≤ ℓ (spatialPart ξ) → ‖normalizeCovector ℓ ξ‖ ≤ Λ →
            spatialPart (normalizeCovector ℓ ξ) ∈ Kη →
            (∀ y ∈ closedBall x ρ,
              |normalizeCovector ℓ ξ 0 - fieldRoot (coordinateSplit i) Q H
                (rootState y (spatialPart (normalizeCovector ℓ ξ)))| ≤ ε) →
            (∀ y ∈ closedBall x ρ, ContDiffAt ℝ ∞
              (fun y ↦ conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c y ξ) y) ∧
            ∀ m, (1 + ‖ξ‖) * cNorm (closedBall x ρ) m
              (fun y ↦ conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c y ξ) ≤
                C m * (1 + cNorm (closedBall xQ RQ) m Q) := by
  obtain ⟨ε, hε, δ, hδ, C, hC, hgap, hdomain, hb⟩ :=
    exists_bminus_fieldRoot_cNorm_bounds i r c x hρ xQ RQ hphysical
      hKA hKη H hH M hμ hν hprimitive
  let W := 1 + a⁻¹ + max 0 Λ
  have hW : 0 < W := by
    dsimp [W]
    positivity
  refine ⟨ε, hε, δ, hδ, fun m ↦ W * C m,
    fun m ↦ mul_pos hW (hC m), hgap, hdomain, ?_⟩
  intro Ω hΩ hKQ Q hQ hQrange ξ hr hnorm hη hband
  obtain ⟨hsmooth, hbound⟩ := hb Ω hΩ hKQ Q hQ hQrange
    (normalizeCovector ℓ ξ) hη hband
  refine ⟨?_, ?_⟩
  · intro y hy
    exact (contDiffAt_const (c := (ℓ (spatialPart ξ))⁻¹)).smul (hsmooth y hy)
  intro m
  have he := cNorm_smul_of_contDiffAt (ℓ (spatialPart ξ))⁻¹
    (fun y hy ↦ (hsmooth y hy).of_le (show (m : ℕ∞ω) ≤ ∞ by simp))
  change cNorm (closedBall x ρ) m
    (fun y ↦ conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c y ξ) =
      ‖(ℓ (spatialPart ξ))⁻¹‖ * cNorm (closedBall x ρ) m
        (fun y ↦ bminus i Q (fieldRoot (coordinateSplit i) Q H) r c y (normalizeCovector ℓ ξ)) at he
  rw [he, ← mul_assoc]
  have hw : (1 + ‖ξ‖) * ‖(ℓ (spatialPart ξ))⁻¹‖ ≤ W :=
    (conic_inverse_weight_le ℓ ha hr hnorm).trans (by dsimp [W]; linarith [le_max_right 0 Λ])
  calc
    _ ≤ W * cNorm (closedBall x ρ) m
        (fun y ↦ bminus i Q (fieldRoot (coordinateSplit i) Q H) r c y (normalizeCovector ℓ ξ)) :=
      mul_le_mul_of_nonneg_right hw (cNorm_nonneg _ _ _)
    _ ≤ W * (C m * (1 + cNorm (closedBall xQ RQ) m Q)) :=
      mul_le_mul_of_nonneg_left (hbound m) hW.le
    _ = _ := by ring

end JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
