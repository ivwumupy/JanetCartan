module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.WeightedPhysicalBudget
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.SpectralSupport

/-!
# Supported PDO budgets from the original minor and coefficient data

Both literal algebraic symbols are treated together. The off-root interval,
determinant gap, support box, high constants and uniform low bound are chosen
before the varying original fields. All intermediate inverse, source-product
and physical-action bounds are instantiated in this theorem.

Consumers: `CompleteResidual.directPDOSymbols` indices zero and three,
`PdoRealization.directPDOSymbols_regularizations`, and the forward and literal
adjoint gain estimates in `PdoRealization.IntegerBounds`. Source:
`app:ch_regular_base:eq:complement-inverse`, `complement-symbol` and
`energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
open ResidualCoordinates RootFamily ActualCarriers EvolutionIntegral PdoRealization
open JanetCartan.CharacteristicTransport.CompleteResidual
open AmplitudeBound FourierIntegral
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "Coeff" => Fin (d + 1) → Mat

/-- Actual supported symbol budgets for both algebraic terms in the complete
residual. The coordinate-derivative reserve is explicitly ONE. The finite
original low order is `2 * (d + 2) + 2`; it supplies the uniform weighted
derivatives through `2 * (d + 2) + 1` required by BOTH gain-one estimates.
For Sobolev order `n`, the high input is the displayed bound at
`m = 2 * (d + 2) + (n + 1)`, hence a fixed total reserve
`2 * (d + 2) + 2` in the original coefficient norms.

The parent still chooses common masks and proves their geometric containment
for the SAME root branch. In particular `NormalizedSpectralSupport` is a
separate, exact condition on the multiplier, not a root-band inference.
No completion gap, inverse bound, full-symbol bound or operator estimate is
an input. Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_conicAlgebraicSymbols_supported_budgets
    (ℓ : Euclidean d →L[ℝ] ℝ) (i r c : Fin (d + 1))
    (x : E) {R : ℝ} (hR : 0 < R) (xQ : E) (RQ : ℝ)
    (hphysical : MapsTo (physicalCoordinates i) (closedBall x R) (closedBall xQ RQ))
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
    {a : ℝ} (ha : 0 < a) (Λ : ℝ)
    (ρ : Euclidean d → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hsρ : tsupport ρ ⊆ {η | 0 < ℓ η})
    (σ : RootState (Euclidean d) → ℝ) (hσ : ContDiff ℝ ∞ σ)
    (hsσ : ∀ w ∈ tsupport σ,
      EvolutionIntegral.KernelIdentification.timeSpacePoint w.1 w.2.1 ∈ closedBall x R)
    (β : E → ℂ) (hβ : ContDiff ℝ ∞ β) (Mβ : ℝ)
    (hmask : ∀ ξ, ‖(ρ (spatialPart ξ) : ℂ) * β ξ‖ ≤ Mβ)
    (hradial : ∀ ξ ∈ tsupport β, a ≤ ℓ (spatialPart ξ))
    (hnorm : ∀ ξ ∈ tsupport β, ‖normalizeCovector ℓ ξ‖ ≤ Λ)
    (hη : ∀ ξ ∈ tsupport β, spatialPart (normalizeCovector ℓ ξ) ∈ Kη)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hco : HasCompactSupport χout) (hcs : HasCompactSupport χsource)
    (hcarrier : tsupport χout ⊆ closedBall x R)
    (Mlow : ℝ) (hMlow : 0 ≤ Mlow) :
    ∃ ε > 0, ∃ δ > 0, ∃ Rbox > 0, ∃ C : ℕ → ℝ, ∃ L > 0,
      (∀ m, 0 < C m) ∧
      (∀ p ∈ minorCoefficientClass r c M μ ν, ∀ e : ℝ, |e| ≤ ε →
        δ ≤ |(pencilCompletion p.1 p.2 (minorRightNullvector p.1 r c)
          (minorLeftNullvector p.1 p.2 r c) e).det| ∧
        δ ≤ |(borderedPencil p.1 p.2 (minorRightNullvector p.1 r c)
          (minorLeftNullvector p.1 p.2 r c) e).det|) ∧
      ∀ (Ω : Set E), IsOpen Ω → closedBall xQ RQ ⊆ Ω →
        ∀ (Q : E → Coeff) (B : E → Mat),
          ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω → MapsTo Q (closedBall xQ RQ) KA →
          cNorm (closedBall xQ RQ) (2 * (d + 2) + 2) Q ≤ Mlow →
          cNorm (closedBall xQ RQ) (2 * (d + 2) + 2) B ≤ Mlow →
          ∀ D : Set (RootState (Euclidean d)), IsOpen D →
            ContDiffOn ℝ ∞ (fieldRoot (coordinateSplit i) Q H) D →
            (∀ w ∈ D, (coordinateSplit i).symm (w.1, w.2.1) ∈ Ω) →
            (∀ y ∈ closedBall x R, ∀ ξ ∈ tsupport β,
              rootState y (spatialPart (normalizeCovector ℓ ξ)) ∈ D) →
            NormalizedSpectralSupport ℓ (fieldRoot (coordinateSplit i) Q H) (closedBall x R) ε β →
            let b := directAlgebraicSymbol
              (conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c)
              (conicSourceSymbol ℓ ρ σ) β
            let p := physicalSymbolApply
              (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
              (fun y ↦ (zeroth i B y).map Complex.ofReal) b
            ∀ s ∈ ({b, p} : Set (E → E → CMat)),
              ContDiff ℝ ∞ (Function.uncurry s) ∧
              GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource s) Rbox L ∧
              (∀ ξ is, is.length ≤ 2 * (d + 2) + 1 → ∀ z,
                (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
                  (maskedPhysicalPDOCycleSymbol χout χsource s ξ) z‖ ≤ L) ∧
              ∀ m ξ is, is.length ≤ m → ∀ z,
                (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
                  (maskedPhysicalPDOCycleSymbol χout χsource s ξ) z‖ ≤
                  C m * (1 + cNorm (closedBall xQ RQ) (m + 1) Q +
                    cNorm (closedBall xQ RQ) (m + 1) B) := by
  obtain ⟨ε, hε, δ, hδ, Db, hDb, hgap, hdomain, hb⟩ :=
    exists_conicAlgebraicSymbol_weighted_cNorm_bounds ℓ i r c x hR xQ RQ hphysical
      hKA hKη H hH M hμ hν hprimitive ha Λ ρ σ hσ β Mβ hmask hradial hnorm hη
  obtain ⟨Dp, hDp, hp⟩ := exists_physicalSymbolApply_weighted_cNorm_transfer
    i x hR xQ RQ hphysical Mlow Db hDb
  choose T hT htransfer using fun m ↦
    exists_maskedPhysicalPDOCycleSymbol_derivative_constant (q := d + 1)
      x R χout χsource ho hs hco hcs hcarrier m
  obtain ⟨Rbox, hRbox, hbox⟩ := exists_common_maskedPhysicalPDOCycleSymbol_support
    (q := d + 1) hco hcs
  let C : ℕ → ℝ := fun m ↦ T m * (Db m + Dp m)
  have hC m : 0 < C m := mul_pos (hT m) (add_pos (hDb m) (hDp m))
  let k := 2 * (d + 2) + 1
  let L := C k * (1 + 2 * Mlow)
  have hL : 0 < L := mul_pos (hC k) (by positivity)
  refine ⟨ε, hε, δ, hδ, Rbox, hRbox, C, L, hL, hC, hgap, ?_⟩
  intro Ω hΩ hKQ Q B hQ hB hQrange hQlow hBlow D hD hroot hmap hstate hband b p
  have hdom := normalized_support_subset_complementDomain ℓ i r c H hdomain hprimitive Q
    (fun y hy ↦ hQrange (hphysical hy)) β hη hstate hband
  have hbSmooth : ContDiff ℝ ∞ (Function.uncurry b) :=
    contDiff_conicAlgebraicSymbol ℓ i hQ hD hroot hmap r c hdom
      ρ hρ hsρ σ hσ hsσ β hβ (fun ξ hξ ↦ mem_image_of_mem _ hξ)
  let U := physicalCoordinates i ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage (physicalCoordinates i).continuous
  have hKU : closedBall x R ⊆ U := fun y hy ↦ hKQ (hphysical hy)
  have hA : ContDiffOn ℝ ∞
      (fun y a ↦ (coefficient i Q y a).map Complex.ofReal) U := by
    apply contDiffOn_pi.mpr
    intro a
    exact contDiff_matrix_map_ofReal.comp_contDiffOn
      (contDiff_pencil.comp_contDiffOn
        ((hQ.comp (physicalCoordinates i).contDiff.contDiffOn (fun _ hy ↦ hy)).prodMk
          contDiffOn_const))
  have hBc : ContDiffOn ℝ ∞ (fun y ↦ (zeroth i B y).map Complex.ofReal) U :=
    contDiff_matrix_map_ofReal.comp_contDiffOn
      (hB.comp (physicalCoordinates i).contDiff.contDiffOn (fun _ hy ↦ hy))
  have hbSupport : ∀ y, y ∉ closedBall x R → ∀ η, b y η = 0 := by
    intro y hy η
    have hσzero : σ (rootState y ((ℓ (spatialPart η))⁻¹ • spatialPart η)) = 0 := by
      by_contra hn
      have hw := hsσ _ (subset_tsupport σ hn)
      have he : EvolutionIntegral.KernelIdentification.timeSpacePoint (y 0) (spatialPart y) = y :=
        EvolutionIntegral.KernelIdentification.timeSpaceMeasurableEquiv.symm_apply_apply y
      exact hy (by simpa only [rootState, he] using hw)
    simp [b, directAlgebraicSymbol, conicSourceSymbol, ResidualCoordinates.sourceSymbol, hσzero]
  have hpSmooth : ContDiff ℝ ∞ (Function.uncurry p) :=
    contDiff_physicalSymbolApply_on_carrier isClosed_closedBall hU hKU hA hBc hbSmooth hbSupport
  have hbBound := (hb Ω hΩ hKQ Q hQ hQrange hband).2
  have hpBound := hp Ω hΩ hKQ Q B b hQ hB hbSmooth hpSmooth
    ((cNorm_mono_order (by omega : 1 ≤ 2 * (d + 2) + 2)).trans hQlow)
    ((cNorm_mono_order (by omega : 0 ≤ 2 * (d + 2) + 2)).trans hBlow) hbBound
  have hsmooth (s : E → E → CMat) (hs' : s ∈ ({b, p} : Set (E → E → CMat))) :
      ContDiff ℝ ∞ (Function.uncurry s) := by
    simp only [mem_insert_iff, mem_singleton_iff] at hs'
    rcases hs' with rfl | rfl
    · exact hbSmooth
    · exact hpSmooth
  have hbudget (s : E → E → CMat) (hs' : s ∈ ({b, p} : Set (E → E → CMat)))
      (m : ℕ) (η : E) :
      (1 + ‖η‖) * cNorm (closedBall x R) m (fun y ↦ s y η) ≤
        (Db m + Dp m) * (1 + cNorm (closedBall xQ RQ) (m + 1) Q +
          cNorm (closedBall xQ RQ) (m + 1) B) := by
    have hhigh : 0 ≤ 1 + cNorm (closedBall xQ RQ) (m + 1) Q +
        cNorm (closedBall xQ RQ) (m + 1) B := by
      linarith [cNorm_nonneg (closedBall xQ RQ) (m + 1) Q,
        cNorm_nonneg (closedBall xQ RQ) (m + 1) B]
    simp only [mem_insert_iff, mem_singleton_iff] at hs'
    rcases hs' with rfl | rfl
    · apply (hbBound η m).trans
      apply mul_le_mul
      · exact le_add_of_nonneg_right (hDp m).le
      · have hq := cNorm_mono_order (s := closedBall xQ RQ) (f := Q) (Nat.le_succ m)
        linarith [cNorm_nonneg (closedBall xQ RQ) (m + 1) B]
      · linarith [cNorm_nonneg (closedBall xQ RQ) m Q]
      · exact (add_pos (hDb m) (hDp m)).le
    · exact (hpBound η m).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hDb m).le) hhigh)
  intro s hs'
  have hsSmooth := hsmooth s hs'
  have hderiv m ξ is (his : is.length ≤ m) z :
      (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
        (maskedPhysicalPDOCycleSymbol χout χsource s ξ) z‖ ≤
        C m * (1 + cNorm (closedBall xQ RQ) (m + 1) Q +
          cNorm (closedBall xQ RQ) (m + 1) B) := by
    have hnonneg : 0 ≤ (Db m + Dp m) *
        (1 + cNorm (closedBall xQ RQ) (m + 1) Q + cNorm (closedBall xQ RQ) (m + 1) B) :=
      mul_nonneg (add_pos (hDb m) (hDp m)).le (by
        linarith [cNorm_nonneg (closedBall xQ RQ) (m + 1) Q,
          cNorm_nonneg (closedBall xQ RQ) (m + 1) B])
    exact (htransfer m s hsSmooth _ hnonneg (hbudget s hs' m) ξ is his z).trans_eq (by
      dsimp [C]; ring)
  have hlow ξ is (his : is.length ≤ k) z :
      (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
        (maskedPhysicalPDOCycleSymbol χout χsource s ξ) z‖ ≤ L := by
    apply (hderiv k ξ is his z).trans
    apply mul_le_mul_of_nonneg_left _ (hC k).le
    have hq := (cNorm_mono_order (s := closedBall xQ RQ) (f := Q)
      (show k + 1 ≤ 2 * (d + 2) + 2 by dsimp [k]; omega)).trans hQlow
    have hbb := (cNorm_mono_order (s := closedBall xQ RQ) (f := B)
      (show k + 1 ≤ 2 * (d + 2) + 2 by dsimp [k]; omega)).trans hBlow
    linarith
  refine ⟨hsSmooth, ⟨contDiff_maskedPhysicalPDOCycleSymbol ho hs hsSmooth, hbox s, ?_⟩,
    hlow, hderiv⟩
  intro ξ is his z
  have hweighted := hlow ξ is (by dsimp [k]; omega) z
  exact (le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg ξ])).trans hweighted

end JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
