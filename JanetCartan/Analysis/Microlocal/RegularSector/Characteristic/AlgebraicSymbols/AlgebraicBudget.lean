module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.SourceBounds

/-!
# The actual source–inverse product has a single-high weighted budget

The common interval and determinant gap are constructed from the original
minor data. The remaining support inputs are geometric conditions on the
original multiplier. No inverse or product-symbol seminorm is assumed.
Consumer: `CompleteResidual.directPDOSymbols` index zero, and its physical
derivative at index three, in `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
open ResidualCoordinates RootFamily ActualCarriers EvolutionIntegral
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "Coeff" => Fin (d + 1) → Mat

/-- Weighted physical derivatives of the LITERAL algebraic PDO symbol, with
reserve zero and one high original coefficient norm. The fixed source,
radial mask and original multiplier remain in the symbol, including every
physical derivative of the source. The interval and constants precede `Q`.

The parent must place the multiplier in the displayed normalized spectral
band on the entire physical norm ball; root-uniqueness-band membership alone
does not imply this condition. Radial separation and bounded normalized full
covectors are also explicit primitive support conditions.
Source: `app:ch_regular_base:eq:complement-inverse`, `complement-symbol` and
`energy-complete-residual` in `paper-v2.tex`. -/
theorem exists_conicAlgebraicSymbol_weighted_cNorm_bounds
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
    (ρ : Euclidean d → ℝ) (σ : RootState (Euclidean d) → ℝ) (hσ : ContDiff ℝ ∞ σ)
    (β : E → ℂ) (Mβ : ℝ)
    (hmask : ∀ ξ, ‖(ρ (spatialPart ξ) : ℂ) * β ξ‖ ≤ Mβ)
    (hradial : ∀ ξ ∈ tsupport β, a ≤ ℓ (spatialPart ξ))
    (hnorm : ∀ ξ ∈ tsupport β, ‖normalizeCovector ℓ ξ‖ ≤ Λ)
    (hη : ∀ ξ ∈ tsupport β, spatialPart (normalizeCovector ℓ ξ) ∈ Kη) :
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
          NormalizedSpectralSupport ℓ (fieldRoot (coordinateSplit i) Q H) (closedBall x R) ε β →
          let b := directAlgebraicSymbol
            (conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c)
            (conicSourceSymbol ℓ ρ σ) β
          (∀ ξ y, y ∈ closedBall x R → ContDiffAt ℝ ∞ (fun y ↦ b y ξ) y) ∧
          ∀ ξ m, (1 + ‖ξ‖) * cNorm (closedBall x R) m (fun y ↦ b y ξ) ≤
            C m * (1 + cNorm (closedBall xQ RQ) m Q) := by
  obtain ⟨ε, hε, δ, hδ, D, hD, hgap, hdomain, hb⟩ :=
    exists_conicBminus_fieldRoot_weighted_cNorm_bounds ℓ i r c x hR xQ RQ
      hphysical hKA hKη H hH M hμ hν hprimitive ha Λ
  obtain ⟨S, hS, hsource⟩ := exists_sourceSymbol_physical_cNorm_bounds x R hKη σ hσ
  let P : ℕ → ℝ := fun m ↦ (m + 1 : ℝ) * 2 ^ m
  let T := 1 + max 0 Mβ
  have hP m : 0 < P m := by dsimp [P]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨ε, hε, δ, hδ, fun m ↦ P m * (T * S m) * D m,
    fun m ↦ mul_pos (mul_pos (hP m) (mul_pos hT (hS m))) (hD m), hgap, hdomain, ?_⟩
  intro Ω hΩ hKQ Q hQ hQrange hband b
  have hzero (ξ : E) (hξ : β ξ = 0) : (fun y ↦ b y ξ) = 0 := by
    funext y
    simp [b, directAlgebraicSymbol, hξ]
  have hsourceSmooth (η : Euclidean d) : ContDiff ℝ ∞ (fun y : E ↦ sourceSymbol σ y η) :=
    Complex.ofRealCLM.contDiff.comp (hσ.comp
      ((coordinateSplit 0).contDiff.fst.prodMk
        ((coordinateSplit 0).contDiff.snd.prodMk contDiff_const)))
  have hsplit (ξ : E) : (fun y ↦ conicSourceSymbol ℓ ρ σ y (spatialPart ξ) * β ξ) =
      fun y ↦ ((ρ (spatialPart ξ) : ℂ) * β ξ) •
        sourceSymbol σ y (spatialPart (normalizeCovector ℓ ξ)) := by
    have he : spatialPart (normalizeCovector ℓ ξ) =
        (ℓ (spatialPart ξ))⁻¹ • spatialPart ξ :=
      congrArg Prod.snd ((coordinateSplit 0).map_smul (ℓ (spatialPart ξ))⁻¹ ξ)
    funext y
    simp only [conicSourceSymbol, he, smul_eq_mul]
    ring
  have hsmooth (ξ : E) (hξ : β ξ ≠ 0) :=
    hb Ω hΩ hKQ Q hQ hQrange ξ (hradial ξ (subset_tsupport β hξ))
      (hnorm ξ (subset_tsupport β hξ)) (hη ξ (subset_tsupport β hξ))
      (fun y hy ↦ hband y hy ξ (subset_tsupport β hξ))
  have hscalar (ξ : E) : ContDiff ℝ ∞
      (fun y ↦ conicSourceSymbol ℓ ρ σ y (spatialPart ξ) * β ξ) := by
    rw [hsplit]
    exact (contDiff_const (c := ((ρ (spatialPart ξ) : ℂ) * β ξ))).smul (hsourceSmooth _)
  refine ⟨?_, ?_⟩
  · intro ξ y hy
    by_cases hξ : β ξ = 0
    · rw [hzero ξ hξ]
      exact contDiffAt_const
    · exact (hscalar ξ).contDiffAt.smul ((hsmooth ξ hξ).1 y hy)
  intro ξ m
  by_cases hξ : β ξ = 0
  · rw [hzero ξ hξ, cNorm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (hP m).le
      (mul_nonneg hT.le (hS m).le)) (hD m).le)
      (add_nonneg zero_le_one (cNorm_nonneg _ _ _))
  have hmem := subset_tsupport β hξ
  have hsc : cNorm (closedBall x R) m
      (fun y ↦ conicSourceSymbol ℓ ρ σ y (spatialPart ξ) * β ξ) ≤ T * S m := by
    rw [hsplit, cNorm_const_complex_smul m _ (fun _ _ ↦ (hsourceSmooth _).contDiffAt.of_le (by simp))]
    exact mul_le_mul ((hmask ξ).trans (by dsimp [T]; linarith [le_max_right 0 Mβ]))
      (hsource _ (hη ξ hmem) m) (cNorm_nonneg _ _ _) hT.le
  have hprod := cNorm_complex_smul_le_of_contDiffAt (isCompact_closedBall x R) m
    (fun y _ ↦ (hscalar ξ).contDiffAt.of_le (by simp))
    (fun y hy ↦ ((hsmooth ξ hξ).1 y hy).of_le (show (m : ℕ∞ω) ≤ ∞ by simp))
  change cNorm (closedBall x R) m (fun y ↦ b y ξ) ≤
    P m * cNorm (closedBall x R) m
      (fun y ↦ conicSourceSymbol ℓ ρ σ y (spatialPart ξ) * β ξ) *
      cNorm (closedBall x R) m
        (fun y ↦ conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c y ξ) at hprod
  calc
    _ ≤ (1 + ‖ξ‖) * (P m * (T * S m) * cNorm (closedBall x R) m
        (fun y ↦ conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c y ξ)) :=
      mul_le_mul_of_nonneg_left (hprod.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsc (hP m).le)
          (cNorm_nonneg _ _ _))) (by positivity)
    _ = (P m * (T * S m)) * ((1 + ‖ξ‖) * cNorm (closedBall x R) m
        (fun y ↦ conicBminus ℓ i Q (fieldRoot (coordinateSplit i) Q H) r c y ξ)) := by ring
    _ ≤ (P m * (T * S m)) * (D m * (1 + cNorm (closedBall xQ RQ) m Q)) :=
      mul_le_mul_of_nonneg_left ((hsmooth ξ hξ).2 m)
        (mul_nonneg (hP m).le (mul_nonneg hT.le (hS m).le))
    _ = _ := by ring

end JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
