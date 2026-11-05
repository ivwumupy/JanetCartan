module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.InverseBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.SourceBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.Masks

/-!
# Source multiplication on the retained finite-family inverse interval

Consumer: `exists_selected_algebraicSymbols_supported_budgets`, for indices zero
and three of `directPDOSymbols` in `app:ch_regular_base:eq:energy-complete-residual`.
The inverse inputs are exactly the local outputs of
`exists_finite_physical_evolution_and_algebraic_inverse`. No interval is selected
here; the compact normalized buffer is read from `normalizedRootDomain`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAlgebraic
open ActualCarriers Characteristic Characteristic.AlgebraicChart
open Characteristic.RootFamily Characteristic.ResidualCoordinates
open Characteristic.AlgebraicSymbols Characteristic.EvolutionIntegral
open FiniteMasks FiniteMasks.ActualFamily
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "Coeff" => Fin (d + 1) → Mat
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- Multiply the SAME retained conic inverse by the original source and physical
multiplier. Constants precede the radial enlargement and coefficient field;
there is no derivative loss. The two local inverse premises are projections of
`exists_finite_physical_evolution_and_algebraic_inverse`, and the domain premise
is its exact normalized complement containment. Source:
`app:ch_regular_base:eq:complement-symbol` and `energy-complete-residual`. -/
theorem exists_selected_sourceInverse_weighted_cNorm_bounds
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (ρ : Euclidean d → ℝ) (hρrange : ∀ η, ρ η ∈ Icc (0 : ℝ) 1)
    (D : ℕ → ℝ) (hD : ∀ m, 0 < D m) :
    let c := f.chart p
    let x' := (physicalCoordinates c.index).symm x
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (L : ℝ) (Q : E → Coeff),
        let h := fieldRoot (coordinateSplit c.index) Q c.root
        let β := fun ζ ↦ (dilatedConicMask (f.angularMask p) L (physicalCoordinates c.index ζ) : ℂ)
        ((physicalCoordinates c.index ⁻¹' Ω) ×ˢ
          (normalizeCovector c.radialSection '' tsupport β) ⊆
          complementDomain c.index Q h c.row c.col (normalizedRootDomain c)) →
        (∀ ζ ∈ tsupport β,
          (∀ y ∈ closedBall x' RQ, ContDiffAt ℝ ∞
            (fun y ↦ conicBminus c.radialSection c.index Q h c.row c.col y ζ) y) ∧
          ∀ m, (1 + ‖ζ‖) * cNorm (closedBall x' RQ) m
            (fun y ↦ conicBminus c.radialSection c.index Q h c.row c.col y ζ) ≤
              D m * (1 + cNorm (closedBall x RQ) m Q)) →
        let b := directAlgebraicSymbol
          (conicBminus c.radialSection c.index Q h c.row c.col)
          (conicSourceSymbol c.radialSection ρ c.sourceMask) β
        (∀ ζ y, y ∈ closedBall x' RQ → ContDiffAt ℝ ∞ (fun y ↦ b y ζ) y) ∧
        ∀ ζ m, (1 + ‖ζ‖) * cNorm (closedBall x' RQ) m (fun y ↦ b y ζ) ≤
          C m * (1 + cNorm (closedBall x RQ) m Q) := by
  intro c x'
  let ℓ := c.radialSection
  let i := c.index
  let r := c.row
  let c' := c.col
  let σ := c.sourceMask
  have hσ := c.sourceMask_smooth
  let Kη := closedBall (coordinateSplit c.index p.val.val).2
    (min c.coefficientRadius c.rootRadius)
  obtain ⟨S, hS, hsource⟩ := exists_sourceSymbol_physical_cNorm_bounds x' RQ (Kη := Kη)
    (isCompact_closedBall _ _) σ hσ
  let P : ℕ → ℝ := fun m ↦ (m + 1 : ℝ) * 2 ^ m
  let T := (2 : ℝ)
  have hP m : 0 < P m := by dsimp [P]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨fun m ↦ P m * (T * S m) * D m,
    fun m ↦ mul_pos (mul_pos (hP m) (mul_pos hT (hS m))) (hD m), ?_⟩
  intro L Q h β hdom hinverse b
  have hη (ζ : E) (hζ : ζ ∈ tsupport β) :
      spatialPart (normalizeCovector ℓ ζ) ∈ Kη := by
    have hx : physicalCoordinates i x' ∈ Ω := by
      simpa only [i, x', ContinuousLinearEquiv.apply_symm_apply] using hKΩ (mem_closedBall_self hRQ.le)
    have hd := hdom (a := (x', normalizeCovector c.radialSection ζ)) ⟨hx, ζ, hζ, rfl⟩
    exact ball_subset_closedBall hd.1.2
  have hmask (ζ : E) : ‖(ρ (spatialPart ζ) : ℂ) * β ζ‖ ≤ 1 := by
    rw [norm_mul]
    have hρnorm : ‖(ρ (spatialPart ζ) : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hρrange _).1] using (hρrange (spatialPart ζ)).2
    simpa only [one_mul] using mul_le_mul hρnorm
      ((EndpointPdoBounds.complex_dilatedConicMask_pdo_bounds
        (f.angularMask p) (f.angularMask_smooth p) (f.angularMask_range p) L).2
          (physicalCoordinates c.index ζ)) (norm_nonneg _) zero_le_one
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
  have hsmooth (ξ : E) (hξ : β ξ ≠ 0) := hinverse ξ (subset_tsupport β hξ)
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
  have hsc : cNorm (closedBall x' RQ) m
      (fun y ↦ conicSourceSymbol ℓ ρ σ y (spatialPart ξ) * β ξ) ≤ T * S m := by
    rw [hsplit, cNorm_const_complex_smul m _ (fun _ _ ↦ (hsourceSmooth _).contDiffAt.of_le (by simp))]
    exact mul_le_mul ((hmask ξ).trans (by norm_num [T]))
      (hsource _ (hη ξ hmem) m) (cNorm_nonneg _ _ _) hT.le
  have hprod := cNorm_complex_smul_le_of_contDiffAt (isCompact_closedBall x' RQ) m
    (fun y _ ↦ (hscalar ξ).contDiffAt.of_le (by simp))
    (fun y hy ↦ ((hsmooth ξ hξ).1 y hy).of_le (show (m : ℕ∞ω) ≤ ∞ by simp))
  change cNorm (closedBall x' RQ) m (fun y ↦ b y ξ) ≤
    P m * cNorm (closedBall x' RQ) m
      (fun y ↦ conicSourceSymbol ℓ ρ σ y (spatialPart ξ) * β ξ) *
      cNorm (closedBall x' RQ) m
        (fun y ↦ conicBminus ℓ i Q h r c' y ξ) at hprod
  calc
    _ ≤ (1 + ‖ξ‖) * (P m * (T * S m) * cNorm (closedBall x' RQ) m
        (fun y ↦ conicBminus ℓ i Q h r c' y ξ)) :=
      mul_le_mul_of_nonneg_left (hprod.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsc (hP m).le)
          (cNorm_nonneg _ _ _))) (by positivity)
    _ = (P m * (T * S m)) * ((1 + ‖ξ‖) * cNorm (closedBall x' RQ) m
        (fun y ↦ conicBminus ℓ i Q h r c' y ξ)) := by ring
    _ ≤ (P m * (T * S m)) * (D m * (1 + cNorm (closedBall x RQ) m Q)) :=
      mul_le_mul_of_nonneg_left ((hsmooth ξ hξ).2 m)
        (mul_nonneg (hP m).le (mul_nonneg hT.le (hS m).le))
    _ = _ := by ring

end JanetCartan.RegularSector.FiniteAlgebraic
