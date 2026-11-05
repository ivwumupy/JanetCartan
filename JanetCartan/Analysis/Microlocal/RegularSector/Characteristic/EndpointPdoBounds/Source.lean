module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.MaskJets

/-!
# Uniform order-zero budgets for the actual source PDO

The compact source datum is fixed before the physical coefficients. Its
global jets bound every physical slice, independently of the normalized
covector. The original radial mask and right multiplier contribute only
their fixed value bounds to position derivatives. Consumer: index one of
`CompleteResidual.directPDOSymbols`, in `paper-v2.tex`,
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
open EvolutionIntegral EvolutionIntegral.SymbolBudgets ResidualCoordinates
open NormalComparison AmplitudeBound PdoRealization
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => Euclidean (2 * (d + 1))
local notation "Z" => RootState (Euclidean d)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

private def sourceStateLinear : E →L[ℝ] Z :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ (x 0, spatialPart x, 0)
      map_add' := by intro x y; ext <;> first | rfl | simp
      map_smul' := by intro a x; ext <;> first | rfl | simp }

private theorem sourceStateLinear_add (x : E) (η : Euclidean d) :
    sourceStateLinear x + (0, 0, η) = rootState x η := by
  change (x 0 + 0, spatialPart x + 0, (0 : Euclidean d) + η) = _
  simp only [add_zero, zero_add, rootState]

/-- All position derivatives of the literal source PDO are uniformly bounded
over EVERY full frequency. No derivative budget for the PDO is assumed.
Constants involve only fixed compact source/output data and the fixed mask
value bounds, so precede all varying physical coefficients.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_source_position_constants
    {K : Set E} (hK : IsCompact K)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hso : tsupport χout ⊆ K) (hcs : HasCompactSupport χsource)
    (σ : Z → ℝ) (hσ : ContDiff ℝ ∞ σ) (hcσ : HasCompactSupport σ)
    (ℓ : Euclidean d →L[ℝ] ℝ) (ρ : Euclidean d → ℝ) (β : E → ℂ)
    {Mρ Mβ : ℝ} (hMρ : 0 ≤ Mρ) (hMβ : 0 ≤ Mβ)
    (hbρ : ∀ η, ‖(ρ η : ℂ)‖ ≤ Mρ) (hbβ : ∀ ξ, ‖β ξ‖ ≤ Mβ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ m, ∀ ξ : E, ∀ is : List (Fin (2 * (d + 1))), is.length ≤ m → ∀ z : P,
        ‖matrixAmplitudeCoordinateDerivList is
          (maskedPhysicalPDOCycleSymbol χout χsource
            (fun x ζ ↦ (conicSourceSymbol ℓ ρ σ x (spatialPart ζ) * β ζ) • (1 : Mat)) ξ) z‖ ≤
          C m := by
  let F : Z → Mat := fun w ↦ (σ w : ℂ) • (1 : Mat)
  have hF : ContDiff ℝ ∞ F := (Complex.ofRealCLM.contDiff.comp hσ).smul contDiff_const
  have hcF : HasCompactSupport F := by
    apply HasCompactSupport.intro hcσ
    intro w hw
    have hz : σ w = 0 := image_eq_zero_of_notMem_tsupport hw
    simp only [F, hz, Complex.ofReal_zero, zero_smul]
  choose S hS hbS using fun m ↦ hcF.exists_bound_iteratedFDeriv hF m
  choose D hD hmask using fun m ↦ exists_masked_position_derivative_constant
    (q := q) hK χout χsource ho hs hso hcs m
  let T := fun m : ℕ ↦ (m + 1 : ℝ) * (S m * max 1 ‖sourceStateLinear (d := d)‖ ^ m)
  have hT m : 0 ≤ T m := by dsimp [T]; have := hS m; positivity
  refine ⟨fun m ↦ 1 + D m * (Mρ * Mβ * T m), ?_, ?_⟩
  · intro m
    have := hD m
    have := hT m
    positivity
  intro m ξ is hi z
  let ζ := (2 * Real.pi) • ξ
  let η := (ℓ (spatialPart ζ))⁻¹ • spatialPart ζ
  let g : E → Mat := fun x ↦ F (sourceStateLinear x + (0, 0, η))
  have hg : ContDiff ℝ ∞ g := hF.comp (sourceStateLinear.contDiff.add contDiff_const)
  have hgj k (hk : k ≤ m) x : ‖iteratedFDeriv ℝ k g x‖ ≤
      S m * max 1 ‖sourceStateLinear (d := d)‖ ^ m := by
    apply (norm_iteratedFDeriv_preAffine_le (x := x) sourceStateLinear (0, 0, η)
      isOpen_univ hF.contDiffOn (mem_univ _) k).trans
    exact mul_le_mul (hbS m k hk _)
      ((pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) k).trans
        (pow_le_pow_right₀ (le_max_left _ _) hk)) (by positivity) (hS m)
  have hgc : cNorm K m g ≤ T m := by
    have h := cNorm_le_sum_of_bounds (s := K) (f := g)
      (fun k (_ : k ≤ m) ↦ mul_nonneg (hS m)
        (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) m))
      (fun k hk x _ ↦ hgj k hk x)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using h
  let a : ℂ := (ρ (spatialPart ζ) : ℂ) * β ζ
  have ha : ‖a‖ ≤ Mρ * Mβ := by
    rw [norm_mul]
    exact mul_le_mul (hbρ _) (hbβ _) (norm_nonneg _) hMρ
  have he : (fun x ↦ (conicSourceSymbol ℓ ρ σ x (spatialPart ζ) * β ζ) • (1 : Mat)) =
      (fun x ↦ a • g x) := by
    funext x
    simp only [g, sourceStateLinear_add, F, a, conicSourceSymbol, sourceSymbol, smul_smul]
    congr 1
    ring
  have hm := hmask m univ isOpen_univ (subset_univ K) _
    ((hg.const_smul a).contDiffOn) is hi z
  rw [cNorm_complex_smul_on_open isOpen_univ (subset_univ K) hg.contDiffOn] at hm
  change ‖matrixAmplitudeCoordinateDerivList is
    (fun p ↦ (χout (splitPhysicalPositions p).1 * χsource (splitPhysicalPositions p).2) •
      ((conicSourceSymbol ℓ ρ σ (splitPhysicalPositions p).1 (spatialPart ζ) * β ζ) • (1 : Mat))) z‖ ≤ _
  simp_rw [congrFun he] 
  apply hm.trans
  have hmul : D m * (‖a‖ * cNorm K m g) ≤ D m * (Mρ * Mβ * T m) :=
    mul_le_mul_of_nonneg_left (mul_le_mul ha hgc (cNorm_nonneg _ _ _) (mul_nonneg hMρ hMβ)) (hD m).le
  linarith

/-- The actual source supplies the normal-amplitude input for PDO
regularization and all higher position inputs for integer bounds. Its
constants are independent of every physical coefficient, and hence also
obey the requested single-high original-coefficient budget.
Source: `app:ch_regular_base:eq:energy-complete-residual`, index one. -/
theorem exists_source_pdo_budgets
    {K : Set E} (hK : IsCompact K)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hso : tsupport χout ⊆ K) (hcs : HasCompactSupport χsource)
    (σ : Z → ℝ) (hσ : ContDiff ℝ ∞ σ) (hcσ : HasCompactSupport σ)
    (ℓ : Euclidean d →L[ℝ] ℝ) (ρ : Euclidean d → ℝ) (β : E → ℂ)
    (hρ : ContDiff ℝ ∞ ρ) (hsρ : tsupport ρ ⊆ {η | 0 < ℓ η})
    (hβ : ContDiff ℝ ∞ β)
    {Mρ Mβ : ℝ} (hMρ : 0 ≤ Mρ) (hMβ : 0 ≤ Mβ)
    (hbρ : ∀ η, ‖(ρ η : ℂ)‖ ≤ Mρ) (hbβ : ∀ ξ, ‖β ξ‖ ≤ Mβ)
    (R : ℝ) (hoR : ∀ x ∈ tsupport χout, ‖x‖ ≤ R)
    (hsR : ∀ x ∈ tsupport χsource, ‖x‖ ≤ R) :
    let c := fun x ζ ↦ (conicSourceSymbol ℓ ρ σ x (spatialPart ζ) * β ζ) • (1 : Mat)
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      FourierIntegral.GraphNormalAmplitudeBounds
        (maskedPhysicalPDOCycleSymbol χout χsource c) R (C (2 * (d + 2))) ∧
      ∀ m, ∀ ξ : E, ∀ is : List (Fin (2 * (d + 1))), is.length ≤ m → ∀ z : P,
        ‖matrixAmplitudeCoordinateDerivList is (maskedPhysicalPDOCycleSymbol χout χsource c ξ) z‖ ≤ C m := by
  intro c
  obtain ⟨C, hC, hb⟩ := exists_source_position_constants (q := q)
    hK χout χsource ho hs hso hcs σ hσ hcσ ℓ ρ β hMρ hMβ hbρ hbβ
  refine ⟨C, hC, ⟨?_, ?_, ?_⟩, hb⟩
  · exact contDiff_sourcePDOCycleSymbol ℓ ρ hρ hsρ σ hσ β χout χsource hβ ho hs
  · exact maskedPhysicalPDOCycleSymbol_supportedInCenteredBox χout χsource c hoR hsR
  · exact hb (2 * (d + 2))

end JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
