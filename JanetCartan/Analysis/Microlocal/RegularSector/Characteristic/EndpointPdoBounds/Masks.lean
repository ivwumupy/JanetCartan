module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.Source
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.Nested

/-!
# The finite conic masks and the normalized diagonal support obligation

The mask bounds used in the PDO budgets are consequences of `FiniteMasks`.
Only position derivatives occur in these budgets, so the multiplier's value
bound suffices. The last lemma states the exact support-to-buffer inclusion
which remains with the parent's same-family finite chart construction.
Source: `paper-v2.tex`, `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
open EvolutionIntegral EvolutionIntegral.SymbolBudgets ResidualCoordinates
open AmplitudeBound PdoRealization FourierIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => Euclidean (2 * (d + 1))
local notation "Z" => RootState (Euclidean d)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- The fixed finite conic multiplier supplies the smoothness and value
bound used by every PDO position derivative (`energy-complete-residual`). -/
theorem complex_conicMask_pdo_bounds {n : ℕ} (a : Euclidean n → ℝ)
    (ha : ContDiff ℝ ∞ a) (hb : ∀ ξ, a ξ ∈ Icc (0 : ℝ) 1) :
    ContDiff ℝ ∞ (fun ξ ↦ (FiniteMasks.conicMask a ξ : ℂ)) ∧
      ∀ ξ, ‖(FiniteMasks.conicMask a ξ : ℂ)‖ ≤ 1 := by
  refine ⟨Complex.ofRealCLM.contDiff.comp (FiniteMasks.contDiff_conicMask ha), ?_⟩
  intro ξ
  have h := FiniteMasks.conicMask_mem_Icc hb ξ
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

/-- Enlarging the fixed low-frequency collar preserves the PDO mask budget.
The literal multiplier is retained (`energy-complete-residual`). -/
theorem complex_dilatedConicMask_pdo_bounds (b : E → ℝ)
    (hb : ContDiff ℝ ∞ b) (hbr : ∀ ξ, b ξ ∈ Icc (0 : ℝ) 1) (L : ℝ) :
    ContDiff ℝ ∞ (fun ξ ↦ (FiniteMasks.dilatedConicMask b L ξ : ℂ)) ∧
      ∀ ξ, ‖(FiniteMasks.dilatedConicMask b L ξ : ℂ)‖ ≤ 1 :=
  ⟨Complex.ofRealCLM.contDiff.comp (FiniteMasks.contDiff_dilatedConicMask hb L),
    fun ξ ↦ (complex_conicMask_pdo_bounds b hb hbr).2 (L⁻¹ • ξ)⟩

/-- Instantiate the source PDO with the SAME finite angular collar and
original right multiplier. No source PDO derivative bounds are inputs.
Consumer: `directPDOSymbols_regularizations`, index one, in
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_finiteMask_source_pdo_budgets
    {K : Set E} (hK : IsCompact K)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hso : tsupport χout ⊆ K) (hcs : HasCompactSupport χsource)
    (σ : Z → ℝ) (hσ : ContDiff ℝ ∞ σ) (hcσ : HasCompactSupport σ)
    (ℓ : Euclidean d →L[ℝ] ℝ) (angular : Euclidean d → ℝ)
    (ha : ContDiff ℝ ∞ angular) (har : ∀ η, angular η ∈ Icc (0 : ℝ) 1)
    (hapos : ∀ η ∈ tsupport angular, 0 < ℓ η)
    (b : E → ℝ) (hb : ContDiff ℝ ∞ b) (hbr : ∀ ξ, b ξ ∈ Icc (0 : ℝ) 1) (L : ℝ)
    (R : ℝ) (hoR : ∀ x ∈ tsupport χout, ‖x‖ ≤ R)
    (hsR : ∀ x ∈ tsupport χsource, ‖x‖ ≤ R) :
    let β := fun ξ ↦ (FiniteMasks.dilatedConicMask b L ξ : ℂ)
    let c := fun x ζ ↦ (conicSourceSymbol ℓ (FiniteMasks.conicMask angular) σ x (spatialPart ζ) * β ζ) • (1 : Mat)
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource c) R (C (2 * (d + 2))) ∧
      ∀ m ξ is, is.length ≤ m → ∀ z : P,
        ‖matrixAmplitudeCoordinateDerivList is (maskedPhysicalPDOCycleSymbol χout χsource c ξ) z‖ ≤ C m := by
  have hρ := complex_conicMask_pdo_bounds angular ha har
  have hβ := complex_dilatedConicMask_pdo_bounds b hb hbr L
  have hsρ : tsupport (FiniteMasks.conicMask angular) ⊆ {η | 0 < ℓ η} :=
    FiniteMasks.conicMask_tsupport_subset_cone angular hapos (fun η hη t ht ↦ by
      change 0 < ℓ (t • η)
      simpa only [map_smul, smul_eq_mul] using mul_pos ht hη)
  exact exists_source_pdo_budgets hK χout χsource ho hs hso hcs σ hσ hcσ
    ℓ (FiniteMasks.conicMask angular) (fun ξ ↦ (FiniteMasks.dilatedConicMask b L ξ : ℂ))
    (FiniteMasks.contDiff_conicMask ha) hsρ hβ.1 zero_le_one zero_le_one hρ.2 hβ.2 R hoR hsR

/-- Explicit parent-instantiation criterion for the SAME normalized amplitude
buffer. The shell is `max 1 |η|`; both time slots lie in the original time
buffer. These are geometric inclusions, not PDO derivative assumptions.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem diagonal_shell_cover_of_radial_support
    (β : E → ℂ) (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) (ε a b : ℝ)
    {K : Set E}
    (hposition : ∀ x ∈ K, x 0 ∈ closedBall z.1 (2 * ε) ∧
      spatialPart x ∈ closedBall z.2.1 (2 * ε))
    (hfrequency : ∀ ζ ∈ tsupport β,
      (max 1 ‖spatialPart ζ‖)⁻¹ • spatialPart ζ ∈ ConicPhase.radialSectionBand ℓ z.2.2 ε a b) :
    ∀ ζ ∈ tsupport β, ∃ R : ℝ, 1 ≤ R ∧ ∃ η : Euclidean d,
      spatialPart ζ = R • η ∧ ‖spatialPart ζ‖ ≤ R ∧
      MapsTo (diagonalPoint η) K (ConicPhase.bufferedJetSet ℓ z ε a b) := by
  intro ζ hζ
  let R := max 1 ‖spatialPart ζ‖
  have hR : 1 ≤ R := le_max_left _ _
  refine ⟨R, hR, R⁻¹ • spatialPart ζ, ?_, le_max_right _ _, ?_⟩
  · rw [smul_inv_smul₀ (ne_of_gt (zero_lt_one.trans_le hR))]
  · intro x hx
    exact (diagonalPoint_mem_bufferedJetSet_iff ℓ z ε a b _ x).mpr
      ⟨(hposition x hx).1, (hposition x hx).2, hfrequency ζ hζ⟩

end JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
