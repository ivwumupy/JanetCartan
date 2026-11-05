module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.PhysicalMasks
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.Masks

/-!
# The literal source PDO on the selected physical family

Instantiate index one of `directPDOSymbols` on the same selected source,
spatial and physical masks, with the exact physical radial multiplier.
This supplies its actual regularization input to the complete residual.
The constants depend only on fixed masks and precede the coefficient fields.
Source: `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Matrix
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FinitePdo
open Characteristic Characteristic.ResidualCoordinates Characteristic.PdoRealization
open Characteristic.EvolutionIntegral
open Characteristic.EndpointPdoBounds FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open AmplitudeBound FourierIntegral
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

/-- The exact selected source symbol, with the physical frequency permutation
inside the radial cutoff (`energy-complete-residual`, index one). -/
def selectedSourceSymbol (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (L : ℝ) (y ζ : E) : CMat :=
  (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
    (f.chart p).sourceMask y (spatialPart ζ) *
      (dilatedConicMask (f.angularMask p) L (physicalCoordinates (f.chart p).index ζ) : ℂ)) • 1

/-- Discharge every source-PDO budget input from the actual finite family's
fixed masks. The canonical masked physical symbol has all position budgets
and the exact normal-amplitude bound used by `directPDOSymbols_regularizations`.
No varying coefficient occurs in these constants (`energy-complete-residual`). -/
theorem exists_selected_source_pdo_budgets
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (L : ℝ) :
    ∃ R > (0 : ℝ), ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      GraphNormalAmplitudeBounds
        (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
          (selectedSourceSymbol f p L)) R (C (2 * (d+2))) ∧
      ∀ m ξ is, is.length ≤ m → ∀ z,
        ‖matrixAmplitudeCoordinateDerivList is
          (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
            (selectedSourceSymbol f p L) ξ) z‖ ≤ C m := by
  obtain ⟨ho, hs, hco, hcs, hcarrier⟩ := chartPhysicalMasks_properties f p
  obtain ⟨hρ, hsρ, _⟩ := chartConicMask_properties f p
  obtain ⟨B, hB⟩ := (hco.union hcs).exists_bound_of_continuousOn continuous_id.continuousOn
  let R := |B| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hoR (y : E) (hy : y ∈ tsupport (chartOutputMask f p)) : ‖y‖ ≤ R :=
    (hB y (Or.inl hy)).trans (by dsimp [R]; linarith [le_abs_self B])
  have hsR (y : E) (hy : y ∈ tsupport (chartInputMask f p)) : ‖y‖ ≤ R :=
    (hB y (Or.inr hy)).trans (by dsimp [R]; linarith [le_abs_self B])
  have hβ := complex_dilatedConicMask_pdo_bounds (f.angularMask p)
    (f.angularMask_smooth p) (f.angularMask_range p) L
  have hbρ := (complex_conicMask_pdo_bounds (f.spatialMask p)
    (f.spatialMask_properties p).1 (f.spatialMask_properties p).2.1).2
  obtain ⟨C, hC, hb⟩ := exists_source_pdo_budgets (q := d+1)
    (isCompact_closedBall ((physicalCoordinates (f.chart p).index).symm x) RQ)
    _ _ ho hs hcarrier hcs (f.chart p).sourceMask
    (f.chart p).sourceMask_smooth (f.chart p).sourceMask_compact
    (f.chart p).radialSection _ _ hρ hsρ
    (hβ.1.comp (physicalCoordinates (f.chart p).index).contDiff)
    zero_le_one zero_le_one hbρ (fun ζ ↦ hβ.2 (physicalCoordinates (f.chart p).index ζ))
    R hoR hsR
  exact ⟨R, hR, C, hC, hb⟩

/-- On the common physical ball the SAME diagonal source mask is one on
the right multiplier. This is a pointwise symbol identity; the physical
source mask remains on the right of the corresponding operator
(`energy-complete-residual`). -/
theorem selectedSourceSymbol_on_common_ball
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) {y : E}
    (hy : y ∈ closedBall x (4 * f.physicalRadius)) (ζ : E) :
    selectedSourceSymbol f p f.radialThreshold
      ((physicalCoordinates (f.chart p).index).symm y)
      ((physicalCoordinates (f.chart p).index).symm ζ) =
      (dilatedConicMask (f.angularMask p) f.radialThreshold ζ : ℂ) • (1 : CMat) := by
  let e := physicalCoordinates (f.chart p).index
  by_cases hz : dilatedConicMask (f.angularMask p) f.radialThreshold ζ = 0
  · simp only [selectedSourceSymbol, ContinuousLinearEquiv.apply_symm_apply,
      hz, Complex.ofReal_zero, mul_zero, zero_smul]
  have hζ : e.symm ζ ∈ tsupport
      (dilatedConicMask (f.angularMask p) f.radialThreshold ∘ e) :=
    subset_tsupport _ (by
      change dilatedConicMask (f.angularMask p) f.radialThreshold (e (e.symm ζ)) ≠ 0
      rwa [e.apply_symm_apply])
  have hsource := f.conicSourceSymbol_eq_one p
    (y := e.symm y) (by
      change e (e.symm y) ∈ closedBall x (4 * f.physicalRadius)
      rwa [e.apply_symm_apply]) hζ
  dsimp only [e] at hsource
  simp only [selectedSourceSymbol, hsource, one_mul,
    ContinuousLinearEquiv.apply_symm_apply]

/-- Exact finite source ledger on the common physical ball. The angular
complement and the literal low-frequency cutoff are retained as summands;
the sum of characteristic source PDOs alone is not the identity.
Consumer: the `Op(α)-I` term of `prop:complete-residual`. -/
theorem selectedSourceSymbols_complete_partition
    (f : ActualMaskFamily Ω x RQ A₀ K M) {y : E}
    (hy : y ∈ closedBall x (4 * f.physicalRadius)) (ζ : E) :
    (∑ p, selectedSourceSymbol f p f.radialThreshold
      ((physicalCoordinates (f.chart p).index).symm y)
      ((physicalCoordinates (f.chart p).index).symm ζ)) +
      (dilatedConicMask (fun η ↦ 1 - ∑ p, f.angularMask p η) f.radialThreshold ζ : ℂ) •
        (1 : CMat) +
      (FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0
        (f.radialThreshold⁻¹ • ζ) : ℂ) • (1 : CMat) = 1 := by
  classical
  simp_rw [selectedSourceSymbol_on_common_ball f _ hy]
  rw [← Finset.sum_smul, ← add_smul, ← add_smul]
  have h := congrArg (fun a : ℝ ↦ (a : ℂ)) (f.complete_partition ζ)
  simp only [Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_one] at h
  rw [h, one_smul]

end JanetCartan.RegularSector.FinitePdo
