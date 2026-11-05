module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.CoefficientLocalization

/-!
# Physical reality pairing in the selected coordinates

The exact equation returned by `completeResidual_of_selected_physical_chart`
passes to the physical plus pairing with the ORIGINAL locally smooth real
coefficients. Coefficient extensions are constructed on each test carrier.
The principal `Op(α)` remains separate from all three residual terms.
Source: `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral
open JanetCartan.CharacteristicTransport.CompleteResidual
open FourierIntegral FourierIntegral.FullLowBounds
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "C2" => SpacetimeL2 d (d + 1)

/-- The SAME complete physical solver pairs as `S + cSc`, with no extra
factor of `i` and with all residual summands retained. The sector equation
is supplied by `completeResidual_of_selected_physical_chart`; this deduction
adds no global coefficient regularity assumption.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem physicalPair_test_of_coordinate_residual
    (i : Fin (d + 1)) {Ω : Set E} (hΩ : IsOpen Ω)
    (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    {U : Set E} (hUΩ : ∀ x ∈ U, physicalCoordinates i x ∈ Ω)
    (S principal endpoint retarded derivative : C2 →L[ℂ] C2)
    (hsector : ∀ f φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ j,
      physicalTestAction (coefficient i Q) (zeroth i B) (fun x ↦ (S f x).ofLp) φ j =
        ∫ x, φ x • ((principal + (endpoint + retarded + (1 / Complex.I) • derivative)) f) x j)
    (f : C2) (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (j : Fin (d + 1)) :
    physicalTestAction (coefficient i Q) (zeroth i B)
      (fun x ↦ (physicalPairedSectorSum {()} (fun _ : Unit ↦ S) f x).ofLp) φ j =
      ∫ x, φ x • ((physicalPairedSectorSum {()} (fun _ : Unit ↦ principal) +
        physicalPairedSectorSum {()} (fun _ : Unit ↦ endpoint + retarded +
          (1 / Complex.I) • derivative)) f) x j := by
  obtain ⟨Ae, Be, hAe, hBe, he⟩ := exists_smooth_coordinate_coefficients i hΩ Q B hQ hB
    (isClosed_tsupport φ) (fun x hx ↦ hUΩ x (hφU hx))
  have hAe' (a k l) : ContDiff ℝ ∞ (fun x ↦ Ae x a k l) :=
    (Matrix.entryLinearMap ℝ ℝ k l).toContinuousLinearMap.contDiff.comp
      ((contDiff_pi.mp hAe) a)
  have hBe' (k l) : ContDiff ℝ ∞ (fun x ↦ Be x k l) :=
    (Matrix.entryLinearMap ℝ ℝ k l).toContinuousLinearMap.contDiff.comp hBe
  have htest (u : E → Fin (d + 1) → ℂ) :
      physicalTestAction Ae Be u φ j =
        physicalTestAction (coefficient i Q) (zeroth i B) u φ j :=
    physicalTestAction_eq_of_coefficients_on_support Ae _ Be _ u φ
      (fun x hx ↦ (he x hx).1.eq_of_nhds) (fun x hx ↦ (he x hx).2.eq_of_nhds) j
  rw [← htest]
  exact completeResidual_physicalPairedSectorSum_test Ae Be hAe' hBe' {()}
    (fun _ : Unit ↦ S) (fun _ ↦ principal) (fun _ ↦ endpoint) (fun _ ↦ retarded)
    (fun _ ↦ derivative) hφ hcφ j
    (fun _ _ v ↦ (htest _).trans (hsector (graphTestToLp v) φ hφ hcφ hφU j)) f

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
