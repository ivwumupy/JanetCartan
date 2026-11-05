module

public import JanetCartan.Analysis.Microlocal.EllipticLocalization.Support
public import JanetCartan.Analysis.Microlocal.EllipticComplement.PositionBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.MaskJets

/-!
# Actual elliptic symbol budgets with a supplied output mask

Apply the completed weighted symbol producer and the shared physical mask-jet
estimates to the supplied common output. The inverse and full residual retain
their degree-minus-one weight and original coefficient reserve. The source
keeps degree zero and has no coefficient cost. Consumers: the common-output
polynomial restriction estimates in `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticLocalization
open EllipticComplement FiniteMasks.ActualFamily Characteristic.AlgebraicSymbols Characteristic.PdoRealization
open Characteristic.EndpointPdoBounds FourierIntegral AmplitudeBound
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "Coeff" => Fin (d + 1) → Mat
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
local notation "χs" => fun z ↦ (f.inputMask z : ℂ)

/-- The inverse and its physical derivative supply the actual weighted
position bounds of the canonical PDO calculus. The low original order is
`2*(d+2)+2`; the high position jets have reserve one, uniformly in `L`
(`app:ch_regular_base:eq:sector-theorem-solution`, `measured-adjoint`). -/
theorem exists_elliptic_masked_pdo_budgets (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω)
    (χout : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hco : HasCompactSupport χout)
    (hsout : tsupport χout ⊆ closedBall x (2*f.physicalRadius)) :
    ∃ R > 0, ∃ N > 0, ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
    ∀ L ≥ f.radialThreshold, ∀ (Q : E → Coeff) (B : E → Mat),
      ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
      MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
      cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M →
      cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M →
      ∀ s ∈ ({ellipticInverseSymbol f hK L Q, ellipticResidualSymbol f hK L Q B} :
        Set (E → E → CMat)),
        let a := maskedPhysicalPDOCycleSymbol χout (χs) s
        GraphNormalAmplitudeBounds a R N ∧
        (∀ ξ is, is.length ≤ 2*(d+2)+1 → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (a ξ) z‖ ≤ N) ∧
        ∀ m ξ is, is.length ≤ m → ∀ z,
          (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (a ξ) z‖ ≤
            C m * (1 + cNorm (closedBall x RQ) (m+1) Q + cNorm (closedBall x RQ) (m+1) B) := by
  obtain ⟨D, hD, hpos⟩ := exists_ellipticSymbols_weighted_cNorm f hK hΩ hRQΩ
  have hs := Complex.ofRealCLM.contDiff.comp f.inputMask_smooth
  have hcs := f.inputMask_compact.comp_left Complex.ofReal_zero
  obtain ⟨R, hR, hbox⟩ :=
    exists_common_maskedPhysicalPDOCycleSymbol_support (q := d+1) hco hcs
  choose F hF htransfer using fun m ↦ exists_maskedPhysicalPDOCycleSymbol_derivative_constant
    (q := d+1) x (2*f.physicalRadius) χout (χs) ho hs hco hcs hsout m
  let C m := F m * D m
  have hC m : 0 < C m := mul_pos (hF m) (hD m)
  let k := 2*(d+2)+1
  let N := C k * (1 + 2 * max 0 M)
  refine ⟨R, hR, N, mul_pos (hC k) (by positivity), C, hC, ?_⟩
  intro L hL Q B hQ hB hmap hQlow hBlow s hmem a
  obtain ⟨hsm, hj⟩ := hpos L hL Q B hQ hB hmap
    ((cNorm_mono_order (by omega : 1 ≤ 2*(d+2)+2)).trans hQlow)
    ((cNorm_mono_order (by omega : 0 ≤ 2*(d+2)+2)).trans hBlow) s hmem
  have hb (m : ℕ) ξ is (hi : is.length ≤ m) z :
      (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (a ξ) z‖ ≤
          C m * (1 + cNorm (closedBall x RQ) (m+1) Q + cNorm (closedBall x RQ) (m+1) B) := by
    have hhi : 0 ≤ 1 + cNorm (closedBall x RQ) (m+1) Q + cNorm (closedBall x RQ) (m+1) B :=
      by linarith [cNorm_nonneg (closedBall x RQ) (m+1) Q, cNorm_nonneg (closedBall x RQ) (m+1) B]
    exact (htransfer m s hsm _ (mul_nonneg (hD m).le hhi) (fun η ↦ hj η m) ξ is hi z).trans_eq
      (mul_assoc _ _ _).symm
  have hlow ξ is (hi : is.length ≤ k) z :
      (1 + ‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is (a ξ) z‖ ≤ N := by
    refine (hb k ξ is hi z).trans (mul_le_mul_of_nonneg_left ?_ (hC k).le)
    dsimp only [k]
    linarith [le_max_right 0 M]
  refine ⟨⟨contDiff_maskedPhysicalPDOCycleSymbol ho hs hsm, hbox s, ?_⟩, hlow, hb⟩
  intro ξ is hi z
  exact (le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg ξ])).trans
    (hlow ξ is (by dsimp [k]; omega) z)

/-- The independent source symbol has uniform unweighted bounds at every
position order. No original coefficient enters its budget; these are the
actual principal-source regularizations in `sector-theorem-identity`. -/
theorem exists_ellipticSource_masked_pdo_budgets
    (χout : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hco : HasCompactSupport χout)
    (hsout : tsupport χout ⊆ closedBall x (2*f.physicalRadius)) :
    ∃ R > 0, ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ L : ℝ, let a := maskedPhysicalPDOCycleSymbol χout (χs) (ellipticSourceSymbol f hK L)
      GraphNormalAmplitudeBounds a R (C (2*(d+2))) ∧
      ∀ m ξ is, is.length ≤ m → ∀ z, ‖matrixAmplitudeCoordinateDerivList is (a ξ) z‖ ≤ C m := by
  let S := closedBall x (2*f.physicalRadius)
  have hs := Complex.ofRealCLM.contDiff.comp f.inputMask_smooth
  have hcs := f.inputMask_compact.comp_left Complex.ofReal_zero
  choose D hD hmask using fun m ↦ exists_masked_position_derivative_constant (q := d+1)
    (isCompact_closedBall x (2*f.physicalRadius)) χout (χs) ho hs hsout hcs m
  obtain ⟨R, hR, hbox⟩ := exists_common_maskedPhysicalPDOCycleSymbol_support (q := d+1) hco hcs
  let C m := D m * cNorm S m (fun _ : E ↦ (1 : CMat))
  refine ⟨R, hR, C, fun m ↦ mul_nonneg (hD m).le (cNorm_nonneg _ _ _), ?_⟩
  intro L a
  have ha := ellipticSourceMask_properties f hK L
  have hb (m : ℕ) (ξ : E) is (hi : is.length ≤ m) z :
      ‖matrixAmplitudeCoordinateDerivList is (a ξ) z‖ ≤ C m := by
    let t : ℂ := (ellipticSourceMask f hK L ((2*Real.pi) • ξ) : ℂ)
    have ht : ‖t‖ ≤ 1 := by
      have h := ha.2 ((2*Real.pi) • ξ)
      simpa only [t, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
    apply (hmask m univ isOpen_univ (subset_univ _) (fun _ ↦ t • (1 : CMat))
      contDiffOn_const is hi z).trans
    rw [cNorm_const_complex_smul m t (f := fun _ : E ↦ (1 : CMat)) (fun _ _ ↦ contDiffAt_const)]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (cNorm_nonneg _ _ _) ht) (hD m).le
  exact ⟨⟨contDiff_maskedPhysicalPDOCycleSymbol ho hs
    (((Complex.ofRealCLM.contDiff.comp ha.1).comp contDiff_snd).smul contDiff_const),
    hbox _, hb _⟩, hb⟩

end JanetCartan.RegularSector.EllipticLocalization
