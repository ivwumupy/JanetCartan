module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.PhysicalBudget

/-!
# Tame physical action with the original coefficients

The full physical action is a fixed smooth function of the coefficient values
and the first jet of the symbol. Compact-range tame composition keeps all
high norms additive and costs exactly one derivative. The zeroth-order
coefficient and the derivative of the entire symbol are retained.
Consumer: `directPDOSymbols` index three, in
`app:ch_regular_base:eq:energy-complete-residual` of `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
open ResidualCoordinates RootFamily ActualCarriers EvolutionIntegral
open JanetCartan.CharacteristicTransport.CompleteResidual
open FullPhaseCharts.InverseEstimates NullTransport.AmplitudeTame
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "Coeff" => Fin (d + 1) → Mat

private theorem contDiff_positionSlice (c : E → E → CMat)
    (hc : ContDiff ℝ ∞ (Function.uncurry c)) (η : E) :
    ContDiff ℝ ∞ (fun y ↦ c y η) :=
  hc.comp (contDiff_id.prodMk (contDiff_const (c := η)))

/-- Transfer the already constructed weighted algebraic budget through the
literal physical action. The only low coefficient order needed here is one
for `Q` and zero for `B`; the integer-gain application below requires its
explicit larger finite order. The final construction instantiates `hcBound`
with `exists_conicAlgebraicSymbol_weighted_cNorm_bounds` and both smoothness
inputs with the supported-extension theorems.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_physicalSymbolApply_weighted_cNorm_transfer
    (i : Fin (d + 1)) (x : E) {R : ℝ} (hR : 0 < R) (xQ : E) (RQ : ℝ)
    (hphysical : MapsTo (physicalCoordinates i) (closedBall x R) (closedBall xQ RQ))
    (M : ℝ) (D : ℕ → ℝ) (hD : ∀ m, 0 < D m) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (Ω : Set E), IsOpen Ω → closedBall xQ RQ ⊆ Ω →
        ∀ (Q : E → Coeff) (B : E → Mat) (c : E → E → CMat),
          ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
          ContDiff ℝ ∞ (Function.uncurry c) →
          let p := physicalSymbolApply (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
            (fun y ↦ (zeroth i B y).map Complex.ofReal) c
          ContDiff ℝ ∞ (Function.uncurry p) →
          cNorm (closedBall xQ RQ) 1 Q ≤ M → cNorm (closedBall xQ RQ) 0 B ≤ M →
          (∀ η m, (1 + ‖η‖) * cNorm (closedBall x R) m (fun y ↦ c y η) ≤
            D m * (1 + cNorm (closedBall xQ RQ) m Q)) →
          ∀ η m, (1 + ‖η‖) * cNorm (closedBall x R) m (fun y ↦ p y η) ≤
            C m * (1 + cNorm (closedBall xQ RQ) (m + 1) Q +
              cNorm (closedBall xQ RQ) (m + 1) B) := by
  obtain ⟨A, hA, hact⟩ := exists_physicalSymbolApply_slice_cNorm_bound
    i x hR xQ RQ hphysical M (D 1 * (1 + M))
  refine ⟨fun m ↦ A m * (1 + D (m + 1)),
    fun m ↦ mul_pos (hA m) (by linarith [hD (m + 1)]), ?_⟩
  intro Ω hΩ hKQ Q B c hQ hB hc p hp hQM hBM hcBound η m
  let w := 1 + ‖η‖
  have hw : 0 < w := by dsimp [w]; positivity
  have hs : ContDiff ℝ ∞ (fun y ↦ c y η) := contDiff_positionSlice c hc η
  have hps : ContDiff ℝ ∞ (fun y ↦ p y η) := contDiff_positionSlice p hp η
  have hf : ContDiff ℝ ∞ (fun y ↦ w • c y η) := (contDiff_const (c := w)).smul hs
  have hn (j : ℕ) : cNorm (closedBall x R) j (fun y ↦ w • c y η) =
      w * cNorm (closedBall x R) j (fun y ↦ c y η) := by
    rw [show (fun y ↦ w • c y η) = w • (fun y ↦ c y η) from rfl,
      cNorm_smul w (hs.of_le (by simp)), Real.norm_eq_abs, abs_of_pos hw]
  have hlow : cNorm (closedBall x R) 1 (fun y ↦ w • c y η) ≤ D 1 * (1 + M) := by
    rw [hn]
    exact (hcBound η 1).trans
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hQM) (hD 1).le)
  have h := hact Ω hΩ hKQ Q B (fun y ↦ w • c y η) hQ hB hf
    ((cNorm_mono_order (show 0 ≤ 1 by omega)).trans hQM) hBM hlow m
  have he : (fun y ↦ physicalSymbolApply
      (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
      (fun y ↦ (zeroth i B y).map Complex.ofReal) (fun y _ ↦ w • c y η) y 0) =
      w • (fun y ↦ p y η) := by
    funext y
    exact physicalSymbolApply_real_frequency_smul _ _ (fun y _ ↦ c y η) (fun _ ↦ w) y 0
  rw [he, cNorm_smul w (hps.of_le (by simp)), Real.norm_eq_abs, abs_of_pos hw, hn] at h
  apply h.trans
  have hcb := hcBound η (m + 1)
  have hq := cNorm_nonneg (closedBall xQ RQ) (m + 1) Q
  have hb := cNorm_nonneg (closedBall xQ RQ) (m + 1) B
  have hmajor : 1 + cNorm (closedBall xQ RQ) (m + 1) Q +
      cNorm (closedBall xQ RQ) (m + 1) B +
      w * cNorm (closedBall x R) (m + 1) (fun y ↦ c y η) ≤
      (1 + D (m + 1)) * (1 + cNorm (closedBall xQ RQ) (m + 1) Q +
        cNorm (closedBall xQ RQ) (m + 1) B) := by
    dsimp [w]
    nlinarith [mul_nonneg (hD (m + 1)).le hb]
  exact (mul_le_mul_of_nonneg_left hmajor (hA m).le).trans_eq (by ring)

end JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
