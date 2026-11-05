module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.Diagonal
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.PhysicalAction.Products

/-!
# A single high norm for the actual upper-endpoint matrix product

The `A_t W₁(t,t)` term in `paper-v2.tex`,
`app:ch_regular_base:eq:energy-complete-residual`, is estimated with the
existing compact-ball tame product theorem. In particular the two high
norms are added, never multiplied. Only the zeroth normalized amplitude
budget is needed to fix this product constant. For the actual producer
this requires original coefficient orders ten in `Q` and nine in `B`;
the larger fixed low reserve needed for the PDO theorem is separate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
open EvolutionIntegral EvolutionIntegral.SymbolBudgets AmplitudeBounds.PhysicalAction
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => EvolutionIntegral.SymbolBudgets.TwoTimePoint d
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- Tame Frobenius bounds for the SAME diagonal matrix product, uniformly
in every normalized shell. Constants precede the varying coefficient and
amplitude. The only symbol inputs are the published joint two-time budgets;
no PDO derivative estimate is assumed. Consumer: the gain-one endpoint PDO
in `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_diagonal_matrixProduct_cNorm_bounds
    (x₀ : E) {r : ℝ} (hr : 0 < r) (MA MW : ℝ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (U : Set E), IsOpen U → closedBall x₀ r ⊆ U →
      ∀ (A : E → Mat), ContDiffOn ℝ ∞ A U → cNorm (closedBall x₀ r) 0 A ≤ MA →
      ∀ (J : Set T), IsCompact J →
      ∀ (W : TwoTimeAmplitude d q), ContDiff ℝ ∞ (jointAmplitude W) →
        BoundedTwoTimeOrderSeminorm 1 J 0 W → twoTimeOrderSeminorm 1 J 0 W ≤ MW →
      ∀ R : ℝ, 1 ≤ R → ∀ η : Euclidean d,
        MapsTo (diagonalPoint η) (closedBall x₀ r) J →
      ∀ m, BoundedTwoTimeOrderSeminorm 1 J m W →
        cNorm (closedBall x₀ r) m
          (fun x : E ↦ R • (A x * W (x 0) (x 0) (spatialPart x) (R • η))) ≤
        C m * (1 + cNorm (closedBall x₀ r) m A + twoTimeOrderSeminorm 1 J m W) := by
  obtain ⟨C, hC, htame⟩ := exists_smoothPair_cNorm_bounds x₀ hr MA MW
    (fun p : Mat × Mat ↦ p.1 * p.2) (contDiff_fst.mul contDiff_snd)
  refine ⟨C, hC, ?_⟩
  intro U hU hKU A hA hA0 J hJ W hW hW0 hMW R hR η hmap m hWm
  let v : E → Mat := fun x ↦ R • W (x 0) (x 0) (spatialPart x) (R • η)
  have hv : ContDiff ℝ ∞ v := by
    have hp : ContDiff ℝ ∞ (diagonalPoint (R • η)) :=
      diagonalLinear.contDiff.add contDiff_const
    simpa only [Function.comp_apply, diagonalPoint_eq, jointAmplitude] using (hW.comp hp).const_smul R
  have hv0 : cNorm (closedBall x₀ r) 0 v ≤ MW := by
    have h : cNorm (closedBall x₀ r) 0 v ≤ twoTimeOrderSeminorm 1 J 0 W := by
      simpa only [pow_one] using cNorm_diagonal_orderField_le hJ W hW 1 0 hW0 hR η hmap
    exact h.trans hMW
  have hvm : cNorm (closedBall x₀ r) m v ≤ twoTimeOrderSeminorm 1 J m W := by
    simpa only [pow_one] using cNorm_diagonal_orderField_le hJ W hW 1 m hWm hR η hmap
  have h := htame U hU hKU A v hA hv.contDiffOn hA0 hv0 m
  have he : (fun x ↦ A x * v x) =
      (fun x ↦ R • (A x * W (x 0) (x 0) (spatialPart x) (R • η))) := by
    funext x
    exact Matrix.mul_smul _ _ _
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith) (hC m).le)

end JanetCartan.RegularSector.Characteristic.EndpointPdoBounds
