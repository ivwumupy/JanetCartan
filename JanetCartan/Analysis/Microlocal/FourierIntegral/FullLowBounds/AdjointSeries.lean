module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion

/-!
# Strong adjoint convergence through the actual source series

For `app:ch_regular_base:thm:actual-calculus`, Step 1, the adjoint source masks
occur on the left of the coefficient adjoints. Dominated convergence of this
series supplies the strong adjoint limit needed by `FullLowBounds.SourceSeries`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullLowBounds
open SourceExpansion AmplitudeBound
variable {n r : ℕ} {R ℓ : ℝ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Strong coefficient adjoint convergence passes through the literal reversed
source series. The bound is the summable decay derived from the original full
symbol jets (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem tendsto_sourceOperatorSeries_adjoint_apply
    (hn : 0 < n) (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
    (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    (μ : ℕ) {B : ℝ} (hb : HasFullSourceSymbolBound A (μ + lowReserve n) B)
    (β : SourceCutoff n R ℓ) (C : (Fin n → ℤ) → H →L[ℂ] H) (G : ℝ)
    (hgraph : ∀ k b, HasCoefficientSymbolBound (matrixCoefficient ℓ A k) μ b →
      ‖C k‖ ≤ G * b)
    (Creg : ℕ → (Fin n → ℤ) → H →L[ℂ] H)
    (hreg : ∀ j k b, HasCoefficientSymbolBound (matrixCoefficient ℓ A k) μ b →
      ‖Creg j k‖ ≤ G * b)
    (hlim : ∀ k u, Tendsto (fun j ↦ (Creg j k).adjoint u) atTop
      (𝓝 ((C k).adjoint u))) (u : H) :
    Tendsto (fun j ↦ (sourceOperatorSeries β (Creg j)).adjoint u) atTop
      (𝓝 ((sourceOperatorSeries β C).adjoint u)) := by
  let b : (Fin n → ℤ) → ℝ := fun k ↦
    G * ((r : ℝ)^2 * coefficientConstant n (lowReserve n) ℓ * B *
      decayWeight (lowReserve n) k)
  have hbSum : Summable b :=
    (((summable_decayWeight_lowReserve n).mul_left _).mul_left _)
  have hsum (D : (Fin n → ℤ) → H →L[ℂ] H)
      (hD : ∀ k b, HasCoefficientSymbolBound (matrixCoefficient ℓ A k) μ b →
        ‖D k‖ ≤ G * b) :
      (sourceOperatorSeries β D).adjoint u =
        ∑' k, (sourceModulation β k).adjoint ((D k).adjoint u) := by
    exact (hasSum_apply
      (hasSum_sourceOperatorTerm_adjoint hn hℓ hR A hs hA μ hb β D G hD) u).tsum_eq.symm
  simp_rw [hsum C hgraph, hsum (Creg _) (hreg _)]
  apply tendsto_tsum_of_dominated_convergence (hbSum.mul_right ‖u‖)
  · intro k
    exact (sourceModulation β k).adjoint.continuous.continuousAt.tendsto.comp (hlim k u)
  · exact Eventually.of_forall fun j k ↦ by
      have hk := norm_sourceCoefficientOperator_le hn hℓ hR A hs hA μ hb
        (Creg j) G (hreg j) k
      have hm : ‖(sourceModulation (r := r) β k).adjoint‖ ≤ 1 := by
        simpa only [LinearIsometryEquiv.norm_map] using norm_sourceModulation_le (r := r) β k
      calc
        ‖(sourceModulation β k).adjoint ((Creg j k).adjoint u)‖ ≤
            ‖(sourceModulation β k).adjoint‖ * ‖(Creg j k).adjoint u‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖(Creg j k).adjoint u‖ := mul_le_of_le_one_left (norm_nonneg _) hm
        _ ≤ ‖(Creg j k).adjoint‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ b k * ‖u‖ := by
          simpa only [LinearIsometryEquiv.norm_map] using
            mul_le_mul_of_nonneg_right hk (norm_nonneg u)

end JanetCartan.FourierIntegral.FullLowBounds
