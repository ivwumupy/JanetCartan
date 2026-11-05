module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization.Fourier
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization.Matrix

/-!
# From elapsed graph jet bounds to actual spacetime Fourier Sobolev bounds

This is the concrete space comparison between
`exists_buffered_elapsed_graph_sobolev_bound` and
`localized_strongIntegral_sobolev_bound`, for
`app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`.

The input identification is isometric. The output is the actual zeroth jet,
with Fourier membership and a fixed norm comparison proved from classical
derivatives and density. Finite channels retain their Hilbert norms. The
parent supplies the exact dense test action of its actual localized graph;
uniqueness then transfers the estimate without assuming regularity of that
operator. Instantiating those graph identities remains the parent's task.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization

open RetardedSobolev.Spaces FourierIntegral FiniteChain.Graph.KernelLimits
open Pseudodifferential AmplitudeBound RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}
variable (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d + 1))
variable (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)

/-- The concrete zeroth-jet realization preserves Hilbert channel norms in
the Fourier comparison. The constant is independent of the number of channels
(`app:ch_regular:eq:chain-tail`). -/
theorem vectorZeroJet_fourier_bound (m : ℕ)
    (u : PiLp 2 (fun _ : Fin q => Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)))) :
    MemVectorFourierSobolev (m : ℝ) (vectorZeroJet J hJ m u) ∧
      vectorFourierSobolevNorm (m : ℝ) (vectorZeroJet J hJ m u) ≤
        fourierComparisonConstant J m * ‖u‖ := by
  constructor
  · change MemMatrixFourierSobolev (m : ℝ)
      (finiteL2CoordinateIsometry volume (vectorZeroJet J hJ m u))
    rw [vectorZeroJet_coordinates]
    exact fun a => (physicalZeroJet_fourier_bound J hJ m (u a)).1
  · change matrixFourierSobolevNorm (m : ℝ)
      (finiteL2CoordinateIsometry volume (vectorZeroJet J hJ m u)) ≤ _
    rw [vectorZeroJet_coordinates]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (fourierComparisonConstant_pos J m).le
      (norm_nonneg u))).mp
    change matrixFourierSobolevNorm (m : ℝ)
      (WithLp.toLp 2 (fun a => physicalZeroJet J hJ m (u a))) ^ 2 ≤
        (fourierComparisonConstant J m * ‖u‖) ^ 2
    rw [matrixFourierSobolevNorm_sq, mul_pow, PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ a : Fin q, (fourierComparisonConstant J m * ‖u a‖) ^ 2 :=
        Finset.sum_le_sum (fun a _ => pow_le_pow_left₀ (fourierSobolevNorm_nonneg _ _)
          (physicalZeroJet_fourier_bound J hJ m (u a)).2 2)
      _ = _ := by simp only [mul_pow, Finset.mul_sum]

/-- The bounded matrix extension has an actual spacetime L² realization
with Fourier Hᵐ membership and the bound needed by
`localized_strongIntegral_sobolev_bound`. No estimate on the realized operator
is a premise (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem matrixRealization_fourier_bound {m : ℕ}
    (Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))) (u : SpacetimeL2 d q) :
    MemVectorFourierSobolev (m : ℝ) (matrixRealization J hJ Op u) ∧
      vectorFourierSobolevNorm (m : ℝ) (matrixRealization J hJ Op u) ≤
        fourierComparisonConstant J m * ‖matrixOperator Op‖ * ‖u‖ := by
  have h := vectorZeroJet_fourier_bound J hJ m (matrixOperator Op (inputEquiv J hJ u))
  change MemVectorFourierSobolev (m : ℝ)
      (vectorZeroJet J hJ m (matrixOperator Op (inputEquiv J hJ u))) ∧ _
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    _ ≤ fourierComparisonConstant J m * (‖matrixOperator Op‖ * ‖inputEquiv J hJ u‖) :=
      mul_le_mul_of_nonneg_left ((matrixOperator Op).le_opNorm _) (fourierComparisonConstant_pos J m).le
    _ = _ := by rw [LinearIsometryEquiv.norm_map, mul_assoc]

/-- Exact physical dense-test action transfers the proved Fourier bound to
any bounded actual spacetime operator. The test-action producer is the
parent's `EvolutionIntegral` graph realization; its Sobolev estimate is a
conclusion here (`app:ch_regular:eq:chain-tail`). -/
theorem fourier_bound_of_test_action {m : ℕ}
    (Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)))
    (T : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hT : ∀ (f : Fin q → Test d) (a : Fin q),
      finiteL2CoordinateIsometry volume (T (physicalTestToL2 J hJ f)) a =ᵐ[volume]
        ((matrixOperator Op (completedTestVector 0 f) a).val (zeroIndex d m)) ∘
          (graphInputCoordinates J).symm)
    (u : SpacetimeL2 d q) :
    MemVectorFourierSobolev (m : ℝ) (T u) ∧
      vectorFourierSobolevNorm (m : ℝ) (T u) ≤
        fourierComparisonConstant J m * ‖matrixOperator Op‖ * ‖u‖ := by
  rw [eq_matrixRealization_of_test_action J hJ Op T hT]
  exact matrixRealization_fourier_bound J hJ Op u

/-- The exact Cartesian test-action interface exported by the graph jet
constructor yields the actual spacetime Fourier estimate. This is the direct
consumer bridge to `localized_strongIntegral_sobolev_bound`; it assumes no
Fourier comparison or leakage estimate (`app:ch_regular:eq:chain-tail`). -/
theorem fourier_bound_of_cartesian_test_action {m : ℕ}
    (Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
      Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)))
    (T : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hT : ∀ (f : Fin q → Test d) (a : Fin q),
      (fun p : (Fin d → ℝ) × ℝ =>
        finiteL2CoordinateIsometry volume (T (physicalTestToL2 J hJ f)) a (J (p.2, p.1))) =ᵐ[volume]
        (matrixOperator Op (completedTestVector 0 f) a).val (zeroIndex d m))
    (u : SpacetimeL2 d q) :
    MemVectorFourierSobolev (m : ℝ) (T u) ∧
      vectorFourierSobolevNorm (m : ℝ) (T u) ≤
        fourierComparisonConstant J m * ‖matrixOperator Op‖ * ‖u‖ := by
  rw [eq_matrixRealization_of_cartesian_test_action J hJ Op T hT]
  exact matrixRealization_fourier_bound J hJ Op u

/-- One positive constant is fixed before all bounded matrix operators and
all data, with the exact physical test action and uniqueness retained.
This packages the concrete implication required by the elapsed-graph parent
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_uniform_matrixRealization_fourier_bound (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ Op : Fin q → Fin q → Sobolev 0 (volume : Measure ((Fin d → ℝ) × ℝ)) →L[ℂ]
          Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ)),
        ∃ T : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
          (∀ u, MemVectorFourierSobolev (m : ℝ) (T u) ∧
            vectorFourierSobolevNorm (m : ℝ) (T u) ≤ K * ‖matrixOperator Op‖ * ‖u‖) ∧
          (∀ (f : Fin q → Test d) (a : Fin q),
            finiteL2CoordinateIsometry volume (T (physicalTestToL2 J hJ f)) a =ᵐ[volume]
              ((matrixOperator Op (completedTestVector 0 f) a).val (zeroIndex d m)) ∘
                (graphInputCoordinates J).symm) ∧
          ∀ U : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
            (∀ (f : Fin q → Test d) (a : Fin q),
              finiteL2CoordinateIsometry volume (U (physicalTestToL2 J hJ f)) a =ᵐ[volume]
                ((matrixOperator Op (completedTestVector 0 f) a).val (zeroIndex d m)) ∘
                  (graphInputCoordinates J).symm) → U = T := by
  refine ⟨fourierComparisonConstant J m, fourierComparisonConstant_pos J m, fun Op =>
    ⟨matrixRealization J hJ Op, matrixRealization_fourier_bound J hJ Op,
      matrixRealization_test_action J hJ Op, ?_⟩⟩
  exact fun U hU => eq_matrixRealization_of_test_action J hJ Op U hU

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization
