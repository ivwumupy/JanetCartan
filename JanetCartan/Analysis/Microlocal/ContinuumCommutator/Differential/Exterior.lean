module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Exterior.Extension

/-!
# Fixed exterior multiplication commutator

For `app:ch_background:eq:bg-commutator`, the exact ordered Leibniz formula
removes the all-datum branch. Its surviving terms define a bounded operator
`H^(s-1) → L²`, for arbitrary finite-dimensional real Hilbert-valued fields.
Smooth density identifies it with the distributional commutator. The coefficient
`(1-χ)^2` of the fixed exterior normal is included as a specialization.
The consumer is the full continuum differential commutator and then the integer
regularity step in `app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace JanetCartan.ContinuumCommutator.Exterior

open PeriodicSobolevSpace

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- A real scalar multiplier is symmetric for the actual L² pairing
(`app:ch_background:prop:bg-inverse`). -/
theorem multiplication_inner (q : Torus n → ℝ) (hq : Continuous q)
    (u v : PeriodicL2 n F) :
    ⟪multiplication q hq u, v⟫ = ⟪u, multiplication q hq v⟫ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplication_ae q hq u, multiplication_ae q hq v] with x hu hv
  simp only [hu, hv, real_inner_smul_left, real_inner_smul_right]

private theorem smooth_derivative_inner (is : List (Fin n))
    (f φ : Torus n → F) (hf : IsSmoothPeriodic f) (hφ : IsSmoothPeriodic φ) (s : ℕ) :
    ⟪toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f) (hf.coordinateDerivList is)),
      toL2 0 (ofSmooth 0 φ hφ)⟫ =
      (-1 : ℝ) ^ is.length * ⟪toL2 s (ofSmooth s f hf),
        toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is.reverse φ)
          (hφ.coordinateDerivList is.reverse))⟫ := by
  simp only [inner_periodicL2_ofSmooth]
  exact hf.hasPeriodicWeakDerivativeList is s 0 φ hφ

/-- Testing the completed commutator agrees with the difference of the two
transposed differential expressions, on every `H^(|is|-1)` datum
(`app:ch_background:eq:bg-commutator`). -/
theorem commutator_inner (q : Torus n → ℝ) (hq : IsSmoothPeriodic q)
    (is : List (Fin n)) (u : PeriodicSobolevSpace n F (is.length - 1))
    (φ : Torus n → F) (hφ : IsSmoothPeriodic φ) :
    ⟪commutator q hq is u, toL2 0 (ofSmooth 0 φ hφ)⟫ =
      (-1 : ℝ) ^ is.length *
        (⟪multiplication q hq.1 (toL2 _ u),
            toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is.reverse φ)
              (hφ.coordinateDerivList is.reverse))⟫ -
          ⟪toL2 _ u, toL2 0 (ofSmooth 0
            (periodicCoordinateDerivList is.reverse (fun x ↦ q x • φ x))
            ((smooth_smul hq hφ).coordinateDerivList is.reverse))⟫) := by
  refine (denseRange_ofSmooth (n := n) (F := F) (is.length - 1)).induction_on u ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · rintro ⟨f, hf⟩
    rw [commutator_ofSmooth, inner_sub_left, multiplication_inner,
      multiplication_ofSmooth hq hφ 0 0,
      smooth_derivative_inner is _ φ (smooth_smul hq hf) hφ (is.length - 1),
      smooth_derivative_inner is f _ hf (smooth_smul hq hφ) (is.length - 1),
      multiplication_ofSmooth hq hf (is.length - 1) (is.length - 1)]
    ring

/-- Literal distributional identity for `[D^is,M_q]` on every `H^(s-1)`
field. In particular no top derivative of the datum is required to be in L²
(`app:ch_background:eq:bg-commutator`; `app:ch_background:prop:bg-inverse`). -/
theorem commutator_distribution (q : Torus n → ℝ) (hq : IsSmoothPeriodic q)
    (is : List (Fin n)) (u : PeriodicSobolevSpace n F (is.length - 1))
    (φ : Torus n → F) (hφ : IsSmoothPeriodic φ) :
    (∫ x, ⟪commutator q hq is u x, φ x⟫) =
      (-1 : ℝ) ^ is.length *
        ((∫ x, ⟪multiplication q hq.1 (toL2 _ u) x,
            periodicCoordinateDerivList is.reverse φ x⟫) -
          ∫ x, ⟪toL2 _ u x,
            periodicCoordinateDerivList is.reverse (fun y ↦ q y • φ y) x⟫) := by
  simpa only [inner_periodicL2_ofSmooth] using commutator_inner q hq is u φ hφ

/-- The exterior normal coefficient has the same bounded commutator on every
datum, uniformly in the ordered derivative word
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_exterior_commutator_le (χ : Torus n → ℝ) (hχ : IsSmoothPeriodic χ)
    (is : List (Fin n)) (u : PeriodicSobolevSpace n F (is.length - 1)) :
    ‖commutator (fun x ↦ (1 - χ x) ^ 2) (smooth_exteriorCoefficient hχ) is u‖ ≤
      commutatorConstant (F := F) (fun x ↦ (1 - χ x) ^ 2)
        (smooth_exteriorCoefficient hχ) is.length * ‖u‖ :=
  norm_commutator_le _ _ is u

end JanetCartan.ContinuumCommutator.Exterior
