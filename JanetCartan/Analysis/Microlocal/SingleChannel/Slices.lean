module

public import JanetCartan.Analysis.Microlocal.SingleChannel.Integral
public import JanetCartan.Analysis.Microlocal.SingleChannel.Normalization
public import JanetCartan.Analysis.Microlocal.NormalComparison.OperatorBounds

/-!
# The finite-component slice estimate

Uses the actual mask-free normal operator for `app:ch_osc:prop:osc-channel`.
The Euclidean component norm is the Frobenius norm when the components index
matrix entries. All components and both physical positions are retained.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace JanetCartan.SingleChannel
open NormalComparison
variable {d r : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℂ (Fin r)

/-- Passing from the normal theorem's finite Hilbert sum of scalar outputs
to the literal Euclidean-valued integral preserves squared norm exactly
(`app:ch_osc:prop:osc-channel`). -/
theorem integral_norm_sq_eq_sum_output (g : Y → V) (v : NormalOutputL2 d r)
    (q : ℝ) (h : ∀ i, (fun y ↦ g y i) =ᵐ[volume] fun y ↦ (q : ℂ) * v i y) :
    (∫ y, ‖g y‖ ^ 2) = q ^ 2 * ‖v‖ ^ 2 := by
  have he (i : Fin r) : (fun y ↦ ‖g y i‖ ^ 2) =ᵐ[volume]
      fun y ↦ q ^ 2 * ‖v i y‖ ^ 2 := by
    filter_upwards [h i] with y hy
    rw [hy, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hi (i : Fin r) : Integrable (fun y ↦ ‖g y i‖ ^ 2) :=
    (((Lp.memLp (v i)).integrable_norm_pow (by norm_num)).const_mul (q ^ 2)).congr
      (he i).symm
  simp_rw [EuclideanSpace.norm_sq_eq]
  rw [integral_finsetSum _ (fun i _ ↦ hi i), PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_congr_ae (he i), integral_const_mul, integral_norm_sq_eq_norm_sq]

/-- A slice inherits its uniform bound from the proved mask-free normal
estimate, with the exact extra half power of `K` in
`app:ch_osc:prop:osc-channel`. The constant is chosen before the slice data. -/
theorem exists_uniform_slice_energy_bound
    (G : UniformNormalGeometry d r) (C : ℕ → ℝ) :
    ∃ S > 0, ∀ F : UniformNormalData G C, ∀ ε ∈ Icc 0 G.ε₀, ∀ K > 0,
      ∀ (f : Lp ℂ 2 (volume.restrict G.D)) (g : Y → V),
        (∀ i, (fun y ↦ g y i) =ᵐ[volume] fun y ↦
          (Real.sqrt (K / (2 * Real.pi)) : ℂ) *
            (F.uniformOscillatoryOperator K ε f) i y) →
        (∫ y, ‖g y‖ ^ 2) ≤ (K / (2 * Real.pi)) * S ^ 2 * ‖f‖ ^ 2 := by
  obtain ⟨S, hS, hSb⟩ := G.exists_uniformOscillatoryOperator_bound C
  refine ⟨S, hS, ?_⟩
  intro F ε hε K hK f g hg
  rw [integral_norm_sq_eq_sum_output g _ _ hg, singleChannel_extraScale_sq hK.le]
  have h := (F.uniformOscillatoryOperator K ε).le_opNorm f
  have h' : ‖F.uniformOscillatoryOperator K ε f‖ ≤ S * ‖f‖ :=
    h.trans (mul_le_mul_of_nonneg_right (hSb F ε hε K hK) (norm_nonneg f))
  calc
    K / (2 * Real.pi) * ‖F.uniformOscillatoryOperator K ε f‖ ^ 2 ≤
        K / (2 * Real.pi) * (S * ‖f‖) ^ 2 := by
      gcongr
    _ = _ := by ring

end JanetCartan.SingleChannel
