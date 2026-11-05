module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Mass.Poisson.Summability

/-!
# Differentiating Schwartz periodizations

The locally summable majorants justify differentiation at every order for
`main:lem:smoothing` and `main:eq:smoothing-low`. No convergence or
differentiation hypotheses are imposed on the fixed cutoff.
-/

@[expose] public noncomputable section

open scoped SchwartzMap ContDiff

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- `main:eq:smoothing-low`: the derivative of a periodized Schwartz jet is
its periodized derivative, with convergence in operator norm. -/
theorem hasFDerivAt_tsum_iteratedFDeriv_schwartz_lattice
    (f : 𝓢(EuclideanSpace ℝ (Fin n), F)) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt
      (fun y ↦ ∑' k : Fin n → ℤ,
        iteratedFDeriv ℝ j f (y + WithLp.toLp 2 (fun i ↦ (k i : ℝ))))
      (∑' k : Fin n → ℤ, fderiv ℝ (iteratedFDeriv ℝ j f)
        (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))) x := by
  obtain ⟨u, hu, hb⟩ := exists_summable_bound_iteratedFDeriv_schwartz_lattice f (j + 1)
    (show 0 ≤ ‖x‖ + 1 by positivity)
  have hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (‖x‖ + 1) := by
    simp only [Metric.mem_ball, dist_zero_right]; linarith
  refine hasFDerivAt_tsum_of_isPreconnected (𝕜 := ℝ)
    (f' := fun k y ↦ fderiv ℝ (iteratedFDeriv ℝ j f)
      (y + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))) hu Metric.isOpen_ball
    (convex_ball (0 : EuclideanSpace ℝ (Fin n)) (‖x‖ + 1)).isPreconnected
    (fun k y _ ↦ ?_) (fun k y hy ↦ ?_) hx
    (summable_iteratedFDeriv_schwartz_lattice f j x) hx
  · rw [hasFDerivAt_comp_add_right]
    exact ((f.smooth ⊤).differentiable_iteratedFDeriv (m := j)
      (by exact_mod_cast ENat.natCast_lt_top j) _).hasFDerivAt
  · rw [fderiv_iteratedFDeriv, Function.comp_apply, LinearIsometryEquiv.norm_map]
    exact hb k y (le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hy))

/-- `main:eq:smoothing-low`: iterated Fréchet derivatives commute with
periodization of every Schwartz function on Euclidean space. -/
theorem iteratedFDeriv_schwartzLatticePeriodization
    (f : 𝓢(EuclideanSpace ℝ (Fin n), F)) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ j (schwartzLatticePeriodization f) x =
      ∑' k : Fin n → ℤ,
        iteratedFDeriv ℝ j f (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ))) := by
  induction j generalizing x with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, schwartzLatticePeriodization, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin n)) F).symm.toContinuousLinearEquiv.map_tsum
  | succ j ih =>
    have heq : iteratedFDeriv ℝ j (schwartzLatticePeriodization f) =
        fun y ↦ ∑' k : Fin n → ℤ,
          iteratedFDeriv ℝ j f (y + WithLp.toLp 2 (fun i ↦ (k i : ℝ))) := funext ih
    rw [iteratedFDeriv_succ_eq_comp_left, heq, Function.comp_apply,
      (hasFDerivAt_tsum_iteratedFDeriv_schwartz_lattice f j x).fderiv]
    calc
      _ = ∑' k : Fin n → ℤ,
          (continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (j + 1) ↦ EuclideanSpace ℝ (Fin n)) F).symm
            (fderiv ℝ (iteratedFDeriv ℝ j f)
              (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))) :=
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (j + 1) ↦ EuclideanSpace ℝ (Fin n)) F).symm.toContinuousLinearEquiv.map_tsum
      _ = _ := tsum_congr fun k ↦ congrFun iteratedFDeriv_succ_eq_comp_left.symm _

/-- `main:lem:smoothing`: the lattice periodization of a Schwartz function
is smooth, in every finite dimension. -/
theorem contDiff_schwartzLatticePeriodization
    (f : 𝓢(EuclideanSpace ℝ (Fin n), F)) :
    ContDiff ℝ ∞ (schwartzLatticePeriodization f) := by
  rw [contDiff_iff_continuous_differentiable]
  constructor
  · intro j _
    have heq := funext (iteratedFDeriv_schwartzLatticePeriodization f j)
    rw [heq]
    exact continuous_tsum_iteratedFDeriv_schwartz_lattice f j
  · intro j _
    have heq := funext (iteratedFDeriv_schwartzLatticePeriodization f j)
    rw [heq]
    exact fun x ↦ (hasFDerivAt_tsum_iteratedFDeriv_schwartz_lattice f j x).differentiableAt

end JanetCartan
