module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Mass.Poisson.Differentiation
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel.Mass.Poisson.Fourier

/-!
# Derivative periodization identity for the fixed cutoff

For `main:lem:smoothing` and `main:eq:smoothing-low`, the exact fixed Euclidean
kernel and all its real derivatives can be periodized and differentiated
term by term. The multidimensional Poisson identity identifies this
periodization with the finite Fourier kernel on the normalized unit torus.
-/

@[expose] public noncomputable section

open scoped SchwartzMap ContDiff

namespace JanetCartan

/-- `main:lem:smoothing`: the real part of the exact Euclidean cutoff,
bundled as a Schwartz function without changing its values. -/
def cutoffEuclideanKernelRealSchwartz (n : ℕ) (R : ℝ) (hR : R ≠ 0) :
    𝓢(EuclideanSpace ℝ (Fin n), ℝ) :=
  SchwartzMap.postcompCLM Complex.reCLM (cutoffEuclideanKernelSchwartz n R hR)

/-- `main:lem:smoothing`: the real Schwartz bundle preserves the fixed kernel. -/
@[simp] theorem cutoffEuclideanKernelRealSchwartz_apply (n : ℕ) (R : ℝ) (hR : R ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) :
    cutoffEuclideanKernelRealSchwartz n R hR x = (cutoffEuclideanKernel n R x).re := rfl

/-- `main:eq:smoothing-low`: absolute convergence of the derivative series
in the requested real multilinear codomain. -/
theorem summable_norm_iteratedFDeriv_re_cutoffEuclideanKernel_lattice
    (n j : ℕ) {R : ℝ} (hR : 0 < R) (x : EuclideanSpace ℝ (Fin n)) :
    Summable (fun k : Fin n → ℤ ↦
      ‖iteratedFDeriv ℝ j (fun z ↦ (cutoffEuclideanKernel n R z).re)
        (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))‖) :=
  summable_norm_iteratedFDeriv_schwartz_lattice
    (cutoffEuclideanKernelRealSchwartz n R hR.ne') j x

/-- `main:eq:smoothing-low`: convergence of the actual derivative series. -/
theorem summable_iteratedFDeriv_re_cutoffEuclideanKernel_lattice
    (n j : ℕ) {R : ℝ} (hR : 0 < R) (x : EuclideanSpace ℝ (Fin n)) :
    Summable (fun k : Fin n → ℤ ↦
      iteratedFDeriv ℝ j (fun z ↦ (cutoffEuclideanKernel n R z).re)
        (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))) :=
  (summable_norm_iteratedFDeriv_re_cutoffEuclideanKernel_lattice n j hR x).of_norm

/-- `main:eq:smoothing-low`: termwise differentiation of the fixed real
Euclidean kernel's periodization, with no additional analytic premises. -/
theorem iteratedFDeriv_tsum_re_cutoffEuclideanKernel
    (n j : ℕ) {R : ℝ} (hR : 0 < R) (x : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ j
      (fun y ↦ ∑' k : Fin n → ℤ,
        (cutoffEuclideanKernel n R (y + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))).re) x =
      ∑' k : Fin n → ℤ,
        iteratedFDeriv ℝ j (fun z ↦ (cutoffEuclideanKernel n R z).re)
          (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ))) :=
  iteratedFDeriv_schwartzLatticePeriodization
    (cutoffEuclideanKernelRealSchwartz n R hR.ne') j x

/-- `main:lem:smoothing`: the fixed real Euclidean cutoff periodizes to a
smooth function. -/
theorem contDiff_tsum_re_cutoffEuclideanKernel (n : ℕ) {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) ↦ ∑' k : Fin n → ℤ,
      (cutoffEuclideanKernel n R (y + WithLp.toLp 2 (fun i ↦ (k i : ℝ)))).re) :=
  contDiff_schwartzLatticePeriodization (cutoffEuclideanKernelRealSchwartz n R hR.ne')

/-- `main:eq:smoothing-low`: the kernel in the requested periodization
identity is precisely the derivative of the unshifted periodic lift. -/
theorem periodicCutoffDerivKernel_zero_neg_eq_iteratedFDeriv
    (n j : ℕ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    periodicCutoffDerivKernel j R 0 (-torusQuotient x) =
      iteratedFDeriv ℝ j (fun z ↦ periodicCutoffKernel R (torusQuotient z)) x := by
  have ht := periodicCutoffDerivKernel_translate (n := n) j R x 0
  rw [zero_sub] at ht
  rw [← ht, periodicCutoffDerivKernel_eq_iteratedFDeriv]
  simp only [sub_zero]

/-- `main:lem:smoothing`, `main:eq:smoothing-low`: every derivative of the exact
fixed periodic cutoff kernel is the absolutely convergent periodization of the
corresponding real Euclidean derivative, with the normalized unit lattice. -/
theorem periodicCutoffDerivKernel_eq_tsum_iteratedFDeriv_re_cutoffEuclideanKernel
    (n j : ℕ) {R : ℝ} (hR : 0 < R) (x : EuclideanSpace ℝ (Fin n)) :
    periodicCutoffDerivKernel j R 0 (-torusQuotient x) =
      ∑' k : Fin n → ℤ,
        iteratedFDeriv ℝ j (fun z ↦ (cutoffEuclideanKernel n R z).re)
          (x + WithLp.toLp 2 (fun i ↦ (k i : ℝ))) := by
  rw [periodicCutoffDerivKernel_zero_neg_eq_iteratedFDeriv,
    funext (periodicCutoffKernel_eq_tsum_re_cutoffEuclideanKernel n hR)]
  exact iteratedFDeriv_tsum_re_cutoffEuclideanKernel n j hR x

end JanetCartan
