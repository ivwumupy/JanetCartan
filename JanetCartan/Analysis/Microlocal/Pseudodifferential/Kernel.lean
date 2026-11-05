module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Actual integral kernels

The absolutely integrable kernel operations underlying
`app:ch_regular_base:thm:actual-calculus`. These apply, in particular, to frequency
regularizations of the amplitudes in that theorem. Integrability is explicit:
no assertion about an unregularized oscillatory integral is made here.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.Pseudodifferential

variable {X Y Z E F G : Type*}
  [MeasurableSpace Y] [MeasurableSpace Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `app:ch_regular_base:thm:actual-calculus`: the actual Bochner integral operator
of a kernel, including all physical masks in the kernel. -/
def kernelOperator (μ : Measure Y) (K : X → Y → E →L[ℝ] F) (u : Y → E) (x : X) : F :=
  ∫ y, K x y (u y) ∂μ

/-- `app:ch_regular_base:thm:actual-calculus`: composition integrates over the
intermediate physical position and preserves the order of the matrix factors. -/
def composeKernel (μ : Measure Y) (K : X → Y → F →L[ℝ] G)
    (L : Y → Z → E →L[ℝ] F) (x : X) (z : Z) : E →L[ℝ] G :=
  ∫ y, (K x y).comp (L y z) ∂μ

/-- `app:ch_regular_base:thm:actual-calculus`: Fubini proves the composition law
for actual integrals, under the indicated absolute integrability assumptions. -/
theorem kernelOperator_composeKernel (μ : Measure Y) (ν : Measure Z)
    [SFinite μ] [SFinite ν] [CompleteSpace F] [CompleteSpace G]
    (K : X → Y → F →L[ℝ] G)
    (L : Y → Z → E →L[ℝ] F) (u : Z → E) (x : X)
    (hL : ∀ y, Integrable (fun z ↦ L y z (u z)) ν)
    (hKL : ∀ z, Integrable (fun y ↦ (K x y).comp (L y z)) μ)
    (hint : Integrable (fun p : Y × Z ↦ K x p.1 (L p.1 p.2 (u p.2))) (μ.prod ν)) :
    kernelOperator ν (composeKernel μ K L) u x =
      kernelOperator μ K (kernelOperator ν L u) x := by
  simp only [kernelOperator, composeKernel]
  simp_rw [ContinuousLinearMap.integral_apply (hKL _) (u _),
    ContinuousLinearMap.comp_apply]
  rw [← integral_integral_swap hint]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦ (K x y).integral_comp_comm (hL y)

/-- `app:ch_regular_base:thm:actual-calculus`: a physical source multiplier stays
at the source position in the literal kernel. -/
theorem kernelOperator_source_mul (μ : Measure Y) (K : X → Y → E →L[ℝ] F)
    (b : Y → ℝ) (u : Y → E) (x : X) :
    kernelOperator μ K (fun y ↦ b y • u y) x =
      kernelOperator μ (fun x y ↦ b y • K x y) u x := by
  simp [kernelOperator]

/-- `app:ch_regular_base:thm:actual-calculus`: an output multiplier stays at the
output position in the literal kernel. -/
theorem kernelOperator_target_mul (μ : Measure Y) (K : X → Y → E →L[ℝ] F)
    (b : X → ℝ) (u : Y → E) (x : X) :
    kernelOperator μ (fun x y ↦ b x • K x y) u x =
      b x • kernelOperator μ K u x := by
  simp [kernelOperator, integral_smul]

/-- `app:ch_regular_base:thm:actual-calculus`: an elementary kernel estimate,
valid without assuming integrability of the vector-valued integrand. -/
theorem norm_kernelOperator_le (μ : Measure Y) (K : X → Y → E →L[ℝ] F)
    (u : Y → E) (x : X)
    (hint : Integrable (fun y ↦ ‖K x y‖ * ‖u y‖) μ) :
    ‖kernelOperator μ K u x‖ ≤ ∫ y, ‖K x y‖ * ‖u y‖ ∂μ := by
  exact norm_integral_le_of_norm_le hint
    (Filter.Eventually.of_forall fun y ↦ (K x y).le_opNorm (u y))

end JanetCartan.Pseudodifferential
