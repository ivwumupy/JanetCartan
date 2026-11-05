module

public import JanetCartan.Analysis.Approximation.BallSmoothing.Unit
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Real linearity on smooth closed-ball data

The domain of the operator in `app:ch_regular_base:lem:ball-extension`
consists of representatives smooth at every point of the original closed
ball. Exterior values have no effect, by `unitSmoothing_congr_closedBall`.
Integrability of their zero extensions proves addition for the actual
Bochner integrals; no linearity assertion on arbitrary nonintegrable
functions is used. Continuous real linear target maps commute with the
construction, giving its componentwise vector and tensor action.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Metric ContinuousLinearMap
open scoped ContDiff Convolution

namespace JanetCartan.BallSmoothing

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smooth-up-to-boundary representatives of closed-ball data, with no
exterior regularity or bounds required. The smoother is proved independent
of the representative outside the ball
(`app:ch_regular_base:lem:ball-extension`). -/
def smoothClosedBallData (c : E) (a : ℝ) : Submodule ℝ (E → F) where
  carrier := {f | ∀ x ∈ closedBall c a, ContDiffAt ℝ ∞ f x}
  zero_mem' := fun _ _ ↦ contDiffAt_const
  add_mem' := fun hf hg x hx ↦ (hf x hx).add (hg x hx)
  smul_mem' := fun r _ hf x hx ↦ (hf x hx).const_smul r

/-- Valid input representatives are continuous on the original closed
ball (`app:ch_regular_base:lem:ball-extension`). -/
theorem smoothClosedBallData_continuousOn {c : E} {a : ℝ}
    (f : smoothClosedBallData (F := F) c a) : ContinuousOn (f : E → F) (closedBall c a) :=
  fun x hx ↦ (f.property x hx).continuousAt.continuousWithinAt

omit [NormedSpace ℝ F] in
private theorem reflectedInput_add (R : ℝ) (j : ℕ) (f g : E → F) :
    reflectedInput R j (f + g) = reflectedInput R j f + reflectedInput R j g := by
  funext z
  by_cases hz : (-(j : ℝ) / R) • z ∈ closedBall (0 : E) 1
  · simp only [reflectedInput, inputExtension, indicator_of_mem hz, Pi.add_apply]
  · simp only [reflectedInput, inputExtension, indicator_of_notMem hz, Pi.add_apply, add_zero]

private theorem reflectedInput_smul (R : ℝ) (j : ℕ) (a : ℝ) (f : E → F) :
    reflectedInput R j (a • f) = a • reflectedInput R j f := by
  funext z
  by_cases hz : (-(j : ℝ) / R) • z ∈ closedBall (0 : E) 1
  · simp only [reflectedInput, inputExtension, indicator_of_mem hz, Pi.smul_apply]
  · simp only [reflectedInput, inputExtension, indicator_of_notMem hz, Pi.smul_apply, smul_zero]

/-- Actual addition for inward smoothing on continuous closed-ball
representatives (`app:ch_regular_base:lem:ball-extension`). -/
theorem unitSmoothing_add {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : (2 : ℝ) * m ≤ R) {f g : E → F}
    (hf : ContinuousOn f (closedBall 0 1)) (hg : ContinuousOn g (closedBall 0 1)) :
    unitSmoothing R m (f + g) = unitSmoothing R m f + unitSmoothing R m g := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hR0 : R ≠ 0 := ne_of_gt (by linarith)
  have hreg j (hj : j ∈ Finset.Icc 1 m) (x : E) :
      regularizedAverage (kernel n) R j (f + g) x =
        regularizedAverage (kernel n) R j f x + regularizedAverage (kernel n) R j g x := by
    have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
    have hfc := hasCompactSupport_kernel.convolutionExists_left (lsmul ℝ ℝ)
      contDiff_kernel.continuous (integrable_reflectedInput hR0 hj0 hf).locallyIntegrable
    have hgc := hasCompactSupport_kernel.convolutionExists_left (lsmul ℝ ℝ)
      contDiff_kernel.continuous (integrable_reflectedInput hR0 hj0 hg).locallyIntegrable
    simp only [regularizedAverage, reflectedInput_add]
    exact (hfc _).distrib_add (hgc _)
  rw [unitSmoothing_eq_regularized hm hR (f + g), unitSmoothing_eq_regularized hm hR f,
    unitSmoothing_eq_regularized hm hR g]
  funext x
  simp only [Pi.add_apply]
  have hs : (∑ j ∈ Finset.Icc 1 m, coefficient m j • regularizedAverage (kernel n) R j (f + g) x) =
      (∑ j ∈ Finset.Icc 1 m, coefficient m j • regularizedAverage (kernel n) R j f x) +
        ∑ j ∈ Finset.Icc 1 m, coefficient m j • regularizedAverage (kernel n) R j g x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j hj ↦ by rw [hreg j hj x, smul_add]
  rw [hs, smul_add]

/-- Actual real homogeneity for the same inward smoother
(`app:ch_regular_base:lem:ball-extension`). -/
theorem unitSmoothing_smul {m : ℕ} (hm : 1 ≤ m) {R : ℝ}
    (hR : (2 : ℝ) * m ≤ R) (a : ℝ) (f : E → F) :
    unitSmoothing R m (a • f) = a • unitSmoothing R m f := by
  rw [unitSmoothing_eq_regularized hm hR (a • f), unitSmoothing_eq_regularized hm hR f]
  have hreg j x : regularizedAverage (kernel n) R j (a • f) x =
      a • regularizedAverage (kernel n) R j f x := by
    simp only [regularizedAverage, reflectedInput_smul, convolution_smul, Pi.smul_apply]
  funext x
  simp only [Pi.smul_apply, hreg]
  simp_rw [smul_comm (coefficient m _) a]
  rw [← Finset.smul_sum, smul_comm]

/-- The genuine real linear operator on smooth closed-ball data.
Global smoothness and fixed compact support of every value are the checked
properties `contDiff_unitSmoothing` and `unitSmoothing_hasCompactSupport`
(`app:ch_regular_base:lem:ball-extension`). -/
def unitSmoothingLinear {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : (2 : ℝ) * m ≤ R) :
    smoothClosedBallData (F := F) (0 : E) 1 →ₗ[ℝ] (E → F) where
  toFun f := unitSmoothing R m (f : E → F)
  map_add' f g := unitSmoothing_add hm hR
    (smoothClosedBallData_continuousOn f) (smoothClosedBallData_continuousOn g)
  map_smul' a f := unitSmoothing_smul hm hR a (f : E → F)

/-- Every continuous real linear target map commutes with the literal
smoother. In particular, the same real scalar operator acts on each vector
or tensor coordinate in `main:lem:smoothing`. -/
theorem unitSmoothing_map [CompleteSpace F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (L : F →L[ℝ] G) {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : (2 : ℝ) * m ≤ R)
    {f : E → F} (hf : ContinuousOn f (closedBall 0 1)) :
    unitSmoothing R m (fun x ↦ L (f x)) = fun x ↦ L (unitSmoothing R m f x) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hR0 : R ≠ 0 := ne_of_gt (by linarith)
  have href j : reflectedInput R j (fun x ↦ L (f x)) = fun z ↦ L (reflectedInput R j f z) := by
    funext z
    by_cases hz : (-(j : ℝ) / R) • z ∈ closedBall (0 : E) 1
    · simp only [reflectedInput, inputExtension, indicator_of_mem hz]
    · simp only [reflectedInput, inputExtension, indicator_of_notMem hz, map_zero]
  have hreg j (hj : j ∈ Finset.Icc 1 m) (x : E) :
      regularizedAverage (kernel n) R j (fun z ↦ L (f z)) x =
        L (regularizedAverage (kernel n) R j f x) := by
    have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
    have hfc := hasCompactSupport_kernel.convolutionExists_left (lsmul ℝ ℝ)
      contDiff_kernel.continuous (integrable_reflectedInput hR0 hj0 hf).locallyIntegrable
    have hi : Integrable (fun t ↦ kernel n t •
        reflectedInput R j f ((1 - R / (j : ℝ)) • x - t)) := hfc _
    simp only [regularizedAverage, href, convolution, lsmul_apply]
    simpa only [map_smul] using L.integral_comp_comm hi
  rw [unitSmoothing_eq_regularized hm hR (fun x ↦ L (f x)), unitSmoothing_eq_regularized hm hR f]
  funext x
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, hreg j hj x]

end JanetCartan.BallSmoothing
