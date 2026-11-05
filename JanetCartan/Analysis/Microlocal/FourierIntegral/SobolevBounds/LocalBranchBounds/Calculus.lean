module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.BranchBounds
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer

/-!
# Local joint calculus for graph primitive expansions

Only neighborhoods in the original physical `(x,y,η)` coordinates are used.
Consumer: the local branch bounds for `app:ch_regular_base:eq:fio-input`.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local

/-- Joint physical points in the original coordinate order.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
abbrev Point (n : ℕ) := (Euclidean n × Euclidean n) × Euclidean n

/-- Evaluate a curried field at a joint physical point, retaining both masks.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def uncurry {n : ℕ} {E : Type*} (f : Field n E) (p : Point n) : E := f p.1.1 p.1.2 p.2

variable {n r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Slot differentiability at a physical point, for the local Leibniz rule
in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
def SliceDifferentiableAt (f : Field n E) (p : Point n) : Prop :=
  ∀ c, DifferentiableAt ℝ (slice c f p.1.1 p.1.2 p.2) (anchor c p.1.1 p.1.2 p.2)

/-- Joint smoothness at a point is preserved by an actual coordinate derivative.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem contDiffAt_derivative {f : Field n E} {p : Point n}
    (h : ContDiffAt ℝ ∞ (uncurry f) p) (c : Coordinate n) :
    ContDiffAt ℝ ∞ (uncurry (derivative c f)) p := by
  rcases c with ⟨c, i⟩
  cases c with
  | left =>
    have hh := h.comp (p, p.1.1)
      ((contDiffAt_snd.prodMk contDiffAt_fst.fst.snd).prodMk contDiffAt_fst.snd)
    exact (hh.fderiv contDiffAt_fst.fst (by simp)).clm_apply contDiffAt_const
  | right =>
    have hh := h.comp (p, p.1.2)
      ((contDiffAt_fst.fst.fst.prodMk contDiffAt_snd).prodMk contDiffAt_fst.snd)
    exact (hh.fderiv contDiffAt_fst.snd (by simp)).clm_apply contDiffAt_const
  | covector =>
    have hh := h.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    exact (hh.fderiv contDiffAt_snd (by simp)).clm_apply contDiffAt_const

/-- Actual joint jets inherit local primitive regularity; no global extension
of homogeneous coefficients is required. Source: Step 3 of the actual calculus.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem contDiffAt_jet {f : Field n E} {p : Point n}
    (h : ContDiffAt ℝ ∞ (uncurry f) p) (w : List (Coordinate n)) :
    ContDiffAt ℝ ∞ (uncurry (jet w f)) p := by
  induction w with
  | nil => exact h
  | cons c w ih => exact contDiffAt_derivative ih c

/-- Local joint regularity supplies each slice derivative in the product rule.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem sliceDifferentiableAt_of_contDiffAt {f : Field n E} {p : Point n}
    (h : ContDiffAt ℝ ∞ (uncurry f) p) : SliceDifferentiableAt f p := by
  intro c
  cases c with
  | left => exact (h.comp p.1.1
      ((contDiffAt_id.prodMk contDiffAt_const).prodMk contDiffAt_const)).differentiableAt (by simp)
  | right => exact (h.comp p.1.2
      ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt (by simp)
  | covector => exact (h.comp p.2
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)

/-- Locality of the actual partial derivative, with all spectator slots kept.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem derivative_congr {f g : Field n E} {p : Point n}
    (h : uncurry f =ᶠ[𝓝 p] uncurry g) (c : Coordinate n) :
    uncurry (derivative c f) p = uncurry (derivative c g) p := by
  have he : slice c.1 f p.1.1 p.1.2 p.2 =ᶠ[𝓝 (anchor c.1 p.1.1 p.1.2 p.2)]
      slice c.1 g p.1.1 p.1.2 p.2 := by
    rcases c with ⟨c, i⟩
    cases c with
    | left =>
      exact h.comp_tendsto
        (((continuous_id.prodMk continuous_const).prodMk continuous_const).tendsto p.1.1)
    | right =>
      exact h.comp_tendsto
        (((continuous_const.prodMk continuous_id).prodMk continuous_const).tendsto p.1.2)
    | covector => exact h.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto p.2)
  exact congrArg (fun L : Euclidean n →L[ℝ] E => L (EuclideanSpace.single c.2 1))
    (he.fderiv_eq (𝕜 := ℝ))

/-- Equality on an open neighborhood can be differentiated without extending
its coefficients. Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem derivative_eqOn {U : Set (Point n)} (hU : IsOpen U) {f g : Field n E}
    (h : Set.EqOn (uncurry f) (uncurry g) U) (c : Coordinate n) :
    Set.EqOn (uncurry (derivative c f)) (uncurry (derivative c g)) U := by
  intro p hp
  exact derivative_congr (Filter.eventuallyEq_of_mem (hU.mem_nhds hp) h) c

/-- Local addition rule used by the finite primitive expansion in Step 3.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem derivative_add_at (c : Coordinate n) {f g : Field n E} {p : Point n}
    (hf : SliceDifferentiableAt f p) (hg : SliceDifferentiableAt g p) :
    uncurry (derivative c (f + g)) p =
      uncurry (derivative c f + derivative c g) p := by
  simp [uncurry, derivative, partialDeriv, fderiv_add (hf c.1) (hg c.1)]

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- Local Leibniz rule retains derivatives of the actual inverse in Step 3.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem derivative_multiply_at (c : Coordinate n) {f : Field n ℂ} {g : Field n E}
    {p : Point n} (hf : SliceDifferentiableAt f p) (hg : SliceDifferentiableAt g p) :
    uncurry (derivative c (multiply f g)) p =
      uncurry (multiply (derivative c f) g + multiply f (derivative c g)) p := by
  have hs : slice c.1 f p.1.1 p.1.2 p.2 (anchor c.1 p.1.1 p.1.2 p.2) = uncurry f p := by
    cases c.1 <;> rfl
  have ht : slice c.1 g p.1.1 p.1.2 p.2 (anchor c.1 p.1.1 p.1.2 p.2) = uncurry g p := by
    cases c.1 <;> rfl
  have hd := congrArg (fun L : Euclidean n →L[ℝ] E => L (EuclideanSpace.single c.2 1))
    (fderiv_fun_smul (hf c.1) (hg c.1))
  simpa only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, hs, ht,
    derivative, partialDeriv, slice_multiply, multiply, Pi.add_apply, Pi.smul_apply,
    Pi.smul_def, add_comm, uncurry] using hd

end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local
