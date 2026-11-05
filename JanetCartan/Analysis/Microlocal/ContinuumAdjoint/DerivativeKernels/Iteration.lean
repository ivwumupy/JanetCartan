module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Iteration.Weak

/-!
# Ordered initial and carrier derivatives of the chart adjoint

For `app:ch_background:prop:bg-adjoint`, every ordered word of the actual
Fourier-side derivatives equals the finite, constructed amplitude expansion.
The hypotheses are joint smoothness, a common compact measurement support, and
the two exact phase identities of `app:ch_background:eq:bg-derivative-trade`
on that support. All integral interchanges and support preservation are proved.
The datum derivative count is `dataDerivatives_length_le_expansion`.

This is a chart-level result. Identifying the chart integral with the literal
torus adjoint and identifying physical initial derivatives by Fourier inversion
remain the responsibility of the parent construction.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow AmplitudeBound NormalComparison
variable {n : ℕ}

/-- Ordered actual derivatives in `app:ch_background:prop:bg-adjoint`.
The leftmost letter acts last, as in the published amplitude recursion. -/
def applyInitialCarrierDerivativeList : List (InitialCarrierDerivative n) →
    (CarrierVariable n → ℂ) → CarrierVariable n → ℂ
  | [], f => f
  | d :: ds, f => applyInitialCarrierDerivative d (applyInitialCarrierDerivativeList ds f)

/-- Every ordered actual derivative is smooth in the carrier variable on
smooth data (`app:ch_background:prop:bg-adjoint`). -/
theorem contDiff_applyInitialCarrierDerivativeList
    {f : CarrierVariable n → ℂ}
    (hf : ∀ η, ContDiff ℝ ∞ (fun z ↦ f (z, η)))
    (ds : List (InitialCarrierDerivative n)) (η : Euclidean (n - 1)) :
    ContDiff ℝ ∞ (fun z ↦ applyInitialCarrierDerivativeList ds f (z, η)) := by
  induction ds with
  | nil => exact hf η
  | cons d ds ih =>
    cases d with
    | initial h =>
      simpa only [applyInitialCarrierDerivativeList, applyInitialCarrierDerivative] using
        (contDiff_const (c := Complex.I * (inner ℝ h η : ℂ))).mul ih
    | carrier h => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

private theorem contDiff_list_sum_realize
    {S : Set (Euclidean n)} (hS : IsCompact S) (ts : List (AdjointDerivativeTerm n))
    (ha : ∀ t ∈ ts, SmoothSupportedAdjointAmplitude S t.amplitude)
    {Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ}
    (hΦ : ∀ η, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ Φ p.1 p.2 η))
    {v : Euclidean n → ℂ} (hv : ContDiff ℝ ∞ v) (η : Euclidean (n - 1)) :
    ContDiff ℝ ∞ (fun z ↦ (ts.map (fun t ↦ t.realize Φ v (z, η))).sum) := by
  induction ts with
  | nil => exact contDiff_const
  | cons t ts ih =>
    exact (contDiff_chartAdjoint_carrier hS (ha t (by simp)) hΦ
      (contDiff_euclideanCoordinateDerivList hv _) η).add
      (ih (fun q hq ↦ ha q (List.mem_cons_of_mem t hq)))

/-- Actual derivatives commute with the finite sum of realized terms because
each carrier section is smooth (`app:ch_background:prop:bg-adjoint`). -/
theorem applyInitialCarrierDerivative_sum_realize
    {S : Set (Euclidean n)} (hS : IsCompact S) (ts : List (AdjointDerivativeTerm n))
    (ha : ∀ t ∈ ts, SmoothSupportedAdjointAmplitude S t.amplitude)
    {Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ}
    (hΦ : ∀ η, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ Φ p.1 p.2 η))
    {v : Euclidean n → ℂ} (hv : ContDiff ℝ ∞ v)
    (d : InitialCarrierDerivative n) (u : CarrierVariable n) :
    applyInitialCarrierDerivative d (fun w ↦ (ts.map (fun t ↦ t.realize Φ v w)).sum) u =
      (ts.map (fun t ↦ applyInitialCarrierDerivative d (t.realize Φ v) u)).sum := by
  induction ts with
  | nil => cases d <;> simp [applyInitialCarrierDerivative]
  | cons t ts ih =>
    have ht : DifferentiableAt ℝ (fun z ↦ t.realize Φ v (z, u.2)) u.1 :=
      (contDiff_chartAdjoint_carrier hS (ha t (by simp)) hΦ
      (contDiff_euclideanCoordinateDerivList hv t.dataDerivatives) u.2).differentiable
      (by simp) u.1
    have hs := (contDiff_list_sum_realize hS ts
      (fun q hq ↦ ha q (List.mem_cons_of_mem t hq)) hΦ hv u.2).differentiable
      (by simp) u.1
    have hi := ih (fun q hq ↦ ha q (List.mem_cons_of_mem t hq))
    cases d with
    | initial h =>
      simpa only [List.map_cons, List.sum_cons,
        applyInitialCarrierDerivative, mul_add] using congrArg
          (fun c ↦ (Complex.I * (inner ℝ h u.2 : ℂ)) * t.realize Φ v u + c) hi
    | carrier h =>
      simpa only [List.map_cons, List.sum_cons, applyInitialCarrierDerivative,
        fderiv_fun_add ht hs, add_apply] using congrArg
          (fun c ↦ fderiv ℝ (fun z ↦ t.realize Φ v (z, u.2)) u.1 h + c) hi

private theorem sum_map_flatMap {α β : Type*} (ts : List α) (g : α → List β) (f : β → ℂ) :
    ((ts.flatMap g).map f).sum = (ts.map (fun t ↦ ((g t).map f).sum)).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

/-- Every ordered word of actual Fourier-side initial/carrier derivatives of
the chart adjoint is the published finite amplitude expansion
(`app:ch_background:prop:bg-adjoint`). Initial letters multiply by `i⟪h,η⟫`;
carrier letters are actual Fréchet derivatives. No expansion identity or
interchange is assumed. -/
theorem applyInitialCarrierDerivativeList_chartAdjoint
    {S : Set (Euclidean n)} (hS : IsCompact S) {a : AdjointAmplitude n}
    (ha : SmoothSupportedAdjointAmplitude S a)
    {L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n}
    {V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n}
    (hL : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ L p.1 p.2 h))
    (hV : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ V p.1 p.2 h))
    {Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ}
    (hΦ : ∀ η, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ Φ p.1 p.2 η))
    (hphaseL : ∀ z x η h, x ∈ S → inner ℝ h η =
      fderiv ℝ (fun y ↦ Φ z y η) x (L z x h))
    (hphaseV : ∀ z x η h, x ∈ S → fderiv ℝ (fun w ↦ Φ w x η) z h =
      fderiv ℝ (fun y ↦ Φ z y η) x (V z x h))
    {v : Euclidean n → ℂ} (hv : ContDiff ℝ ∞ v)
    (ds : List (InitialCarrierDerivative n)) (u : CarrierVariable n) :
    applyInitialCarrierDerivativeList ds
      (fun w ↦ chartAdjoint (fun x ↦ Φ w.1 x w.2) (fun x ↦ a w.1 x w.2) v) u =
      ((adjointDerivativeExpansion L V ds a).map (fun t ↦ t.realize Φ v u)).sum := by
  induction ds generalizing u with
  | nil => simp [applyInitialCarrierDerivativeList, adjointDerivativeExpansion,
      AdjointDerivativeTerm.realize, euclideanCoordinateDerivList]
  | cons d ds ih =>
    have hreg := smoothSupported_adjointDerivativeExpansion hS.isClosed ha hL hV ds
    simp only [applyInitialCarrierDerivativeList]
    rw [show applyInitialCarrierDerivativeList ds
        (fun w ↦ chartAdjoint (fun x ↦ Φ w.1 x w.2) (fun x ↦ a w.1 x w.2) v) =
        fun w ↦ ((adjointDerivativeExpansion L V ds a).map
          (fun t ↦ t.realize Φ v w)).sum from funext ih]
    rw [applyInitialCarrierDerivative_sum_realize hS _ hreg hΦ hv,
      adjointDerivativeExpansion, sum_map_flatMap]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact applyInitialCarrierDerivative_realize hS (hreg t ht) hL hV hΦ hphaseL hphaseV hv d u

/-- Each constructed term has at most the word length of datum derivatives,
retains the original support, and defines a convergent integral. These are the
termwise inputs to the raw Sobolev estimate in
`app:ch_background:prop:bg-adjoint`. -/
theorem adjointDerivativeExpansion_term_properties
    {S : Set (Euclidean n)} (hS : IsCompact S) {a : AdjointAmplitude n}
    (ha : SmoothSupportedAdjointAmplitude S a)
    {L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n}
    {V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n}
    (hL : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ L p.1 p.2 h))
    (hV : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ V p.1 p.2 h))
    {Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ}
    (hΦ : ∀ η, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ Φ p.1 p.2 η))
    {v : Euclidean n → ℂ} (hv : ContDiff ℝ ∞ v)
    (ds : List (InitialCarrierDerivative n)) (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds a) :
    t.dataDerivatives.length ≤ ds.length ∧
      SmoothSupportedAdjointAmplitude S t.amplitude ∧
      ∀ u : CarrierVariable n, Integrable (fun x ↦
        oscillatoryFactor (-1) (Φ u.1 x u.2) *
          (t.amplitude u.1 x u.2 * euclideanCoordinateDerivList t.dataDerivatives v x)) := by
  have hreg := smoothSupported_adjointDerivativeExpansion hS.isClosed ha hL hV ds t ht
  exact ⟨dataDerivatives_length_le_expansion L V ds a t ht, hreg,
    integrable_realize_integrand hS hreg hΦ hv⟩

/-- On smooth test data the next carrier letter in every ordered word is also
its weak derivative with respect to the original product Lebesgue measure.
Together with `applyInitialCarrierDerivativeList_chartAdjoint` this gives the
weak interpretation of the constructed expansion
(`app:ch_background:prop:bg-adjoint`). -/
theorem weak_carrier_applyInitialCarrierDerivativeList_chartAdjoint
    {S : Set (Euclidean n)} (hS : IsCompact S) {a : AdjointAmplitude n}
    (ha : SmoothSupportedAdjointAmplitude S a)
    {Φ : CarrierParameter → Euclidean n → Euclidean (n - 1) → ℝ}
    (hΦ : ∀ η, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ Φ p.1 p.2 η))
    {v : Euclidean n → ℂ} (hv : ContDiff ℝ ∞ v)
    (ds : List (InitialCarrierDerivative n)) (η : Euclidean (n - 1))
    {ψ : CarrierParameter → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) (h : CarrierParameter) :
    let f : CarrierVariable n → ℂ := fun u ↦
      chartAdjoint (fun x ↦ Φ u.1 x u.2) (fun x ↦ a u.1 x u.2) v
    (∫ z, applyInitialCarrierDerivativeList (.carrier h :: ds) f (z, η) * ψ z
      ∂(volume.prod volume)) =
      -(∫ z, applyInitialCarrierDerivativeList ds f (z, η) * fderiv ℝ ψ z h
        ∂(volume.prod volume)) := by
  apply weak_carrier_applyInitialCarrierDerivative η _ hψ hs h
  exact contDiff_applyInitialCarrierDerivativeList
    (contDiff_chartAdjoint_carrier hS ha hΦ hv) ds η

/-- Each initial letter has the weak physical meaning of multiplication by
`i⟪h,η⟫`, including after any ordered word. This is the frequencywise weak
identity used in the parent's Fourier identification
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem weak_initial_applyInitialCarrierDerivativeList
    (f : CarrierVariable n → ℂ) (ds : List (InitialCarrierDerivative n))
    (z : CarrierParameter) (η h : Euclidean (n - 1))
    {ψ : Euclidean (n - 1) → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ) :
    (∫ y, Complex.exp (Complex.I * (inner ℝ y η : ℂ)) *
      applyInitialCarrierDerivativeList (.initial h :: ds) f (z, η) * ψ y) =
      -(∫ y, Complex.exp (Complex.I * (inner ℝ y η : ℂ)) *
        applyInitialCarrierDerivativeList ds f (z, η) * fderiv ℝ ψ y h) :=
  weak_initial_applyInitialCarrierDerivative (applyInitialCarrierDerivativeList ds f)
    z η h hψ hs

end JanetCartan.ContinuumAdjoint.DerivativeKernels
