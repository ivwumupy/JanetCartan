module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.SymbolBounds.RadialFactor
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Primitive expressions for the actual differentiated coefficients

For `app:ch_background:prop:bg-adjoint`, a coefficient expression records
products and derivatives of the original amplitude and the fields L,V. Its
degree counts total primitive differentiation, not the number of factors.
The expression is constructed from the actual branches, rather than supplied
as an extra hypothesis about generated amplitudes.
-/

@[expose] public noncomputable section
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow NormalComparison
variable {n : ℕ}

/-- Joint carrier/measurement variables for the primitive mixed jets in
`app:ch_background:prop:bg-adjoint`. -/
abbrev AdjointJetPoint (n : ℕ) := CarrierParameter × Euclidean n

/-- The real field component in one derivative trade
(`app:ch_background:eq:bg-derivative-trade`). -/
def branchField
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (d : InitialCarrierDerivative n) (j : Fin n) (p : AdjointJetPoint n) : ℂ :=
  match d with
  | .initial h => (L p.1 p.2 h j : ℝ)
  | .carrier h => (V p.1 p.2 h j : ℝ)

/-- A finite differential expression in the original normalized amplitude and
L,V. This contains no estimates (`app:ch_background:prop:bg-adjoint`). -/
inductive AdjointCoefficientExpression (n : ℕ) where
  | amplitude
  | field (d : InitialCarrierDerivative n) (j : Fin n)
  | add (e f : AdjointCoefficientExpression n)
  | neg (e : AdjointCoefficientExpression n)
  | mul (e f : AdjointCoefficientExpression n)
  | deriv (h : AdjointJetPoint n) (e : AdjointCoefficientExpression n)

namespace AdjointCoefficientExpression

/-- Only the finitely many directions in the derivative word are needed by
the coefficient estimate (`app:ch_background:prop:bg-adjoint`). -/
def UsesDirections (ds : List (InitialCarrierDerivative n)) :
    AdjointCoefficientExpression n → Prop
  | .amplitude => True
  | .field d _ => d ∈ ds
  | .add e f | .mul e f => e.UsesDirections ds ∧ f.UsesDirections ds
  | .neg e | .deriv _ e => e.UsesDirections ds

private theorem usesDirections_mono {ds es : List (InitialCarrierDerivative n)}
    (h : ∀ d ∈ ds, d ∈ es) (e : AdjointCoefficientExpression n)
    (he : e.UsesDirections ds) : e.UsesDirections es := by
  induction e with
  | amplitude => trivial
  | field d j => exact h d he
  | add e f ih₁ ih₂ | mul e f ih₁ ih₂ => exact ⟨ih₁ he.1, ih₂ he.2⟩
  | neg e ih | deriv h e ih => exact ih he

/-- Total primitive derivative excess, used in the `s-k` budget following
`app:ch_background:eq:bg-derivative-trade`. -/
def degree : AdjointCoefficientExpression n → ℕ
  | .amplitude | .field _ _ => 0
  | .add e f => max e.degree f.degree
  | .neg e => e.degree
  | .mul e f => e.degree + f.degree
  | .deriv _ e => e.degree + 1

/-- Evaluate in the actual primitive functions, retaining η as a parameter
(`app:ch_background:prop:bg-adjoint`). -/
def evaluate
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (a : AdjointAmplitude n) (η : Euclidean (n - 1)) :
    AdjointCoefficientExpression n → AdjointJetPoint n → ℂ
  | .amplitude => fun p ↦ a p.1 p.2 η
  | .field d j => branchField L V d j
  | .add e f => fun p ↦ e.evaluate L V a η p + f.evaluate L V a η p
  | .neg e => fun p ↦ -e.evaluate L V a η p
  | .mul e f => fun p ↦ e.evaluate L V a η p * f.evaluate L V a η p
  | .deriv h e => fun p ↦ fderiv ℝ (e.evaluate L V a η) p h

/-- Joint smoothness follows from smooth primitives, not generated-symbol
assumptions (`app:ch_background:prop:bg-adjoint`). -/
theorem contDiff_evaluate
    (L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n)
    (V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n)
    (a : AdjointAmplitude n) (η : Euclidean (n - 1))
    (ha : ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (e : AdjointCoefficientExpression n) : ContDiff ℝ ∞ (e.evaluate L V a η) := by
  induction e with
  | amplitude => exact ha
  | field d j => exact hfield d j
  | add e f he hf => exact he.add hf
  | neg e he => exact he.neg
  | mul e f he hf => exact he.mul hf
  | deriv h e he => exact (he.fderiv_right (by simp)).clm_apply contDiff_const

private theorem fderiv_slice_right (f : AdjointJetPoint n → ℂ)
    (hf : ContDiff ℝ ∞ f) (z : CarrierParameter) (x h : Euclidean n) :
    fderiv ℝ (fun y ↦ f (z, y)) x h = fderiv ℝ f (z, x) (0, h) := by
  have hd := (hf.differentiable (by simp) (z, x)).hasFDerivAt.comp x
    ((hasFDerivAt_const z x).prodMk (hasFDerivAt_id x))
  simpa [Function.comp_def] using congrArg (fun A : Euclidean n →L[ℝ] ℂ ↦ A h) hd.fderiv

private theorem fderiv_slice_left (f : AdjointJetPoint n → ℂ)
    (hf : ContDiff ℝ ∞ f) (z h : CarrierParameter) (x : Euclidean n) :
    fderiv ℝ (fun w ↦ f (w, x)) z h = fderiv ℝ f (z, x) (h, 0) := by
  have hi : HasFDerivAt (fun w : CarrierParameter ↦ (w, x))
      ((ContinuousLinearMap.id ℝ CarrierParameter).prod 0) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const x z)
  have hd := (hf.differentiable (by simp) (z, x)).hasFDerivAt.comp z hi
  simpa [Function.comp_def] using congrArg (fun A : CarrierParameter →L[ℝ] ℂ ↦ A h) hd.fderiv

/-- Finite addition of coefficient expressions, with an empty sum represented
by the difference of two equal primitives (`app:ch_background:prop:bg-adjoint`). -/
def sum : List (AdjointCoefficientExpression n) → AdjointCoefficientExpression n
  | [] => .add .amplitude (.neg .amplitude)
  | e :: es => .add e (sum es)

private theorem evaluate_sum (L V a η) (es : List (AdjointCoefficientExpression n))
    (p : AdjointJetPoint n) :
    (sum es).evaluate L V a η p = (es.map (fun e ↦ e.evaluate L V a η p)).sum := by
  induction es with
  | nil => simp [sum, evaluate]
  | cons e es ih => simp [sum, evaluate, ih]

private theorem degree_sum_le (es : List (AdjointCoefficientExpression n)) (b : ℕ)
    (h : ∀ e ∈ es, e.degree ≤ b) : (sum es).degree ≤ b := by
  induction es with
  | nil => simp [sum, degree]
  | cons e es ih =>
      exact max_le (h e (by simp)) (ih (fun f hf ↦ h f (by simp [hf])))

private theorem usesDirections_sum (ds : List (InitialCarrierDerivative n))
    (es : List (AdjointCoefficientExpression n))
    (h : ∀ e ∈ es, e.UsesDirections ds) : (sum es).UsesDirections ds := by
  induction es with
  | nil => exact ⟨trivial, trivial⟩
  | cons e es ih => exact ⟨h e (by simp), ih (fun f hf ↦ h f (by simp [hf]))⟩

/-- The divergence expression in the actual zero branch
(`app:ch_background:eq:bg-derivative-trade`). -/
def divergence (d : InitialCarrierDerivative n) (e : AdjointCoefficientExpression n) :
    AdjointCoefficientExpression n :=
  sum (List.ofFn (fun j : Fin n ↦
    .deriv (0, EuclideanSpace.single j 1) (.mul (.field d j) e)))

/-- Construct the zero branch directly in primitives
(`app:ch_background:eq:bg-derivative-trade`). -/
def zeroBranch (d : InitialCarrierDerivative n) (e : AdjointCoefficientExpression n) :
    AdjointCoefficientExpression n :=
  match d with
  | .initial _ => divergence d e
  | .carrier h => .add (.deriv (h, 0) e) (.neg (divergence d e))

/-- Construct a first branch directly in primitives
(`app:ch_background:eq:bg-derivative-trade`). -/
def firstBranch (d : InitialCarrierDerivative n) (e : AdjointCoefficientExpression n)
    (j : Fin n) : AdjointCoefficientExpression n :=
  match d with
  | .initial _ => .mul (.field d j) e
  | .carrier _ => .neg (.mul (.field d j) e)

/-- Branches use only their new direction and directions already present
(`app:ch_background:prop:bg-adjoint`). -/
theorem usesDirections_branches (ds : List (InitialCarrierDerivative n))
    (d : InitialCarrierDerivative n) (e : AdjointCoefficientExpression n)
    (he : e.UsesDirections ds) :
    (e.zeroBranch d).UsesDirections (d :: ds) ∧
      ∀ j, (e.firstBranch d j).UsesDirections (d :: ds) := by
  have he' := usesDirections_mono (fun v hv ↦ List.mem_cons_of_mem d hv) e he
  have hd : (divergence d e).UsesDirections (d :: ds) := by
    apply usesDirections_sum
    simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
    intro j
    exact ⟨by simp [UsesDirections], he'⟩
  cases d <;> simp only [zeroBranch, firstBranch, UsesDirections] at *
  · exact ⟨hd, fun _ ↦ ⟨by simp, he'⟩⟩
  · exact ⟨⟨he', hd⟩, fun _ ↦ ⟨by simp, he'⟩⟩

/-- A zero branch spends one primitive derivative
(`app:ch_background:prop:bg-adjoint`). -/
theorem degree_zeroBranch_le (d : InitialCarrierDerivative n)
    (e : AdjointCoefficientExpression n) : (zeroBranch d e).degree ≤ e.degree + 1 := by
  have hd : (divergence d e).degree ≤ e.degree + 1 := by
    apply degree_sum_le
    simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
    intro j
    simp [degree]
  cases d <;> simpa [zeroBranch, degree] using hd

/-- A first branch spends no primitive derivative; its derivative is on the
datum (`app:ch_background:prop:bg-adjoint`). -/
theorem degree_firstBranch (d : InitialCarrierDerivative n)
    (e : AdjointCoefficientExpression n) (j : Fin n) :
    (firstBranch d e j).degree = e.degree := by
  cases d <;> simp [firstBranch, degree]

/-- Exact equality with the published zero branch. The only assumptions are
smoothness of the primitive functions (`app:ch_background:prop:bg-adjoint`). -/
theorem evaluate_zeroBranch (L V a η)
    (ha : ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (d : InitialCarrierDerivative n) (e : AdjointCoefficientExpression n)
    (p : AdjointJetPoint n) :
    (zeroBranch d e).evaluate L V a η p =
      zeroBranchAmplitude L V d
        (fun z x ξ ↦ e.evaluate L V a ξ (z, x)) p.1 p.2 η := by
  have he := contDiff_evaluate L V a η ha hfield e
  have hd : (divergence d e).evaluate L V a η p =
      ∑ j, partialDeriv
        (fun x ↦ branchField L V d j (p.1, x) * e.evaluate L V a η (p.1, x)) p.2 j := by
    simp only [divergence, evaluate_sum, List.map_ofFn, List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro j _
    exact (fderiv_slice_right _ ((hfield d j).mul he) _ _ _).symm
  cases d with
  | initial h =>
      simpa [zeroBranch, zeroBranchAmplitude, initialZeroAmplitude, branchField] using hd
  | carrier h =>
      simp only [zeroBranch, evaluate, hd, zeroBranchAmplitude, carrierZeroAmplitude,
        transportCoefficient, branchField, ← fderiv_slice_left _ he]
      rfl

/-- Exact equality with each published first branch
(`app:ch_background:prop:bg-adjoint`). -/
theorem evaluate_firstBranch (L V a η) (d : InitialCarrierDerivative n)
    (e : AdjointCoefficientExpression n) (j : Fin n) (p : AdjointJetPoint n) :
    (firstBranch d e j).evaluate L V a η p =
      firstBranchAmplitude L V d
        (fun z x ξ ↦ e.evaluate L V a ξ (z, x)) j p.1 p.2 η := by
  cases d <;> simp [firstBranch, evaluate, firstBranchAmplitude,
    initialFirstAmplitude, carrierFirstAmplitude, branchField]

end AdjointCoefficientExpression

/-- Every actual term has a primitive expression of derivative excess at most
`s-k`. This is the coefficient budget following
`app:ch_background:eq:bg-derivative-trade`, before the fixed symbol reserve. -/
theorem exists_expression_of_mem_adjointDerivativeExpansion (L V)
    (a : AdjointAmplitude n)
    (ha : ∀ η, ContDiff ℝ ∞ (fun p : AdjointJetPoint n ↦ a p.1 p.2 η))
    (hfield : ∀ d j, ContDiff ℝ ∞ (branchField L V d j))
    (ds : List (InitialCarrierDerivative n)) (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds a) :
    ∃ e : AdjointCoefficientExpression n,
      e.degree + t.dataDerivatives.length ≤ ds.length ∧
      e.UsesDirections ds ∧
      t.amplitude = fun z x η ↦ e.evaluate L V a η (z, x) := by
  induction ds generalizing t with
  | nil =>
      simp only [adjointDerivativeExpansion, List.mem_singleton] at ht
      subst t
      exact ⟨.amplitude, by simp [AdjointCoefficientExpression.degree], trivial, rfl⟩
  | cons d ds ih =>
      obtain ⟨u, hu, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨e, he, hdirs, hue⟩ := ih u hu
      simp only [differentiateAdjointTerm, List.mem_cons, List.mem_ofFn] at ht
      rcases ht with rfl | ⟨j, rfl⟩
      · refine ⟨e.zeroBranch d, ?_, (e.usesDirections_branches ds d hdirs).1, ?_⟩
        · have := e.degree_zeroBranch_le d
          simp only [List.length_cons]
          omega
        · dsimp only
          rw [hue]
          funext z x η
          exact (e.evaluate_zeroBranch L V a η (ha η) hfield d (z, x)).symm
      · refine ⟨e.firstBranch d j, ?_, (e.usesDirections_branches ds d hdirs).2 j, ?_⟩
        · simp only [AdjointCoefficientExpression.degree_firstBranch, List.length_cons]
          omega
        · dsimp only
          rw [hue]
          funext z x η
          exact (e.evaluate_firstBranch L V a η d j (z, x)).symm

end JanetCartan.ContinuumAdjoint.DerivativeKernels
