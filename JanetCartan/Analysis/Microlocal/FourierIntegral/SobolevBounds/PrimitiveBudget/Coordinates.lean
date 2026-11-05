module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.TransferAmplitudes
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Iteration

/-!
# Joint coordinates for full graph amplitudes

Physical coordinates for the primitive count in Step 3 of
`app:ch_regular_base:thm:actual-calculus`. The second position and the covector
are separate coordinates; the complete amplitude includes its masks.
-/

@[expose] public noncomputable section
namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget

/-- The three physical slots in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
inductive Slot where
  | left | right | covector
  deriving DecidableEq

/-- A physical coordinate, including both positions and the covector.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
abbrev Coordinate (n : ℕ) := Slot × Fin n

/-- Curried joint fields, in the original `(x,y,η)` order.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
abbrev Field (n : ℕ) (E : Type*) := Euclidean n → Euclidean n → Euclidean n → E

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Vary exactly one slot, as required by the joint primitive count in Step 3.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def slice (p : Slot) (f : Field n E) (x y η : Euclidean n) : Euclidean n → E :=
  match p with
  | .left => fun z => f z y η
  | .right => fun z => f x z η
  | .covector => fun z => f x y z

/-- The point of evaluation of a physical slice.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def anchor (p : Slot) (x y η : Euclidean n) : Euclidean n :=
  match p with
  | .left => x
  | .right => y
  | .covector => η

/-- Actual partial differentiation, with no change of covector normalization.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def derivative (c : Coordinate n) (f : Field n E) : Field n E :=
  fun x y η => partialDeriv (slice c.1 f x y η) (anchor c.1 x y η) c.2

/-- Ordered joint jets, using the existing outermost-first ordered action.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def jet (w : List (Coordinate n)) (f : Field n E) : Field n E :=
  Pseudodifferential.orderedTransferAction derivative w f

/-- Slice differentiability, used only to apply the actual product rule.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def SliceDifferentiable (f : Field n E) : Prop :=
  ∀ p x y η, DifferentiableAt ℝ (slice p f x y η) (anchor p x y η)

/-- Primitive smoothness input for Step 3. This asserts regularity of actual
ordered jets, not a branch expansion or a quantitative estimate.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def JetSmooth (f : Field n E) : Prop :=
  ∀ w, SliceDifferentiable (jet w f)

@[simp] theorem jet_nil (f : Field n E) : jet [] f = f := rfl
@[simp] theorem jet_cons (c : Coordinate n) (w : List (Coordinate n))
    (f : Field n E) : jet (c :: w) f = derivative c (jet w f) := rfl

/-- Explicit identification of the first physical position.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem derivative_left (i : Fin n) (f : Field n E) (x y η : Euclidean n) :
    derivative (.left, i) f x y η = partialDeriv (fun z => f z y η) x i := rfl

/-- Explicit identification of the second physical position.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem derivative_right (i : Fin n) (f : Field n E) (x y η : Euclidean n) :
    derivative (.right, i) f x y η = partialDeriv (fun z => f x z η) y i := rfl

/-- Explicit identification of the physical covector.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem derivative_covector (i : Fin n) (f : Field n E) (x y η : Euclidean n) :
    derivative (.covector, i) f x y η = partialDeriv (fun z => f x y z) η i := rfl

omit [NormedSpace ℝ E] in
@[simp] theorem slice_add (p : Slot) (f g : Field n E) (x y η : Euclidean n) :
    slice p (f + g) x y η = slice p f x y η + slice p g x y η := by cases p <;> rfl

omit [NormedSpace ℝ E] in
@[simp] theorem slice_zero (p : Slot) (x y η : Euclidean n) :
    slice p (0 : Field n E) x y η = 0 := by cases p <;> rfl

theorem SliceDifferentiable.zero : SliceDifferentiable (0 : Field n E) := by
  intro p x y η
  rw [slice_zero]
  exact differentiableAt_const _

theorem SliceDifferentiable.add {f g : Field n E}
    (hf : SliceDifferentiable f) (hg : SliceDifferentiable g) : SliceDifferentiable (f + g) := by
  intro p x y η
  rw [slice_add]
  exact (hf p x y η).add (hg p x y η)

@[simp] theorem derivative_zero (c : Coordinate n) : derivative c (0 : Field n E) = 0 := by
  funext x y η
  simp [derivative, partialDeriv]

theorem derivative_add (c : Coordinate n) {f g : Field n E}
    (hf : SliceDifferentiable f) (hg : SliceDifferentiable g) :
    derivative c (f + g) = derivative c f + derivative c g := by
  funext x y η
  simp [derivative, partialDeriv, fderiv_add (hf c.1 x y η) (hg c.1 x y η)]

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- Scalar multiplication of a whole full-amplitude field.
Source: Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
def multiply (f : Field n ℂ) (g : Field n E) : Field n E :=
  fun x y η => f x y η • g x y η

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
@[simp] theorem slice_multiply (p : Slot) (f : Field n ℂ) (g : Field n E)
    (x y η : Euclidean n) :
    slice p (multiply f g) x y η = fun z => slice p f x y η z • slice p g x y η z := by
  cases p <;> rfl

theorem SliceDifferentiable.multiply {f : Field n ℂ} {g : Field n E}
    (hf : SliceDifferentiable f) (hg : SliceDifferentiable g) :
    SliceDifferentiable (multiply f g) := by
  intro p x y η
  rw [slice_multiply]
  exact (hf p x y η).smul (hg p x y η)

/-- Actual Leibniz rule in any of the three slots; used for both graph branches
in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem derivative_multiply (c : Coordinate n) {f : Field n ℂ} {g : Field n E}
    (hf : SliceDifferentiable f) (hg : SliceDifferentiable g) :
    derivative c (multiply f g) =
      multiply (derivative c f) g + multiply f (derivative c g) := by
  funext x y η
  have hs : slice c.1 f x y η (anchor c.1 x y η) = f x y η := by cases c.1 <;> rfl
  have ht : slice c.1 g x y η (anchor c.1 x y η) = g x y η := by cases c.1 <;> rfl
  have hd := congrArg (fun L : Euclidean n →L[ℝ] E => L (EuclideanSpace.single c.2 1))
    (fderiv_fun_smul (hf c.1 x y η) (hg c.1 x y η))
  simpa only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, hs, ht, derivative, partialDeriv,
    slice_multiply, multiply, Pi.add_apply, Pi.smul_apply, Pi.smul_def, add_comm] using hd

end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget
