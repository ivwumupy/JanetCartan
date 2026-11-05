module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FirstOutputBounds.WeightedJets

/-!
# Primitive jets of the literal adjoint's first output amplitude

Original `(x,y,η)` coordinates, conjugate-transposed full amplitudes and the
Frobenius norm in the gain-one paragraph of Step 3 of
`app:ch_regular_base:thm:actual-calculus`.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FirstOutputJets
open FullAmplitudePrimitiveBudget
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "M" => Matrix (Fin r) (Fin r) ℂ

private theorem derivative_conjTranspose (c : Coordinate n) (A : FullAmplitude n r) :
    derivative c (fun x y η ↦ (A x y η).conjTranspose) =
      fun x y η ↦ (derivative c A x y η).conjTranspose := by
  funext x y η
  have h := congrArg (fun D : E →L[ℝ] M ↦ D (EuclideanSpace.single c.2 1))
    ((starL ℝ : M ≃L[ℝ] M).comp_fderiv (f := slice c.1 A x y η) (x := anchor c.1 x y η))
  rcases c with ⟨p, j⟩
  cases p <;> exact h

/-- Actual joint derivatives commute with conjugate transposition in the original
coordinate order. Source: gain one for the literal adjoint in Step 3. -/
theorem jet_conjTranspose (w : List (Coordinate n)) (A : FullAmplitude n r) :
    jet w (fun x y η ↦ (A x y η).conjTranspose) =
      fun x y η ↦ (jet w A x y η).conjTranspose := by
  induction w with
  | nil => rfl
  | cons c w ih => rw [jet_cons, ih, derivative_conjTranspose]; rfl

/-- Frobenius norms of primitive jets are unchanged by the literal adjoint.
Source: gain one in Step 3 of `app:ch_regular_base:thm:actual-calculus`. -/
theorem norm_jet_conjTranspose (w : List (Coordinate n)) (A : FullAmplitude n r) (x y η : E) :
    ‖jet w (fun x y η ↦ (A x y η).conjTranspose) x y η‖ = ‖jet w A x y η‖ := by
  rw [jet_conjTranspose, Matrix.frobenius_norm_conjTranspose]

/-- Primitive local regularity passes to the conjugate-transposed full amplitude.
Source: the literal-adjoint gain-one paragraph in Step 3. -/
theorem SmoothAwayZero.conjTranspose {A : FullAmplitude n r} (hA : SmoothAwayZero A) :
    SmoothAwayZero (fun x y η ↦ (A x y η).conjTranspose) := by
  intro w x y η hη p
  rw [jet_conjTranspose]
  have h := (hA w x y η hη p).star
  cases p <;> exact h

/-- The physical covector in the literal adjoint's output derivative.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`, gain-one paragraph. -/
def covectorOutputCoefficient (i : Fin n) : Field n ℂ := fun _ _ η ↦ Complex.I * (η i : ℂ)

private theorem derivative_constant (c : Coordinate n) (z : ℂ) :
    derivative c (fun (_ _ _ : E) ↦ z) = 0 := by
  funext x y η
  rcases c with ⟨p, j⟩
  cases p <;> simp [derivative, slice, anchor, partialDeriv]

private theorem derivative_covectorOutputCoefficient (i : Fin n) (c : Coordinate n) :
    derivative c (covectorOutputCoefficient i) =
      fun _ _ _ ↦ if c.1 = .covector ∧ c.2 = i then Complex.I else 0 := by
  funext x y η
  rcases c with ⟨s, j⟩
  cases s with
  | left => simp [derivative, covectorOutputCoefficient, slice, anchor, partialDeriv]
  | right => simp [derivative, covectorOutputCoefficient, slice, anchor, partialDeriv]
  | covector =>
    let L : E →L[ℝ] ℂ := (Complex.I • Complex.ofRealCLM).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i)
    change (fderiv ℝ L η) (EuclideanSpace.single j 1) = _
    rw [L.fderiv]
    by_cases hij : i = j <;> simp [L, hij, eq_comm]

/-- All higher covector-coefficient jets vanish after the first derivative.
This is proved for the physical covector itself, not assumed as a symbol bound.
Source: gain one for the literal adjoint in Step 3. -/
theorem jet_covectorOutputCoefficient (i : Fin n) (w : List (Coordinate n)) :
    jet w (covectorOutputCoefficient i) =
      match w with
      | [] => covectorOutputCoefficient i
      | [c] => fun _ _ _ ↦ if c.1 = .covector ∧ c.2 = i then Complex.I else 0
      | _ :: _ :: _ => 0 := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [jet_cons, ih]
    cases w with
    | nil => exact derivative_covectorOutputCoefficient i c
    | cons d v =>
      cases v with
      | nil => exact derivative_constant c _
      | cons e v => exact derivative_zero c

/-- Smoothness of the explicit physical covector coefficient, including all jets.
Source: the literal-adjoint gain-one paragraph in Step 3. -/
theorem smooth_covectorOutputCoefficient (i : Fin n) : SmoothAwayZero (covectorOutputCoefficient i) := by
  intro w x y η _ p
  rw [jet_covectorOutputCoefficient]
  cases w with
  | nil =>
    cases p <;> simp only [slice, anchor, covectorOutputCoefficient]
    · fun_prop
    · fun_prop
    · exact ((Complex.I • Complex.ofRealCLM).comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i)).differentiableAt
  | cons c w =>
    cases w <;> cases p <;> exact differentiableAt_const _

/-- Explicit weighted order-one estimate for the physical covector factor.
Source: gain one for the literal adjoint in Step 3. -/
theorem weighted_covectorOutputCoefficient_le (i : Fin n) (w : List (Coordinate n))
    (x y η : E) (ρ : ℝ) (hρ : 1 ≤ ρ) (hη : ‖η‖ ≤ ρ) :
    ρ ^ frequencyOrder w * ‖jet w (covectorOutputCoefficient i) x y η‖ ≤ ρ := by
  rw [jet_covectorOutputCoefficient]
  cases w with
  | nil =>
    simpa [frequencyOrder, covectorOutputCoefficient, norm_mul] using
      (PiLp.norm_apply_le η i).trans hη
  | cons c w =>
    cases w with
    | nil =>
      by_cases hc : c.1 = .covector ∧ c.2 = i
      · simp [hc, frequencyOrder]
      · simp [hc, le_trans zero_le_one hρ]
    | cons d w => simpa using le_trans zero_le_one hρ

/-- Finite first-output formula for the literal adjoint. All matrix jets are those
of the original amplitude, conjugate-transposed once. Source: gain one in Step 3. -/
theorem jet_adjointFirstOutputAmplitude (A : FullAmplitude n r) (i : Fin n)
    (hA : SmoothAwayZero A) (w : List (Coordinate n)) (x y η : E) (hη : η ≠ 0) :
    jet w (adjointFirstOutputAmplitude A i) x y η =
      (jet (w ++ [(.right, i)]) A x y η).conjTranspose +
        ((splits w).map (fun p ↦ jet p.1 (covectorOutputCoefficient i) x y η •
          (jet p.2 A x y η).conjTranspose)).sum := by
  have he : adjointFirstOutputAmplitude A i =
      derivative (.right, i) (fun x y η ↦ (A x y η).conjTranspose) +
        multiply (covectorOutputCoefficient i) (fun x y η ↦ (A x y η).conjTranspose) := rfl
  rw [he, jet_firstOutput _ _ _ hA.conjTranspose (smooth_covectorOutputCoefficient i) w x y η hη]
  simp_rw [jet_conjTranspose]

/-- Order-zero weighted jets of the literal adjoint's first output amplitude from
order-minus-one jets of the original full amplitude through `|w|+1`. No additional
phase or operator bound is required in this direction.
Source: gain one after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem weighted_adjointFirstOutputAmplitude_le (A : FullAmplitude n r) (i : Fin n)
    (hA : SmoothAwayZero A) (w : List (Coordinate n)) (x y η : E) (hη : η ≠ 0)
    (ρ a : ℝ) (hρ : 1 ≤ ρ) (ha : 0 ≤ a) (hηρ : ‖η‖ ≤ ρ)
    (hAj : ∀ v, v.length ≤ w.length + 1 →
      ρ ^ frequencyOrder v * ‖jet v A x y η‖ ≤ a / ρ) :
    ρ ^ frequencyOrder w * ‖jet w (adjointFirstOutputAmplitude A i) x y η‖ ≤
      a + (2 : ℝ) ^ w.length * a := by
  have he : adjointFirstOutputAmplitude A i =
      derivative (.right, i) (fun x y η ↦ (A x y η).conjTranspose) +
        multiply (covectorOutputCoefficient i) (fun x y η ↦ (A x y η).conjTranspose) := rfl
  rw [he]
  simpa only [one_mul] using weighted_firstOutput_le
    (fun x y η ↦ (A x y η).conjTranspose) (covectorOutputCoefficient i) (.right, i)
    (by simp) hA.conjTranspose (smooth_covectorOutputCoefficient i) w x y η hη
    ρ a 1 hρ ha zero_le_one
    (fun v hv ↦ by simpa only [norm_jet_conjTranspose] using hAj v hv)
    (fun v _ ↦ by simpa only [one_mul] using weighted_covectorOutputCoefficient_le i v x y η ρ hρ hηρ)

end JanetCartan.FourierIntegral.FirstOutputJets
