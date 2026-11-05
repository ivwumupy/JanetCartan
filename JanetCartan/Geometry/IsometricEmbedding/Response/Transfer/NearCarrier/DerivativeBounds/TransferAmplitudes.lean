module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.LowOperator

/-!
# Literal coefficient and divergence modifications of full amplitudes

The one-derivative forward/reverse rules of
`app:ch_response:eq:direct-envelope-profile` modify a full amplitude either by
coefficient multiplication (when the derivative reaches the datum) or by a
physical derivative plus source divergences. We construct those functions and
prove their total derivative cost. Signs and matrix order are retained in the
bilinear maps. The zero direction permits a pure divergence in the reverse rule.

The operator one-derivative identities remain external analytic inputs. In
particular these amplitude identities do not themselves establish an identity
for the oscillatory integral.
-/

@[expose] public noncomputable section
open scoped ContDiff

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier

variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace AmplitudeExpression

/-- The complete amplitude of the datum-derivative branch in
`app:ch_response:eq:direct-envelope-profile`. A coefficient is a primitive
field, not a bound for a modified amplitude. -/
def coefficientProduct (B : E →L[ℝ] E →L[ℝ] E) (i : ι)
    (e : AmplitudeExpression X E ι) : AmplitudeExpression X E ι :=
  .bilinear B (.primitive i) e

/-- The full no-datum-derivative branch in
`app:ch_response:eq:direct-envelope-profile`: differentiate the amplitude
in the output direction and each coefficient-amplitude product in its source
direction. Every selector derivative is included by ordinary Fréchet differentiation. -/
def divergenceTransfer (v : X)
    (qs : List (X × ι × (E →L[ℝ] E →L[ℝ] E)))
    (e : AmplitudeExpression X E ι) : AmplitudeExpression X E ι :=
  match qs with
  | [] => .deriv v e
  | q :: qs => .add (.deriv q.1 (e.coefficientProduct q.2.2 q.2.1))
      (e.divergenceTransfer v qs)

/-- Coefficient multiplication adds no primitive derivative to the budget
in `app:ch_response:eq:direct-envelope-profile`. -/
@[simp] theorem derivativeCost_coefficientProduct
    (B : E →L[ℝ] E →L[ℝ] E) (i : ι) (e : AmplitudeExpression X E ι) :
    (e.coefficientProduct B i).derivativeCost = e.derivativeCost := by
  simp [coefficientProduct, derivativeCost]

/-- The physical and divergence terms together consume one derivative,
not one derivative for each physical position, in
`app:ch_response:eq:direct-envelope-profile`. -/
@[simp] theorem derivativeCost_divergenceTransfer (v : X)
    (qs : List (X × ι × (E →L[ℝ] E →L[ℝ] E))) (e : AmplitudeExpression X E ι) :
    (e.divergenceTransfer v qs).derivativeCost = e.derivativeCost + 1 := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [divergenceTransfer, derivativeCost, ih]

/-- The literal function of the datum branch, for
`app:ch_response:eq:direct-envelope-profile`. -/
@[simp] theorem evaluate_coefficientProduct
    (a : ι → X → E) (B : E →L[ℝ] E →L[ℝ] E) (i : ι)
    (e : AmplitudeExpression X E ι) (x : X) :
    (e.coefficientProduct B i).evaluate a x = B (a i x) (e.evaluate a x) := rfl

/-- The literal function of the full divergence branch, including both
physical positions, for `app:ch_response:eq:direct-envelope-profile`. -/
theorem evaluate_divergenceTransfer (a : ι → X → E) (v : X)
    (qs : List (X × ι × (E →L[ℝ] E →L[ℝ] E)))
    (e : AmplitudeExpression X E ι) (x : X) :
    (e.divergenceTransfer v qs).evaluate a x =
      (qs.map (fun q => fderiv ℝ (fun y => q.2.2 (a q.2.1 y) (e.evaluate a y)) x q.1)).sum +
        fderiv ℝ (e.evaluate a) x v := by
  induction qs with
  | nil => simp [divergenceTransfer, evaluate]
  | cons q qs ih =>
    simp only [divergenceTransfer, evaluate, ih, List.map_cons, List.sum_cons,
      coefficientProduct]
    simp only [add_assoc]

end AmplitudeExpression

/-- One literal amplitude modification in the ordered transfer proof of
`app:ch_response:eq:direct-envelope-profile`. Its alternatives distinguish
derivatives on the amplitude from derivatives on the datum. -/
inductive AmplitudeTransferStep (X E ι : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  | amplitude : X → List (X × ι × (E →L[ℝ] E →L[ℝ] E)) → AmplitudeTransferStep X E ι
  | datum : ι → (E →L[ℝ] E →L[ℝ] E) → AmplitudeTransferStep X E ι

namespace AmplitudeTransferStep

/-- Actual expression modification in
`app:ch_response:eq:direct-envelope-profile`. -/
def apply : AmplitudeTransferStep X E ι → AmplitudeExpression X E ι → AmplitudeExpression X E ι
  | .amplitude v qs, e => e.divergenceTransfer v qs
  | .datum i B, e => e.coefficientProduct B i

/-- Whether this step differentiates the datum, in
`app:ch_response:eq:direct-envelope-profile`. -/
def datumOrder : AmplitudeTransferStep X E ι → ℕ
  | .amplitude _ _ => 0
  | .datum _ _ => 1

/-- Each actual step assigns exactly one derivative either to the full
amplitude or the datum (`app:ch_response:eq:direct-envelope-profile`). -/
theorem derivativeCost_apply_add_datumOrder (q : AmplitudeTransferStep X E ι)
    (e : AmplitudeExpression X E ι) :
    (q.apply e).derivativeCost + q.datumOrder = e.derivativeCost + 1 := by
  cases q <;> simp [apply, datumOrder]

/-- Reuse of the published ordered action: the amplitude and datum orders
share one total budget at every branch of
`app:ch_response:eq:direct-envelope-profile`. -/
theorem derivativeCost_orderedTransferAction
    (qs : List (AmplitudeTransferStep X E ι)) (e : AmplitudeExpression X E ι) :
    (Pseudodifferential.orderedTransferAction apply qs e).derivativeCost +
        (qs.map datumOrder).sum = e.derivativeCost + qs.length := by
  induction qs with
  | nil => simp [Pseudodifferential.orderedTransferAction]
  | cons q qs ih =>
    simp only [Pseudodifferential.orderedTransferAction, List.map_cons, List.sum_cons,
      List.length_cons]
    have h := q.derivativeCost_apply_add_datumOrder
      (Pseudodifferential.orderedTransferAction apply qs e)
    omega

/-- An undifferentiated full initial amplitude gives exactly `s-r` amplitude
derivatives on a branch with `r` datum derivatives. No modified-amplitude
bound is assumed (`app:ch_response:eq:direct-envelope-profile`). -/
theorem derivativeCost_orderedTransferAction_of_zero
    (qs : List (AmplitudeTransferStep X E ι)) (e : AmplitudeExpression X E ι)
    (he : e.derivativeCost = 0) :
    (Pseudodifferential.orderedTransferAction apply qs e).derivativeCost =
      qs.length - (qs.map datumOrder).sum := by
  have h := derivativeCost_orderedTransferAction qs e
  omega

variable {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- Low norm of a branch formed by the literal coefficient/divergence
modifications, with the desired exponent `s-r` derived from the actual
construction. This is the amplitude conclusion needed in
`app:ch_response:eq:direct-envelope-profile`; the low calculus and primitive
coefficient jets remain conditional, but no modified-amplitude estimate or
derivative-cost assumption on the final amplitude is required. -/
theorem exists_transferred_lowOperator_constant
    (qs : List (AmplitudeTransferStep X E ι)) (e : AmplitudeExpression X E ι)
    (he : e.derivativeCost = 0)
    (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (c R : ℕ) (hR : c + 2 < R) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    let b := Pseudodifferential.orderedTransferAction apply qs e
    let k := qs.length - (qs.map datumOrder).sum
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ (a : ι → X → E), (∀ i, ContDiff ℝ ∞ (a i)) →
      (∀ i j, j ≤ c + k → ∀ x,
        ‖iteratedFDeriv ℝ j (a i) x‖ ≤ M i j * L ^ (j + 2 - R)) →
      ∀ (T : (X → E) → H →L[ℂ] K) (P : (X → E) → Prop),
      (∀ b, P b → ContDiff ℝ ∞ b → ∀ A : ℝ, 0 ≤ A →
        (∀ j, j ≤ c → ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ A) → ‖T b‖ ≤ C₀ * A) →
      P (b.evaluate a) →
      ‖T (b.evaluate a)‖ ≤ C * L ^ k ∧
        ∀ f, ‖T (b.evaluate a) f‖ ≤ (C * L ^ k) * ‖f‖ := by
  exact AmplitudeExpression.exists_lowOperator_constant M hM _ c R _ hR
    (le_of_eq (derivativeCost_orderedTransferAction_of_zero qs e he)) C₀ hC₀

end AmplitudeTransferStep
end JanetCartan.IsometricEmbedding.Response.NearCarrier
