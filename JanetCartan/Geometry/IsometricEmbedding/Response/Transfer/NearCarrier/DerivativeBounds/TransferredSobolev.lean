module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.SobolevAssembly

/-!
# Sobolev estimates for transferred full amplitudes

The branch estimate for the joint spatial/parameter induction in
`app:ch_response:eq:direct-envelope-profile`. Directions in a transfer step may
include parameter, normalized covector, or either physical position. All of
these spend the same derivative budget. The scalar realization uses literal
Euclidean Lebesgue measure; bilinear amplitude maps retain their given norms,
including Frobenius matrix multiplication when that is the chosen value space.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open JanetCartan.Pseudodifferential

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier

variable {d : ℕ} {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "L2" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

namespace AmplitudeTransferStep

/-- The Sobolev version of the transferred low bound in
`app:ch_response:eq:direct-envelope-profile`. A branch with `r` derivatives on
its datum after `q` transfers has amplitude cost `q-r`. Applying `s` further
spatial derivatives therefore costs only `c + s + q-r` primitive orders.
The constant is chosen before scale, fields, frequency-indexed realization,
and datum. The actual low theorem, spatial transfer identity and geometric
admissibility remain premises; no modified-amplitude estimate is assumed.
This is consumed by the finite compact-parameter induction. -/
theorem exists_transferred_spatialSobolev_constant
    (steps : List (AmplitudeTransferStep X E ι)) (e : AmplitudeExpression X E ι)
    (he : e.derivativeCost = 0)
    (v : Fin d → X) (qs : Fin d → List (X × ι × (E →L[ℝ] E →L[ℝ] E)))
    (B : Fin d → Fin d → E →L[ℝ] E →L[ℝ] E) (idx : Fin d → Fin d → ι)
    (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (c R : ℕ) (hR : c + 2 < R) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (s : ℕ) :
    let b := orderedTransferAction apply steps e
    let k := steps.length - (steps.map datumOrder).sum
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ (a : ι → X → E), (∀ i, ContDiff ℝ ∞ (a i)) →
      (∀ i j, j ≤ c + k + s → ∀ x,
        ‖iteratedFDeriv ℝ j (a i) x‖ ≤ M i j * L ^ (j + 2 - R)) →
      ∀ (T : (X → E) → L2 →L[ℂ] L2) (P : (X → E) → Prop),
      (∀ b, P b → ContDiff ℝ ∞ b → ∀ A : ℝ, 0 ≤ A →
        (∀ j, j ≤ c → ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ A) → ‖T b‖ ≤ C₀ * A) →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i, P ((b.divergenceTransfer (v i) (qs i)).evaluate a)) →
      (∀ b : AmplitudeExpression X E ι, P (b.evaluate a) →
        ∀ i j, P ((b.coefficientProduct (B i j) (idx i j)).evaluate a)) →
      HasSpatialAmplitudeTransfer v qs B idx a T P → P (b.evaluate a) →
      ∀ f : L2, MemFourierSobolev (s : ℝ) f →
        MemFourierSobolev (s : ℝ) (T (b.evaluate a) f) ∧
          fourierSobolevNorm (s : ℝ) (T (b.evaluate a) f) ≤
            C * (L ^ k * spatialEnvelopeSobolevProfile s L f) := by
  dsimp only
  simpa only [derivativeCost_orderedTransferAction_of_zero steps e he] using
    AmplitudeExpression.exists_spatialSobolev_constant v qs B idx M hM c R hR C₀ hC₀ s
      (orderedTransferAction apply steps e)

end AmplitudeTransferStep
end JanetCartan.IsometricEmbedding.Response.NearCarrier
