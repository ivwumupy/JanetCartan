module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.SpatialRealization.Scalar
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.SobolevAssembly

/-!
# The spatial transfer input of the envelope induction

Connect the proved literal all-data identities to `HasSpatialAmplitudeTransfer`
for `app:ch_response:eq:direct-envelope-profile`. The parent supplies its full
amplitude interpretation, support preservation, and the algebraic identification
of the expression modifications. The independent low calculus supplies bounded
realizations agreeing with those SAME literal kernels. All weak derivative
identities and source approximation are proved here; no high norm is an input.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.SpatialRealization
open FourierIntegral Pseudodifferential IsometricEmbedding.Response.NearCarrier
variable {n : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin 1)) 2 (volume : Measure E)
variable {Z Fld ι : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup Fld] [NormedSpace ℝ Fld]

/-- The forward literal kernel supplies the spatial-transfer hypothesis of the
Sobolev induction, on all scalar data with first L² derivatives. Remaining parent
inputs concern only expression interpretation/support, primitive geometry, and
bounded L² realizations. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem hasSpatialAmplitudeTransfer_forward
    (v : Fin n → Z) (qs : Fin n → List (Z × ι × (Fld →L[ℝ] Fld →L[ℝ] Fld)))
    (M : Fin n → Fin n → Fld →L[ℝ] Fld →L[ℝ] Fld) (idx : Fin n → Fin n → ι)
    (a : ι → Z → Fld) (T : (Z → Fld) → H →L[ℂ] H) (P : (Z → Fld) → Prop)
    (A : (Z → Fld) → FullAmplitude n 1)
    {X Y F : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {Φ : E → E → ℝ} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ))
    {B : E → E → Matrix (Fin n) (Fin n) ℝ}
    (hB : ∀ i j, ContDiff ℝ ∞ (fun p : E × E ↦ B p.1 p.2 i j))
    (hgrad : ∀ i x δ, partialDeriv (fun z ↦ Φ z δ) x i = ∑ j, B x δ i j * δ j)
    (hA : ∀ b, P b → ForwardAmplitudeAdmissible X Y F (A b))
    (hremP : ∀ b : AmplitudeExpression Z Fld ι, P (b.evaluate a) →
      ∀ i, P ((b.divergenceTransfer (v i) (qs i)).evaluate a))
    (hdatumP : ∀ b : AmplitudeExpression Z Fld ι, P (b.evaluate a) →
      ∀ i j, P ((b.coefficientProduct (M i j) (idx i j)).evaluate a))
    (hrem : ∀ b : AmplitudeExpression Z Fld ι, P (b.evaluate a) → ∀ i,
      A ((b.divergenceTransfer (v i) (qs i)).evaluate a) =
        forwardRemainderAmplitude B (A (b.evaluate a)) i)
    (hdatum : ∀ b : AmplitudeExpression Z Fld ι, P (b.evaluate a) → ∀ i j,
      A ((b.coefficientProduct (M i j) (idx i j)).evaluate a) =
        forwardDatumAmplitude B (A (b.evaluate a)) i j)
    (hT : ∀ b, P b → ∀ t : graphTestSpace n 1, T b (graphTestToLp t) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (graphOperator Φ (A b) (fun y ↦ (t.val y).ofLp) x)) :
    HasSpatialAmplitudeTransfer v qs M idx a (fun b ↦ scalarGraphOperator (T b)) P := by
  intro b hb u du hdu i
  apply forwardGraph_allData_scalar_derivative hX hY hF hΦ (hA _ hb) i (hB i)
    (hgrad i) (T (b.evaluate a))
    (T ((b.divergenceTransfer (v i) (qs i)).evaluate a))
    (fun j ↦ T ((b.coefficientProduct (M i j) (idx i j)).evaluate a)) (hT _ hb)
    _ _ u du hdu
  · intro t
    simpa only [hrem b hb i] using hT _ (hremP b hb i) t
  · intro j t
    simpa only [hdatum b hb i j] using hT _ (hdatumP b hb i j) t

/-- The reverse literal kernel supplies the same spatial-transfer hypothesis,
with full remainder `∂y A + Σ ∂x(C A)`. The expression equalities therefore
retain derivatives of the inverse and the entire physical weight. The parent
instantiates them for its selected `j_S U⁻¹` amplitude.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem hasSpatialAmplitudeTransfer_reverse
    (v : Fin n → Z) (qs : Fin n → List (Z × ι × (Fld →L[ℝ] Fld →L[ℝ] Fld)))
    (M : Fin n → Fin n → Fld →L[ℝ] Fld →L[ℝ] Fld) (idx : Fin n → Fin n → ι)
    (a : ι → Z → Fld) (T : (Z → Fld) → H →L[ℂ] H) (P : (Z → Fld) → Prop)
    (A : (Z → Fld) → FullAmplitude n 1)
    {X Y F : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {S : E → E → ℝ} {ζ : E} {ρ : ℝ}
    (hΦ : ContDiff ℝ ∞ (Function.uncurry (phaseIncrement S ζ ρ)))
    {B C : E → E → Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ i j, ContDiff ℝ ∞ (fun p : E × E ↦ C p.1 p.2 i j))
    (hinv : ∀ b, P b → ∀ y δ, ∀ x ∈ tsupport (fun z ↦ A b y z δ),
      C x δ * B x δ = 1)
    (hgrad : ∀ b, P b → ∀ y δ, ∀ x ∈ tsupport (fun z ↦ A b y z δ), ∀ l,
      partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x l =
        (B x δ).mulVec (fun k ↦ δ k) l)
    (hA : ∀ b, P b → ForwardAmplitudeAdmissible X Y F (A b))
    (hremP : ∀ b : AmplitudeExpression Z Fld ι, P (b.evaluate a) →
      ∀ i, P ((b.divergenceTransfer (v i) (qs i)).evaluate a))
    (hdatumP : ∀ b : AmplitudeExpression Z Fld ι, P (b.evaluate a) →
      ∀ i j, P ((b.coefficientProduct (M i j) (idx i j)).evaluate a))
    (hrem : ∀ b : AmplitudeExpression Z Fld ι, P (b.evaluate a) → ∀ i,
      A ((b.divergenceTransfer (v i) (qs i)).evaluate a) =
        ReverseDerivative.remainderAmplitude C (A (b.evaluate a)) i)
    (hdatum : ∀ b : AmplitudeExpression Z Fld ι, P (b.evaluate a) → ∀ i j,
      A ((b.coefficientProduct (M i j) (idx i j)).evaluate a) =
        ReverseDerivative.datumAmplitude C (A (b.evaluate a)) i j)
    (hT : ∀ b, P b → ∀ t : graphTestSpace n 1, T b (graphTestToLp t) =ᵐ[volume]
      fun y ↦ WithLp.toLp 2 (ReverseDerivative.envelopeGraph S ζ ρ (A b)
        (fun x ↦ (t.val x).ofLp) y)) :
    HasSpatialAmplitudeTransfer v qs M idx a (fun b ↦ scalarGraphOperator (T b)) P := by
  intro b hb u du hdu i
  apply reverseGraph_allData_scalar_derivative hX hY hF hΦ (hA _ hb) i (hC i)
    (hinv _ hb) (hgrad _ hb) (T (b.evaluate a))
    (T ((b.divergenceTransfer (v i) (qs i)).evaluate a))
    (fun j ↦ T ((b.coefficientProduct (M i j) (idx i j)).evaluate a)) (hT _ hb)
    _ _ u du hdu
  · intro t
    simpa only [hrem b hb i] using hT _ (hremP b hb i) t
  · intro j t
    simpa only [hdatum b hb i j] using hT _ (hdatumP b hb i j) t

end JanetCartan.ResponseTransfer.SpatialRealization
