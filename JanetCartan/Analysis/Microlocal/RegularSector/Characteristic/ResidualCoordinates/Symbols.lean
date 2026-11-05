module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.Basic

/-!
# Literal matrix symbols in the residual's coordinates

All definitions use the same selected split, pencil, root, flow, inverse
chart, minor and transported source mask. The leading endpoint is obtained
from `exists_pencil_leading_amplitude`'s diagonal output. The off-root
complement equation follows from `exists_smooth_minorComplementInverse`,
including its actual spectral interval; it is not an assumed residual input.
Consumer: `CompleteResidual.completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:two-term-null-identity` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification ActualCarriers
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ

/-- The unchanged spatial root state at a canonical physical point.
Source: `app:ch_regular_base:eq:complement-inverse`. -/
def rootState (x : E) (η : Euclidean d) : RootState (Euclidean d) :=
  (x 0, (spatialPart x, η))

/-- The actual local phase, merely curried into the residual interface.
Smoothness is asserted only on its chart.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
def phase (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d))
    (TwoTimePoint (Euclidean d))) : TwoTimePhase d :=
  fun t s y η ↦ twoTimePhase C (t, (s, (y, η)))

/-- The literal matrix whose columns are the constructed leading columns.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
def leading (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ) : TwoTimeAmplitude d (d + 1) :=
  fun t s y η k j ↦ (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j
    (t, (s, (y, η))) k : ℂ)

/-- The literal correction `W₁ = i b₋₁ P W₀`; the factor `i` is essential for
the physical `P`, without the old `P/i` convention.
Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
def correction (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ) : TwoTimeAmplitude d (d + 1) :=
  fun t s y η k j ↦ Complex.I * (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j
    (t, (s, (y, η))) k : ℂ)

/-- The original transported source datum in canonical coordinates. This is
distinct from both physical masks and the right Fourier multiplier.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
def sourceSymbol (σ : RootState (Euclidean d) → ℝ) (x : E) (η : Euclidean d) : ℂ :=
  σ (rootState x η)

/-- The oblique leading projector `Π = (A_t k) lᵀ` of the same minor.
Source: `app:ch_regular_base:eq:complement-inverse`. -/
def projector (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat)
    (h : RootState (Euclidean d) → ℝ) (r c : Fin (d + 1))
    (x : E) (η : Euclidean d) : CMat :=
  let w := rootState x η
  let H := rootPencil (coordinateSplit i) Q h w
  let A := rootTimeCoefficient (coordinateSplit i) Q w
  (vecMulVec (A *ᵥ minorRightNullvector H r c) (minorLeftNullvector H A r c)).map Complex.ofReal

/-- The actual complement at the independent, possibly off-root frequency.
Its spectral offset is `τ - h(x,η)` on the same minor patch.
Source: `app:ch_regular_base:eq:complement-inverse`. -/
def bminus (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat)
    (h : RootState (Euclidean d) → ℝ) (r c : Fin (d + 1)) (x ξ : E) : CMat :=
  let w := rootState x (spatialPart ξ)
  (minorComplementInverse (rootPencil (coordinateSplit i) Q h w)
    (rootTimeCoefficient (coordinateSplit i) Q w) r c (ξ 0 - h w)).map Complex.ofReal

/-- The complete first-order principal matrix in the residual equals the
original pencil at the same physical covector.
Source: `app:ch_regular_base:eq:complement-symbol`. -/
theorem principalMatrix_eq (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat) (x ξ : E) :
    (∑ a, (ξ a : ℂ) • (coefficient i Q x a).map Complex.ofReal) =
      (pencil (Q (physicalCoordinates i x)) (physicalCoordinates i ξ)).map Complex.ofReal := by
  have hr : (∑ a, ξ a • coefficient i Q x a) =
      pencil (Q (physicalCoordinates i x)) (physicalCoordinates i ξ) := by
    simpa only [coefficient, map_sum, map_smul, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply, pencilContinuousLinearMap_apply] using
      congrArg (fun v ↦ pencilContinuousLinearMap (Q (physicalCoordinates i x))
        (physicalCoordinates i v)) ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).sum_repr ξ)
  rw [← hr]
  ext j k
  simp [Matrix.sum_apply]

/-- The canonical pencil is the root pencil plus the actual spectral offset
times the time coefficient. This is the linear-in-`τ` identity used by the
off-root inverse (`app:ch_regular_base:eq:complement-symbol`). -/
theorem pencil_eq_root_add (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat)
    (h : RootState (Euclidean d) → ℝ) (x ξ : E) :
    pencil (Q (physicalCoordinates i x)) (physicalCoordinates i ξ) =
      rootPencil (coordinateSplit i) Q h (rootState x (spatialPart ξ)) +
        (ξ 0 - h (rootState x (spatialPart ξ))) •
          rootTimeCoefficient (coordinateSplit i) Q (rootState x (spatialPart ξ)) := by
  have he : ((ξ 0, spatialPart ξ) : ℝ × Euclidean d) =
      (h (rootState x (spatialPart ξ)), spatialPart ξ) +
        (ξ 0 - h (rootState x (spatialPart ξ))) • (1, 0) := by
    ext j <;> simp
  change pencilContinuousLinearMap (Q (physicalCoordinates i x))
      ((coordinateSplit i).symm (ξ 0, spatialPart ξ)) = _
  rw [he, map_add, map_smul, map_add, map_smul]
  rfl

/-- The off-root complement equation is a conclusion on an actual positive
interval supplied by `exists_smooth_minorComplementInverse`. The root,
selected minor and simple-root derivative are precisely outputs of
`exists_pencil_leading_amplitude` on its root domain.
Source: `app:ch_regular_base:eq:complement-symbol`. -/
theorem exists_complement_interval (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat)
    (h : RootState (Euclidean d) → ℝ) (r c : Fin (d + 1)) (x : E) (η : Euclidean d)
    (hroot : (rootPencil (coordinateSplit i) Q h (rootState x η)).det = 0)
    (hm : (rootPencil (coordinateSplit i) Q h (rootState x η)).adjugate r c ≠ 0)
    (ht : fderiv ℝ Matrix.det (rootPencil (coordinateSplit i) Q h (rootState x η))
      (rootTimeCoefficient (coordinateSplit i) Q (rootState x η)) ≠ 0) :
    ∃ ε > (0 : ℝ), ∀ τ : ℝ, |τ - h (rootState x η)| < ε →
      (∑ a, ((timeSpacePoint τ η) a : ℂ) • (coefficient i Q x a).map Complex.ofReal) *
        bminus i Q h r c x (timeSpacePoint τ η) = 1 - projector i Q h r c x η := by
  obtain ⟨ε, hε, _, hb⟩ := exists_smooth_minorComplementInverse
    (rootPencil (coordinateSplit i) Q h (rootState x η))
    (rootTimeCoefficient (coordinateSplit i) Q (rootState x η)) r c hroot hm ht
  refine ⟨ε, hε, ?_⟩
  intro τ hτ
  have hid := (hb (τ - h (rootState x η)) hτ).1
  rw [principalMatrix_eq, pencil_eq_root_add i Q h]
  simp only [bminus, timeSpacePoint_time, spatialPart_timeSpacePoint]
  ext j k
  have hij := congrArg (fun M : Mat ↦ (M j k : ℂ)) hid
  simpa [projector, complementProjection, Matrix.mul_apply, Matrix.map_apply,
    Matrix.sub_apply, Matrix.one_apply, apply_ite Complex.ofReal] using hij

/-- Initial row data from the same signed transport give the precise upper
endpoint `A_t W₀ = σ Π`. No leading-endpoint identity is assumed.
The sole diagonal input is exported by `exists_pencil_leading_amplitude`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem leading_endpoint (i : Fin (d + 1)) (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ) (x : E) (η : Euclidean d)
    (hinit : ∀ j, pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j
      (x 0, rootState x η) =
      (σ (rootState x η) * minorLeftNullvector
        (rootPencil (coordinateSplit i) Q h (rootState x η))
        (rootTimeCoefficient (coordinateSplit i) Q (rootState x η)) r c j) •
          minorRightNullvector (rootPencil (coordinateSplit i) Q h (rootState x η)) r c) :
    (coefficient i Q x 0).map Complex.ofReal *
      leading i Q B h Φ C r c σ (x 0) (x 0) (spatialPart x) η =
        sourceSymbol σ x η • projector i Q h r c x η := by
  have hA : coefficient i Q x 0 = rootTimeCoefficient (coordinateSplit i) Q (rootState x η) := by
    simp [coefficient, rootTimeCoefficient, rootState, physicalCoordinates_apply]
  ext k j
  simp only [Matrix.mul_apply, leading]
  change (∑ a, _ * (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j
    (x 0, rootState x η) a : ℂ)) = _
  rw [hinit j]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, hA,
    sourceSymbol, projector, Matrix.map_apply, Matrix.smul_apply,
    vecMulVec, Matrix.of_apply, mulVec, dotProduct, Complex.ofReal_sum]
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The actual phase diagonal transfers only where its geometric producer
proves it. No global diagonal or smoothness at the zero frequency is asserted.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem phase_diagonal
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (x : E) (η : Euclidean d)
    (hdiag : twoTimePhase C (x 0, rootState x η) = ⟪spatialPart x, η⟫_ℝ) :
    phase C (x 0) (x 0) (spatialPart x) η = ⟪spatialPart x, η⟫_ℝ := hdiag

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
