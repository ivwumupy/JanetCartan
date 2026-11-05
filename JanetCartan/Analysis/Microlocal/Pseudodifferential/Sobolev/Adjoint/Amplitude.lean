module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Realization

/-!
# Reversal of the physical amplitude

The literal adjoint in `app:ch_regular_base:thm:actual-calculus` (2)–(3)
conjugates the amplitude and exchanges its two physical positions. Frequency
and all masks are retained. Physical derivative budgets are preserved exactly.
-/

@[expose] public noncomputable section
open scoped ContDiff
open JanetCartan.AmplitudeBound
namespace JanetCartan.Pseudodifferential
variable {d : ℕ}

/-- Coordinate-block swap for `app:ch_regular_base:thm:actual-calculus`. -/
def swapPositionIndex (i : Fin (2 * d)) : Fin (2 * d) :=
  if h : i.val < d then ⟨d + i.val, by omega⟩ else ⟨i.val - d, by omega⟩

/-- Coordinate-block reversal is involutive (`app:ch_regular_base:thm:actual-calculus`). -/
theorem swapPositionIndex_involutive :
    Function.Involutive (swapPositionIndex (d := d)) := by
  intro i
  apply Fin.ext
  by_cases hi : i.val < d
  · simp [swapPositionIndex, hi, show ¬d + i.val < d by omega]
  · simp [swapPositionIndex, hi, show i.val - d < d by omega]
    omega

/-- The exchange of the two coordinate blocks in
`app:ch_regular_base:thm:actual-calculus`. -/
def positionReversalIndex (d : ℕ) : Equiv.Perm (Fin (2 * d)) :=
  ⟨swapPositionIndex, swapPositionIndex,
    swapPositionIndex_involutive, swapPositionIndex_involutive⟩

/-- Physical position reversal is a real linear isometry
(`app:ch_regular_base:thm:actual-calculus`). -/
def positionReversal (d : ℕ) :
    EuclideanSpace ℝ (Fin (2 * d)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * d)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (positionReversalIndex d)

/-- The coordinate formula for physical reversal
(`app:ch_regular_base:thm:actual-calculus`). -/
theorem positionReversal_apply (z : EuclideanSpace ℝ (Fin (2 * d))) (i : Fin (2 * d)) :
    positionReversal d z i = z (positionReversalIndex d i) := rfl

/-- Reversing physical positions twice is the identity
(`app:ch_regular_base:thm:actual-calculus`). -/
@[simp] theorem positionReversal_involutive (z : EuclideanSpace ℝ (Fin (2 * d))) :
    positionReversal d (positionReversal d z) = z := by
  ext i
  simp only [positionReversal_apply]
  exact congrArg z (swapPositionIndex_involutive i)

/-- Position reversal exchanges the literal paired coordinates
(`app:ch_regular_base:thm:actual-calculus`). -/
@[simp] theorem positionReversal_pairedPosition
    (x y : EuclideanSpace ℝ (Fin d)) :
    positionReversal d (pairedPosition x y) = pairedPosition y x := by
  ext i
  rw [positionReversal_apply]
  change pairedPosition x y (swapPositionIndex i) = pairedPosition y x i
  by_cases hi : i.val < d
  · simp [pairedPosition, swapPositionIndex, hi, show ¬d + i.val < d by omega]
  · simp [pairedPosition, swapPositionIndex, hi, show i.val - d < d by omega]

/-- The full reversed amplitude for the literal Hilbert adjoint in
`app:ch_regular_base:thm:actual-calculus` (2)–(3). -/
def adjointAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (ξ : EuclideanSpace ℝ (Fin d)) (z : EuclideanSpace ℝ (Fin (2 * d))) : ℂ :=
  star (b ξ (positionReversal d z))

/-- The source and target positions are exchanged and every mask is conjugated
(`app:ch_regular_base:thm:actual-calculus`). -/
@[simp] theorem adjointAmplitude_pairedPosition
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (ξ x y : EuclideanSpace ℝ (Fin d)) :
    adjointAmplitude b ξ (pairedPosition x y) = star (b ξ (pairedPosition y x)) := by
  simp [adjointAmplitude]

/-- Reversing and conjugating twice restores the full amplitude, including
all masks (`app:ch_regular_base:thm:actual-calculus`). -/
@[simp] theorem adjointAmplitude_involutive
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ) :
    adjointAmplitude (adjointAmplitude b) = b := by
  funext ξ z
  simp [adjointAmplitude]

/-- Joint smoothness is preserved by physical reversal and conjugation
(`app:ch_regular_base:thm:actual-calculus`). -/
theorem contDiff_adjointAmplitude
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) :
    ContDiff ℝ ∞ (Function.uncurry (adjointAmplitude b)) :=
  Complex.conjCLE.contDiff.comp (hb.comp (contDiff_fst.prodMk
    ((positionReversal d).toContinuousLinearEquiv.contDiff.comp contDiff_snd)))

/-- Reversal preserves the fixed physical support box, including its boundary
(`app:ch_regular_base:thm:actual-calculus`). -/
theorem supportedInCenteredBox_adjointAmplitude
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    {R : ℝ} (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) :
    ∀ ξ, SupportedInCenteredBox R (adjointAmplitude b ξ) := by
  intro ξ z hz i
  have h := hs ξ (positionReversal d z) (by simpa [adjointAmplitude] using hz)
    (positionReversalIndex d i)
  simpa only [positionReversal_apply, show positionReversalIndex d (positionReversalIndex d i) = i
    from swapPositionIndex_involutive i] using h

/-- The exact ordered derivative formula for a reversed conjugate amplitude
(`app:ch_regular_base:thm:actual-calculus`). -/
theorem euclideanCoordinateDerivList_adjointAmplitude
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (ξ : EuclideanSpace ℝ (Fin d))
    (is : List (Fin (2 * d))) :
    euclideanCoordinateDerivList is (adjointAmplitude b ξ) =
      fun z ↦ star (euclideanCoordinateDerivList (is.map (positionReversalIndex d))
        (b ξ) (positionReversal d z)) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    funext z
    simp only [euclideanCoordinateDerivList, ih, List.map_cons]
    have hf := (contDiff_euclideanCoordinateDerivList (hb ξ)
      (is.map (positionReversalIndex d))).differentiable (by simp)
    have hc := (hf (positionReversal d z)).hasFDerivAt.comp z
      ((positionReversal d).toContinuousLinearEquiv.hasFDerivAt)
    have hh := Complex.conjCLE.hasFDerivAt.comp z hc
    have hh' : HasFDerivAt
        (fun z ↦ star (euclideanCoordinateDerivList (is.map (positionReversalIndex d))
          (b ξ) (positionReversal d z))) _ z := hh
    rw [hh'.fderiv]
    change star (fderiv ℝ _ _ (positionReversal d (EuclideanSpace.single i 1))) = _
    rw [show positionReversal d (EuclideanSpace.single i 1) =
      EuclideanSpace.single (positionReversalIndex d i) 1 from
      LinearIsometryEquiv.piLpCongrLeft_single (positionReversalIndex d) i 1]

/-- The same total physical derivative budget suffices for the adjoint
(`app:ch_regular_base:thm:actual-calculus`). -/
theorem hasAmplitudeDerivativeBound_adjointAmplitude
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) {N : ℕ} {A : ℝ}
    (h : HasAmplitudeDerivativeBound b N A) :
    HasAmplitudeDerivativeBound (adjointAmplitude b) N A := by
  intro ξ is hi z
  rw [euclideanCoordinateDerivList_adjointAmplitude hb, norm_star]
  exact h ξ _ (by simpa using hi) _

/-- Every frequency-weighted physical bound is preserved with the same constant
and order; in particular this applies to orders zero and minus one in
`app:ch_regular_base:thm:actual-calculus`. -/
theorem weighted_physical_bound_adjointAmplitude
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (N : ℕ) (W : EuclideanSpace ℝ (Fin d) → ℝ)
    (h : ∀ ξ is, is.length ≤ N → ∀ z, ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ W ξ) :
    ∀ ξ is, is.length ≤ N → ∀ z,
      ‖euclideanCoordinateDerivList is (adjointAmplitude b ξ) z‖ ≤ W ξ := by
  intro ξ is hi z
  rw [euclideanCoordinateDerivList_adjointAmplitude hb, norm_star]
  exact h ξ _ (by simpa using hi) _

/-- Order minus one physical budgets are preserved with no derivative loss
or change of constant (`app:ch_regular_base:thm:actual-calculus` (2)–(3)). -/
theorem orderNegOne_physical_bound_adjointAmplitude
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (N : ℕ) (A : ℝ)
    (h : ∀ ξ is, is.length ≤ N → ∀ z,
      ‖euclideanCoordinateDerivList is (b ξ) z‖ ≤ A / (1 + ‖ξ‖)) :
    ∀ ξ is, is.length ≤ N → ∀ z,
      ‖euclideanCoordinateDerivList is (adjointAmplitude b ξ) z‖ ≤ A / (1 + ‖ξ‖) :=
  weighted_physical_bound_adjointAmplitude hb N (fun ξ ↦ A / (1 + ‖ξ‖)) h

/-- Source derivatives of the literal adjoint have exactly the norms of target
derivatives of the original full amplitude. This transfers primitive source
bounds for `app:ch_regular_base:thm:actual-calculus` (2)–(3). -/
theorem norm_iteratedFDeriv_adjointAmplitude_source
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (ξ x y : EuclideanSpace ℝ (Fin d)) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun z ↦ adjointAmplitude b ξ (pairedPosition x z)) y‖ =
      ‖iteratedFDeriv ℝ j (fun z ↦ b ξ (pairedPosition z x)) y‖ := by
  simpa only [adjointAmplitude_pairedPosition, Complex.star_def, Function.comp_def,
    Complex.conjLIE_apply] using
    Complex.conjLIE.norm_iteratedFDeriv_comp_left (fun z ↦ b ξ (pairedPosition z x)) y j

end JanetCartan.Pseudodifferential
