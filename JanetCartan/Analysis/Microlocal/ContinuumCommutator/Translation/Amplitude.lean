module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Coordinates
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Joint physical translations of the full amplitude

The order-one argument in `app:ch_background:prop:bg-inverse` translates both
physical positions. These estimates consume one additional primitive physical
derivative, uniformly in the nonzero step. They concern the literal Euclidean
amplitude; no identification of Euclidean and periodic L² spaces is made.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential

namespace JanetCartan.ContinuumCommutator

variable {d n : ℕ}

/-- The joint output/source direction for `app:ch_background:prop:bg-inverse`. -/
def jointPhysicalDirection (i : Fin d) : EuclideanSpace ℝ (Fin (2 * d)) :=
  EuclideanSpace.single (physicalOutputIndex i) 1 +
    EuclideanSpace.single (physicalSourceIndex i) 1

/-- Both physical positions move with the same sign in
`app:ch_background:prop:bg-inverse`. -/
theorem pairedPosition_add_jointPhysicalDirection (x y : EuclideanSpace ℝ (Fin d))
    (i : Fin d) (h : ℝ) :
    pairedPosition (x + h • EuclideanSpace.single i 1)
      (y + h • EuclideanSpace.single i 1) =
        pairedPosition x y + h • jointPhysicalDirection i := by
  have hp : pairedPosition (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) =
      jointPhysicalDirection i := by
    have he := (pairedPositionCLM (d := d)).map_add
      (EuclideanSpace.single i 1, 0) (0, EuclideanSpace.single i 1)
    simpa [pairedPositionCLM, pairedPosition_single_left, pairedPosition_single_right,
      jointPhysicalDirection] using he
  have he := (pairedPositionCLM (d := d)).map_add (x, y)
    (h • (EuclideanSpace.single i 1, EuclideanSpace.single i 1))
  rw [map_smul] at he
  change _ = pairedPosition x y + h • pairedPosition
    (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) at he
  rw [hp] at he
  exact he

/-- Full amplitude conjugation convention for `app:ch_background:prop:bg-inverse`:
translation acts by `u(x) ↦ u(x + h eᵢ)`. -/
def translatedAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (i : Fin d) (h : ℝ) (ξ : EuclideanSpace ℝ (Fin d))
    (z : EuclideanSpace ℝ (Fin (2 * d))) : ℂ :=
  b ξ (z + h • jointPhysicalDirection i)

/-- The amplitude of the divided conjugation difference in
`app:ch_background:prop:bg-inverse`. -/
def translationDifferenceAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (i : Fin d) (h : ℝ) (ξ : EuclideanSpace ℝ (Fin d))
    (z : EuclideanSpace ℝ (Fin (2 * d))) : ℂ :=
  h⁻¹ • (translatedAmplitude b i h ξ z - b ξ z)

/-- Ordered physical derivatives commute with translation
(`app:ch_background:prop:bg-inverse`). -/
theorem euclideanCoordinateDerivList_translate
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (a : EuclideanSpace ℝ (Fin n))
    (is : List (Fin n)) :
    euclideanCoordinateDerivList is (fun z ↦ f (z + a)) =
      fun z ↦ euclideanCoordinateDerivList is f (z + a) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [euclideanCoordinateDerivList, ih, fderiv_comp_add_right]

/-- Ordered derivatives of the divided full-amplitude translation difference
(`app:ch_background:prop:bg-inverse`). -/
theorem euclideanCoordinateDerivList_translationDifferenceAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (i : Fin d) (h : ℝ)
    (ξ : EuclideanSpace ℝ (Fin d)) (is : List (Fin (2 * d))) :
    euclideanCoordinateDerivList is (translationDifferenceAmplitude b i h ξ) =
      fun z ↦ h⁻¹ • (euclideanCoordinateDerivList is (b ξ)
        (z + h • jointPhysicalDirection i) - euclideanCoordinateDerivList is (b ξ) z) := by
  have ht : ContDiff ℝ ∞ (fun z ↦ b ξ (z + h • jointPhysicalDirection i)) :=
    (hb ξ).comp (contDiff_id.add contDiff_const)
  have he : translationDifferenceAmplitude b i h ξ =
      fun z ↦ (h⁻¹ : ℂ) * ((b ξ (z + h • jointPhysicalDirection i)) + (-1) * b ξ z) := by
    funext z
    simp [translationDifferenceAmplitude, translatedAmplitude, sub_eq_add_neg,
      Complex.real_smul]
    ring
  rw [he, euclideanCoordinateDerivList_const_mul (ht.add (contDiff_const.mul (hb ξ))),
    euclideanCoordinateDerivList_add ht (contDiff_const.mul (hb ξ)),
    euclideanCoordinateDerivList_const_mul (hb ξ), euclideanCoordinateDerivList_translate]
  funext z
  simp [Complex.real_smul, sub_eq_add_neg]
  ring

/-- Differentiating the joint translation path hits the output and source
positions, including all masks (`app:ch_background:prop:bg-inverse`). -/
theorem hasDerivAt_jointPhysicalPath
    (f : EuclideanSpace ℝ (Fin (2 * d)) → ℂ) (hf : Differentiable ℝ f)
    (i : Fin d) (z : EuclideanSpace ℝ (Fin (2 * d))) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (z + s • jointPhysicalDirection i))
      (euclideanCoordinateDerivList [physicalOutputIndex i] f
          (z + t • jointPhysicalDirection i) +
        euclideanCoordinateDerivList [physicalSourceIndex i] f
          (z + t • jointPhysicalDirection i)) t := by
  have hp := ((hasDerivAt_id t).smul_const (jointPhysicalDirection i)).const_add z
  simpa [jointPhysicalDirection, euclideanCoordinateDerivList, map_add, Function.comp_def] using
    (hf _).hasFDerivAt.comp_hasDerivAt t hp

/-- Fundamental theorem of calculus for the exact divided amplitude, valid
for either sign of the step (`app:ch_background:prop:bg-inverse`). -/
theorem translationDifferenceAmplitude_eq_integral
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (i : Fin d) (h : ℝ)
    (ξ : EuclideanSpace ℝ (Fin d)) (z : EuclideanSpace ℝ (Fin (2 * d))) :
    translationDifferenceAmplitude b i h ξ z =
      h⁻¹ • ∫ t in (0 : ℝ)..h, transferAmplitude b i ξ (z + t • jointPhysicalDirection i) := by
  have hc : Continuous (fun t : ℝ ↦
      transferAmplitude b i ξ (z + t • jointPhysicalDirection i)) :=
    (contDiff_transferAmplitude b hb i ξ).continuous.comp (by fun_prop)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc 0 h) ↦
      hasDerivAt_jointPhysicalPath (b ξ) ((hb ξ).differentiable (by simp)) i z t)
    (hc.intervalIntegrable 0 h)
  simpa [translationDifferenceAmplitude, translatedAmplitude, transferAmplitude] using
    congrArg (fun q : ℂ ↦ h⁻¹ • q) he.symm

/-- A joint physical difference quotient consumes only the two first
coordinate derivatives (`app:ch_background:prop:bg-inverse`). -/
theorem norm_jointPhysicalDifference_le
    (f : EuclideanSpace ℝ (Fin (2 * d)) → ℂ) (hf : ContDiff ℝ ∞ f)
    (i : Fin d) (A : ℝ)
    (ho : ∀ z, ‖euclideanCoordinateDerivList [physicalOutputIndex i] f z‖ ≤ A)
    (hs : ∀ z, ‖euclideanCoordinateDerivList [physicalSourceIndex i] f z‖ ≤ A)
    (h : ℝ) (hh : h ≠ 0) (z : EuclideanSpace ℝ (Fin (2 * d))) :
    ‖h⁻¹ • (f (z + h • jointPhysicalDirection i) - f z)‖ ≤ 2 * A := by
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (x := (0 : ℝ)) (y := h)
    (fun t _ ↦ (hasDerivAt_jointPhysicalPath f (hf.differentiable (by simp)) i z t).hasDerivWithinAt)
    (fun t _ ↦ (norm_add_le _ _).trans (add_le_add (ho _) (hs _)))
    convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simp only [zero_smul, add_zero, sub_zero, Real.norm_eq_abs] at he
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    _ ≤ |h|⁻¹ * ((A + A) * |h|) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = 2 * A := by field_simp; ring

/-- Every required low symbol seminorm of the divided amplitude is uniform
in the nonzero step. The budget is on primitive derivatives of the original
full amplitude (`app:ch_background:prop:bg-inverse`). -/
theorem hasAmplitudeDerivativeBound_translationDifferenceAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (i : Fin d) (N : ℕ) (A : ℝ)
    (hA : HasAmplitudeDerivativeBound b (N + 1) A) (h : ℝ) (hh : h ≠ 0) :
    HasAmplitudeDerivativeBound (translationDifferenceAmplitude b i h) N (2 * A) := by
  intro ξ is his z
  rw [euclideanCoordinateDerivList_translationDifferenceAmplitude b hb]
  apply norm_jointPhysicalDifference_le _ (contDiff_euclideanCoordinateDerivList (hb ξ) is)
    i A _ _ h hh z
  · intro w
    exact hA ξ (physicalOutputIndex i :: is) (by simpa using Nat.add_le_add_right his 1) w
  · intro w
    exact hA ξ (physicalSourceIndex i :: is) (by simpa using Nat.add_le_add_right his 1) w

/-- Joint smoothness of the full divided amplitude, including the frequency
parameter (`app:ch_background:prop:bg-inverse`). -/
theorem contDiff_uncurry_translationDifferenceAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (i : Fin d) (h : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (translationDifferenceAmplitude b i h)) := by
  exact ((hb.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))).sub hb).const_smul _

/-- Each physical coordinate moves by at most the step size
(`app:ch_background:prop:bg-inverse`). -/
theorem abs_jointPhysicalDirection_apply_le (i : Fin d) (j : Fin (2 * d)) :
    |jointPhysicalDirection i j| ≤ 1 := by
  have hne : physicalOutputIndex i ≠ physicalSourceIndex i := by
    intro he
    have hv := congrArg Fin.val he
    simp only [physicalOutputIndex, physicalSourceIndex] at hv
    have hi := i.isLt
    omega
  by_cases ho : j = physicalOutputIndex i
  · subst j
    simp [jointPhysicalDirection, EuclideanSpace.single, hne]
  · by_cases hs : j = physicalSourceIndex i
    · subst j
      simp [jointPhysicalDirection, EuclideanSpace.single, Ne.symm hne]
    · simp [jointPhysicalDirection, EuclideanSpace.single, ho, hs]

/-- A single fixed enlarged box contains every translated amplitude with
`|h| ≤ h₀` (`app:ch_background:prop:bg-inverse`). -/
theorem supportedInCenteredBox_translatedAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (R h₀ : ℝ) (hs : ∀ ξ, SupportedInCenteredBox R (b ξ))
    (i : Fin d) (h : ℝ) (hh : |h| ≤ h₀) (ξ : EuclideanSpace ℝ (Fin d)) :
    SupportedInCenteredBox (R + h₀) (translatedAmplitude b i h ξ) := by
  intro z hz j
  have hs' := hs ξ _ hz j
  have hj : |h * jointPhysicalDirection i j| ≤ h₀ := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (abs_jointPhysicalDirection_apply_le i j)
      (abs_nonneg h)).trans (by simpa using hh)
  change |z j + h * jointPhysicalDirection i j| ≤ R at hs'
  calc
    |z j| = |(z j + h * jointPhysicalDirection i j) - h * jointPhysicalDirection i j| := by ring_nf
    _ ≤ |z j + h * jointPhysicalDirection i j| + |h * jointPhysicalDirection i j| := abs_sub _ _
    _ ≤ R + h₀ := add_le_add hs' hj

/-- The divided amplitude has fixed enlarged support, independent of the
nonzero step (`app:ch_background:prop:bg-inverse`). -/
theorem supportedInCenteredBox_translationDifferenceAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (R h₀ : ℝ) (hs : ∀ ξ, SupportedInCenteredBox R (b ξ))
    (i : Fin d) (h : ℝ) (hh : |h| ≤ h₀) (ξ : EuclideanSpace ℝ (Fin d)) :
    SupportedInCenteredBox (R + h₀) (translationDifferenceAmplitude b i h ξ) := by
  intro z hz j
  by_cases ht : translatedAmplitude b i h ξ z = 0
  · have hb : b ξ z ≠ 0 := by
      intro he
      exact hz (by simp [translationDifferenceAmplitude, ht, he])
    exact (hs ξ z hb j).trans (le_add_of_nonneg_right ((abs_nonneg h).trans hh))
  · exact supportedInCenteredBox_translatedAmplitude b R h₀ hs i h hh ξ z ht j

/-- Periodization of the divided amplitude retains every finite low derivative
bound on the enlarged normalized chart (`app:ch_background:prop:bg-inverse`). -/
theorem norm_periodicDeriv_translationDifferenceAmplitude_le
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (R h₀ : ℝ) (hbox : R + h₀ < 1 / 2)
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (i : Fin d) (N : ℕ) (A : ℝ)
    (hA : HasAmplitudeDerivativeBound b (N + 1) A)
    (h : ℝ) (hh : h ≠ 0) (hsmall : |h| ≤ h₀)
    (ξ : EuclideanSpace ℝ (Fin d)) (is : List (Fin (2 * d))) (his : is.length ≤ N)
    (z : Torus (2 * d)) :
    ‖periodicCoordinateDerivList is
      (amplitudePeriodization (translationDifferenceAmplitude b i h ξ)) z‖ ≤ 2 * A := by
  apply norm_coordinateDerivList_amplitudePeriodization_le hbox
    (supportedInCenteredBox_translationDifferenceAmplitude b R h₀ hs i h hsmall ξ)
    (((hb ξ).comp (contDiff_id.add contDiff_const)).sub (hb ξ) |>.const_smul _) is
  exact hasAmplitudeDerivativeBound_translationDifferenceAmplitude b hb i N A hA h hh ξ is his

/-- Fixed cell cutoffs remove all periodic copies of the divided amplitude.
They remain explicit on both physical positions
(`app:ch_background:prop:bg-inverse`; `app:ch_osc:lem:osc-amplitude`). -/
theorem physicalCellCutoff_translationDifferenceAmplitude_eq
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (R h₀ : ℝ) (hbox : R + h₀ < 1 / 2) (hs : ∀ ξ, SupportedInCenteredBox R (b ξ))
    (i : Fin d) (h : ℝ) (hsmall : |h| ≤ h₀)
    (ξ x y : EuclideanSpace ℝ (Fin d)) :
    physicalCellCutoff x *
      amplitudePeriodization (translationDifferenceAmplitude b i h ξ)
        (leftPositionChart 1 x + rightPositionChart 1 y) * physicalCellCutoff y =
      translationDifferenceAmplitude b i h ξ (pairedPosition x y) :=
  physicalCellCutoff_amplitudePeriodization_eq hbox
    (supportedInCenteredBox_translationDifferenceAmplitude b R h₀ hs i h hsmall ξ) x y

/-- Translation preserves joint smoothness of the literal full amplitude
(`app:ch_background:prop:bg-inverse`). -/
theorem contDiff_uncurry_translatedAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (i : Fin d) (h : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (translatedAmplitude b i h)) :=
  hb.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))

/-- Translation preserves the original primitive derivative budget
(`app:ch_background:prop:bg-inverse`). -/
theorem hasAmplitudeDerivativeBound_translatedAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (i : Fin d) (N : ℕ) (A : ℝ) (hA : HasAmplitudeDerivativeBound b N A) (h : ℝ) :
    HasAmplitudeDerivativeBound (translatedAmplitude b i h) N A := by
  intro ξ is his z
  change ‖euclideanCoordinateDerivList is (fun w ↦ b ξ (w + h • jointPhysicalDirection i)) z‖ ≤ A
  rw [euclideanCoordinateDerivList_translate]
  exact hA ξ is his _

end JanetCartan.ContinuumCommutator
