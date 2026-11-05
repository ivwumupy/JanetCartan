module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.ExactCommutator

/-!
# Literal Schwartz commutator and its localization defect

For `app:ch_background:prop:bg-frame`, Step 1, keep the actual Bessel multiplier,
its commutator with the source square, and the next Bessel factor as operators on
Schwartz tests. Plancherel proves the reversed formal adjoint. An intermediate
source mask produces an explicit tail; it is never inserted as an identity.
These identities are consumed by the differential sandwich in `TestOperator`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff
open JanetCartan.Pseudodifferential
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => 𝓢(E, ℂ)

/-- The literal `J` on Schwartz space, with physical covector `2πξ`
(`app:ch_background:prop:bg-frame`, Step 1). -/
def imageBesselSchwartzCLM : S →L[ℂ] S :=
  (FourierTransform.fourierInvCLM ℂ S).comp
    ((SchwartzMap.smulLeftCLM ℂ (fun ξ : E ↦ (imageBesselSymbol ξ : ℂ))).comp
      (FourierTransform.fourierCLM ℂ S))

/-- Agreement with the shared literal Fourier multiplier
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageBesselSchwartzCLM_apply (u : S) :
    imageBesselSchwartzCLM u =
      schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u := rfl

/-- The literal source-square commutator `[J,χ²]` on Schwartz tests
(`app:ch_background:prop:bg-frame`, Step 1). -/
def imageSourceSquareCommutator (χ : E → ℝ) : S →L[ℂ] S :=
  imageBesselSchwartzCLM.comp (SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ))) -
    (SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ))).comp imageBesselSchwartzCLM

/-- The actual source commutator, including its pointwise output cutoff
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageSourceSquareCommutator_apply (χ : E → ℝ)
    (hχ : χ.HasTemperateGrowth) (u : S) (x : E) :
    imageSourceSquareCommutator χ u x =
      imageBesselSchwartzCLM
        (SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ)) u) x -
      (χ x)^2 • imageBesselSchwartzCLM u x := by
  have hsq : (fun y ↦ ((χ y)^2 : ℂ)).HasTemperateGrowth := by fun_prop
  simp [imageSourceSquareCommutator, SchwartzMap.smulLeftCLM_apply_apply hsq,
    Complex.real_smul, Complex.ofReal_pow]

/-- Lebesgue Hermitian pairing of scalar Schwartz tests, used only to prove
literal adjoints in `app:ch_background:prop:bg-frame`, Step 1. -/
def imageSchwartzPairing (u v : S) : ℂ := inner ℂ (u.toLp 2) (v.toLp 2)

/-- The pairing is the Euclidean Lebesgue integral, with no periodic measure
identification (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageSchwartzPairing_eq_integral (u v : S) :
    imageSchwartzPairing u v = ∫ x, star (u x) * v x := by
  simp only [imageSchwartzPairing, SchwartzMap.inner_toL2_toL2_eq, RCLike.inner_apply']
  rfl

private theorem pairing_sub_left (u v w : S) :
    imageSchwartzPairing (u - v) w = imageSchwartzPairing u w - imageSchwartzPairing v w := by
  change inner ℂ ((SchwartzMap.toLpCLM ℂ ℂ 2) (u - v)) (w.toLp 2) = _
  rw [map_sub, inner_sub_left]
  rfl

private theorem pairing_sub_right (u v w : S) :
    imageSchwartzPairing u (v - w) = imageSchwartzPairing u v - imageSchwartzPairing u w := by
  change inner ℂ (u.toLp 2) ((SchwartzMap.toLpCLM ℂ ℂ 2) (v - w)) = _
  rw [map_sub, inner_sub_right]
  rfl

/-- Plancherel and the real symbol prove the actual Schwartz multiplier is
self-adjoint (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageBesselSchwartzCLM_pairing (u v : S) :
    imageSchwartzPairing (imageBesselSchwartzCLM u) v =
      imageSchwartzPairing u (imageBesselSchwartzCLM v) := by
  unfold imageSchwartzPairing
  rw [← SchwartzMap.inner_fourier_toL2_eq (imageBesselSchwartzCLM u) v,
    ← SchwartzMap.inner_fourier_toL2_eq u (imageBesselSchwartzCLM v)]
  simp only [SchwartzMap.inner_toL2_toL2_eq]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [imageBesselSchwartzCLM_apply, fourier_imageBesselMultiplier,
    RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

private theorem realMask_pairing (f : E → ℝ) (hf : f.HasTemperateGrowth) (u v : S) :
    imageSchwartzPairing (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (f x : ℂ)) u) v =
      imageSchwartzPairing u (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (f x : ℂ)) v) := by
  have hc : (fun x ↦ (f x : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [imageSchwartzPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [SchwartzMap.smulLeftCLM_apply_apply hc, smul_eq_mul, star_mul,
    Complex.star_def, Complex.conj_ofReal]
  ring

/-- The literal commutator is skew-adjoint on Euclidean Schwartz tests
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageSourceSquareCommutator_pairing (χ : E → ℝ)
    (hχ : χ.HasTemperateGrowth) (u v : S) :
    imageSchwartzPairing (imageSourceSquareCommutator χ u) v =
      -imageSchwartzPairing u (imageSourceSquareCommutator χ v) := by
  have hsq : (fun y ↦ (χ y)^2).HasTemperateGrowth := by fun_prop
  change imageSchwartzPairing
    (imageBesselSchwartzCLM (SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ)) u) -
      SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ)) (imageBesselSchwartzCLM u)) v =
    -imageSchwartzPairing u
    (imageBesselSchwartzCLM (SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ)) v) -
      SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ)) (imageBesselSchwartzCLM v))
  simp only [← Complex.ofReal_pow]
  rw [pairing_sub_left, pairing_sub_right, imageBesselSchwartzCLM_pairing,
    realMask_pairing _ hsq, realMask_pairing _ hsq, imageBesselSchwartzCLM_pairing]
  ring

/-- Reversing the actual two-factor error gives `-[J,χ²]` after `J`, namely
`([J,χ²]J)* = -J[J,χ²]` (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageSourceSquareCommutator_rightBessel_pairing (χ : E → ℝ)
    (hχ : χ.HasTemperateGrowth) (u v : S) :
    imageSchwartzPairing (imageSourceSquareCommutator χ (imageBesselSchwartzCLM u)) v =
      -imageSchwartzPairing u (imageBesselSchwartzCLM (imageSourceSquareCommutator χ v)) := by
  rw [imageSourceSquareCommutator_pairing χ hχ, imageBesselSchwartzCLM_pairing]

/-- The exact error caused by an intermediate source mask. The second term
is retained as the off-diagonal tail in `app:ch_background:prop:bg-frame`,
Step 1. No localization identity for `J u` is assumed. -/
theorem imageSourceSquareCommutator_localization (χ β : E → ℝ)
    (hχ : χ.HasTemperateGrowth) (hβ : β.HasTemperateGrowth)
    (hplateau : ∀ y, χ y ≠ 0 → β y = 1) (u : S) :
    imageSourceSquareCommutator χ u =
      imageSourceSquareCommutator χ (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (β y : ℂ)) u) -
      SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ))
        (imageBesselSchwartzCLM (u - SchwartzMap.smulLeftCLM ℂ (fun y ↦ (β y : ℂ)) u)) := by
  have hsq : (fun y ↦ ((χ y)^2 : ℂ)).HasTemperateGrowth := by fun_prop
  have hb : (fun y ↦ (β y : ℂ)).HasTemperateGrowth := by fun_prop
  have he : SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ))
      (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (β y : ℂ)) u) =
      SchwartzMap.smulLeftCLM ℂ (fun y ↦ ((χ y)^2 : ℂ)) u := by
    ext y
    simp only [SchwartzMap.smulLeftCLM_apply_apply hsq,
      SchwartzMap.smulLeftCLM_apply_apply hb, smul_eq_mul]
    by_cases hy : χ y = 0
    · simp [hy]
    · simp [hplateau y hy]
  simp only [imageSourceSquareCommutator, sub_apply,
    ContinuousLinearMap.comp_apply, map_sub, he]
  abel

end JanetCartan.ContinuumNormalReduction.ImageNormal
