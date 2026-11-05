module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputDilation.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition

/-!
# Dilation after reassembling an original smooth band

The input to the slice calculus of `app:ch_waves:eq:individual-raw-slice`
is one original wide band, not either of its sharp measurable refinements.
We conjugate the actual annular pullbacks by the checked two-piece Hilbert
identification. The resulting unitary is the literal Jacobian-weighted
pullback on the whole wide band. Its integral formula keeps the physical
Fourier normalization and the exact shifted phase quotient.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.RawPrimary.SliceBounds
open RawInputRealization RawInputPartition RawInputDilation

variable {n : ℕ}

/-- The annular unitary underlying the reassembled wide-band dilation.
This is the same `annularPullback` as in `RawInputDilation.annularDilation`,
with the base radius of the two sharp components retained
(`app:ch_waves:thm:individual`). -/
def sharpBandDilation (n j : ℕ) (b : Fin 2) :
    AnnularL2 n ((2 : ℝ) ^ (j + b.val)) ≃ₗᵢ[ℂ]
      AnnularL2 n ((2 : ℝ) ^ (0 + b.val)) := by
  let hK : 0 < (2 : ℝ) ^ j := by positivity
  let hS : (2 : ℝ) ^ (j + b.val) = (2 : ℝ) ^ j * (2 : ℝ) ^ (0 + b.val) := by
    simp [pow_add]
  let hR : (2 : ℝ) ^ (0 + b.val) = ((2 : ℝ) ^ j)⁻¹ * (2 : ℝ) ^ (j + b.val) := by
    rw [hS, ← mul_assoc, inv_mul_cancel₀ hK.ne', one_mul]
  exact
    { toLinearEquiv :=
        { annularPullbackLinear hK hS with
          invFun := annularPullback (inv_pos.mpr hK) hR
          left_inv := annularPullback_inverse hK hS hR
          right_inv := fun g ↦ by
            change annularPullback hK hS (annularPullback (inv_pos.mpr hK) hR g) = g
            simpa only [inv_inv] using annularPullback_inverse (inv_pos.mpr hK) hR
              (by simpa only [inv_inv] using hS) g }
      norm_map' := annularPullback_norm hK hS }

/-- Almost-everywhere formula before reassembly; no regularity of a sharp
indicator is used (`app:ch_waves:thm:individual`). -/
theorem sharpBandDilation_apply_ae (j : ℕ) (b : Fin 2)
    (f : AnnularL2 n ((2 : ℝ) ^ (j + b.val))) :
    sharpBandDilation n j b f =ᵐ[annularMeasure n ((2 : ℝ) ^ (0 + b.val))]
      fun θ ↦ (Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) : ℂ) * f ((2 : ℝ) ^ j • θ) :=
  by
    change (annularPullback (show 0 < (2 : ℝ) ^ j by positivity)
      (show (2 : ℝ) ^ (j + b.val) = (2 : ℝ) ^ j * (2 : ℝ) ^ (0 + b.val) by
        simp [pow_add]) f) =ᵐ[_] _
    exact MemLp.coeFn_toLp _

/-- The actual unitary on the ORIGINAL wide datum. Both sharp pieces are
reassembled before any symbol calculus (`app:ch_waves:eq:individual-raw-slice`). -/
def wideBandDilation (n j : ℕ) : WideBandL2 n j ≃ₗᵢ[ℂ] WideBandL2 n 0 :=
  ((bandRefinement n j).trans
    (LinearIsometryEquiv.piLpCongrRight 2 (sharpBandDilation n j))).trans
      (bandRefinement n 0).symm

/-- Dilation preserves the literal complex Hilbert norm, including both real
quadratures (`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_wideBandDilation (j : ℕ) (f : WideBandL2 n j) :
    ‖wideBandDilation n j f‖ = ‖f‖ := (wideBandDilation n j).norm_map f

/-- Restricting the reassembled datum recovers the two dilated pieces
(`app:ch_waves:thm:individual`). -/
theorem bandRestriction_wideBandDilation (j : ℕ) (f : WideBandL2 n j) (b : Fin 2) :
    bandRestriction n 0 (wideBandDilation n j f) b =
      sharpBandDilation n j b (bandRestriction n j f b) := by
  have h := (bandRefinement n 0).apply_symm_apply
    (LinearIsometryEquiv.piLpCongrRight 2 (sharpBandDilation n j)
      (bandRefinement n j f))
  exact congrArg (fun v : BandPair n 0 ↦ v b) h

/-- The reassembled unitary is the literal pullback on the complete wide
band, not just on a smaller high-pass annulus
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem wideBandDilation_apply_ae (j : ℕ) (f : WideBandL2 n j) :
    wideBandDilation n j f =ᵐ[volume.restrict (wideBand n 0)]
      fun θ ↦ (Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) : ℂ) * f ((2 : ℝ) ^ j • θ) := by
  have hpiece (b : Fin 2) :
      wideBandDilation n j f =ᵐ[annularMeasure n ((2 : ℝ) ^ (0 + b.val))]
        fun θ ↦ (Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) : ℂ) * f ((2 : ℝ) ^ j • θ) := by
    have he : (2 : ℝ) ^ j * (2 : ℝ) ^ (0 + b.val) = (2 : ℝ) ^ (j + b.val) := by
      simp [pow_add]
    have ha := ae_annular_smul (n := n) (K := (2 : ℝ) ^ j) (by positivity)
      ((2 : ℝ) ^ (0 + b.val))
      (ae_mono (le_of_eq (congrArg (annularMeasure n) he)) (bandRestriction_coeFn n j f b))
    have hb := sharpBandDilation_apply_ae j b (bandRestriction n j f b)
    rw [← bandRestriction_wideBandDilation] at hb
    filter_upwards [bandRestriction_coeFn n 0 (wideBandDilation n j f) b, hb, ha]
      with θ h₁ h₂ h₃
    exact h₁.symm.trans (h₂.trans (congrArg
      (fun z : ℂ ↦ (Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) : ℂ) * z) h₃))
  have hu := (ae_restrict_union_iff _ _ _).mpr ⟨hpiece 0, hpiece 1⟩
  exact ae_mono (le_of_eq (congrArg (fun s ↦ volume.restrict s) (wideBand_eq_union n 0))) hu

/-- Exact pullback of the whole smooth-band domain
(`app:ch_waves:thm:individual`). -/
theorem preimage_wideBand_smul (n j : ℕ) :
    (fun θ : Euclidean (n - 1) ↦ (2 : ℝ) ^ j • θ) ⁻¹' wideBand n j = wideBand n 0 := by
  rw [wideBand_eq_union, wideBand_eq_union, Set.preimage_union]
  have h (b : Fin 2) : (2 : ℝ) ^ (j + b.val) =
      (2 : ℝ) ^ j * (2 : ℝ) ^ (0 + b.val) := by simp [pow_add]
  rw [h 0, h 1, preimage_annulus_smul (by positivity),
    preimage_annulus_smul (by positivity)]

/-- The original wide-band measure has the same actual Jacobian as its
sharp components (`app:ch_waves:eq:individual-raw-slice`). -/
theorem map_wideBandMeasure_smul (n j : ℕ) :
    (volume.restrict (wideBand n 0)).map (fun θ ↦ (2 : ℝ) ^ j • θ) =
      ENNReal.ofReal ((((2 : ℝ) ^ j) ^ (n - 1))⁻¹) • volume.restrict (wideBand n j) := by
  rw [← preimage_wideBand_smul n j, ← Measure.restrict_map (by fun_prop)
    (measurableSet_wideBand n j), Measure.map_addHaar_smul volume (by positivity)]
  simp only [Euclidean, finrank_euclideanSpace_fin,
    abs_of_pos (show 0 < (((2 : ℝ) ^ j) ^ (n - 1))⁻¹ by positivity),
    Measure.restrict_smul]

/-- Exact Bochner substitution on the reassembled wide band, for the integral
identification in `app:ch_waves:eq:individual-raw-slice`. -/
theorem integral_wideBand_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (f : Euclidean (n - 1) → E) :
    (∫ θ in wideBand n 0, f ((2 : ℝ) ^ j • θ)) =
      (((2 : ℝ) ^ j) ^ (n - 1))⁻¹ • ∫ η in wideBand n j, f η := by
  let e := (Homeomorph.smul (Units.mk0 ((2 : ℝ) ^ j) (by positivity)) :
    Euclidean (n - 1) ≃ₜ Euclidean (n - 1)).toMeasurableEquiv
  have he : ⇑e = (fun θ : Euclidean (n - 1) ↦ (2 : ℝ) ^ j • θ) := rfl
  change (∫ θ in wideBand n 0, f (e θ)) = _
  rw [← integral_map_equiv e f, he, map_wideBandMeasure_smul,
    integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- Half-derivative substitution on the reassembled smooth band. The fixed
domain is `[1/2,2]`, and the oscillatory frequency is `2^j ≥ 1`, including the
bottom band (`app:ch_waves:eq:individual-raw-slice`). -/
theorem halfDerivative_wideBand_integral_dilation (hn : 1 ≤ n) (j : ℕ)
    (b : Euclidean (n - 1) → ℂ) (a : Euclidean (n - 1) → E)
    (f : WideBandL2 n j) :
    (∫ η in wideBand n j, ((Real.sqrt ‖η‖ : ℂ) * b η * f η) • a η) =
      (((2 : ℝ) ^ j) ^ ((n : ℝ) / 2) : ℝ) •
        ∫ θ in wideBand n 0,
          ((Real.sqrt ‖θ‖ : ℂ) * b ((2 : ℝ) ^ j • θ) * wideBandDilation n j f θ) •
            a ((2 : ℝ) ^ j • θ) := by
  have hsub := integral_wideBand_smul j
    (fun η ↦ ((Real.sqrt ‖η‖ : ℂ) * b η * f η) • a η)
  calc
    _ = ((2 : ℝ) ^ j) ^ (n - 1) •
        ∫ θ in wideBand n 0,
          ((Real.sqrt ‖(2 : ℝ) ^ j • θ‖ : ℂ) * b ((2 : ℝ) ^ j • θ) *
            f ((2 : ℝ) ^ j • θ)) • a ((2 : ℝ) ^ j • θ) := by
      rw [hsub, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
    _ = _ := by
      rw [← integral_smul, ← integral_smul]
      apply integral_congr_ae
      filter_upwards [wideBandDilation_apply_ae j f] with θ hθ
      rw [hθ, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j),
        Real.sqrt_mul (by positivity)]
      simp only [Complex.ofReal_mul, ← smul_assoc, Complex.real_smul]
      congr 1
      have hscalar : ((((2 : ℝ) ^ j) ^ (n - 1) : ℝ) : ℂ) *
          (Real.sqrt ((2 : ℝ) ^ j) : ℂ) =
          ((((2 : ℝ) ^ j) ^ ((n : ℝ) / 2) : ℝ) : ℂ) *
            (Real.sqrt (((2 : ℝ) ^ j) ^ (n - 1)) : ℂ) := by
        exact_mod_cast jacobian_mul_sqrt hn (by positivity : 0 < (2 : ℝ) ^ j)
      linear_combination
        (Real.sqrt ‖θ‖ : ℂ) * b ((2 : ℝ) ^ j • θ) * f ((2 : ℝ) ^ j • θ) * hscalar

/-- The exact normalized raw quotient integral after wide-band dilation.
The physical Fourier scalar, the half derivative, the original mask, and
the parameter `τ * 2^j` are all retained
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem normalized_wideBand_rawPrimary_integral {X : Type*}
    (hn : 1 ≤ n) (j : ℕ) {τ : ℝ} (hτ : τ ≠ 0)
    (S : X → Euclidean (n - 1) → ℝ) (ζ : Euclidean (n - 1)) (x : X)
    (β : Euclidean (n - 1) → ℂ) (a : Euclidean (n - 1) → E)
    (f : WideBandL2 n j) :
    (2 * Real.pi) ^ (-(n : ℝ) / 2) •
      (∫ η in wideBand n j, ((Real.sqrt ‖η‖ : ℂ) *
        (Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℂ)) * β η) *
          f η) • a η) =
    NormalComparison.normalOperatorScale n ((2 : ℝ) ^ j) •
      ∫ θ in wideBand n 0, ((Real.sqrt ‖θ‖ : ℂ) *
        (NormalComparison.oscillatoryFactor ((2 : ℝ) ^ j)
          (rawPrimaryPhaseDifference S ζ (τ * (2 : ℝ) ^ j) x θ) * β ((2 : ℝ) ^ j • θ)) *
            wideBandDilation n j f θ) • a ((2 : ℝ) ^ j • θ) := by
  rw [halfDerivative_wideBand_integral_dilation hn j, smul_smul,
    fourierScalar_mul_dilationScale (by positivity)]
  simp only [rawPrimaryPhaseDifference_dilate S ζ hτ (show 0 < (2 : ℝ) ^ j by positivity),
    NormalComparison.oscillatoryFactor, Complex.ofReal_mul]

end JanetCartan.RawPrimary.SliceBounds
