module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.BandRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.GradedSum
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.IntegralSum

/-!
# Differentiated reassembly on the original wide input

The graded sum of the constructed branch channels is the derivative of the
SAME full raw integral, rather than a new Sobolev realization. The identities
retain the original smooth bands and Fourier normalization
(`app:ch_waves:eq:individual-raw-slice`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.RawPrimary.SliceBounds
open RawInputPartition NormalComparison

variable {d r J s : ℕ}
local notation "Y" => Euclidean d
local notation "X" => ℝ × Y
local notation "Vₒ" => EuclideanSpace ℂ (Fin r)

private theorem gradedWideBandOperatorSum_coeFn
    (T : SliceDerivativeBranch s → (j : Fin J) →
      WideBandL2 (d + 1) j.val →L[ℂ] Lp Vₒ 2 (volume : Measure X))
    (L : ℝ) (f : WideInput (d + 1) J)
    (g : SliceDerivativeBranch s → Fin J → X → Vₒ)
    (hg : ∀ b j, T b j (f j) =ᵐ[volume] g b j) :
    gradedWideBandOperatorSum T L f =ᵐ[volume] fun x ↦
      ∑ b : SliceDerivativeBranch s, ∑ j : Fin J,
        (((2 : ℝ) ^ j.val) ^ b.phaseCount * L ^ (s - b.phaseCount)) • g b j x := by
  rw [gradedWideBandOperatorSum_apply]
  refine (Lp.coeFn_finsetSum Finset.univ _).trans ?_
  have h (b : SliceDerivativeBranch s) :
      (∑ j : Fin J, (((2 : ℝ) ^ j.val) ^ b.phaseCount * L ^ (s - b.phaseCount)) • T b j (f j))
        =ᵐ[volume] fun x ↦ ∑ j : Fin J,
          (((2 : ℝ) ^ j.val) ^ b.phaseCount * L ^ (s - b.phaseCount)) • g b j x := by
    refine (Lp.coeFn_finsetSum Finset.univ _).trans ?_
    have h' (j : Fin J) := (Lp.coeFn_smul
      (((2 : ℝ) ^ j.val) ^ b.phaseCount * L ^ (s - b.phaseCount)) (T b j (f j))).trans
        ((hg b j).fun_comp (fun z ↦ (((2 : ℝ) ^ j.val) ^ b.phaseCount * L ^ (s - b.phaseCount)) • z))
    filter_upwards [eventuallyEq_sum (s := Finset.univ) (fun j _ ↦ h' j)] with x hx
    simpa only [Finset.sum_apply, Function.comp_apply] using hx
  filter_upwards [eventuallyEq_sum (s := Finset.univ) (fun b _ ↦ h b)] with x hx
  simpa only [Finset.sum_apply] using hx

/-- The finite graded sum of actual normalized branch operators represents
physical differentiation of the original full wide-density field. The
operator representatives are supplied by
`exists_rawSliceNormalizedBranchOperators`; all differentiation, integral
reassembly and support arguments are proved here
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem gradedWideBandOperatorSum_coeFn_rawSliceDerivative
    {U : Set X} {V Ω : Set Y} {Q : Set (ℝ × X × Y)} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hΩ : IsOpen Ω) (hQ : IsOpen Q) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hband : wideBand (d + 1) 0 ⊆ Ω)
    {S : X → Y → ℝ} {A : X → Y → Vₒ} {χ : X → ℝ} {ζ : Y} {τ L : ℝ}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    (hχ : ContDiffOn ℝ ∞ χ U) (hχU : tsupport χ ⊆ U) (hζ : ζ ∈ V)
    (hτ : τ ≠ 0) (hL : 0 < L) {mask : Y → ℂ} {M : ℝ}
    (hmask : Measurable mask) (hmaskb : ∀ η, ‖mask η‖ ≤ M)
    (hm : ∀ j : Fin J, ContDiffOn ℝ ∞
      (fun θ ↦ (Real.sqrt ‖θ‖ : ℂ) * weightedRadialBand (n := d + 1) mask j.val
        ((2 : ℝ) ^ j.val • θ)) Ω)
    (hshift : ∀ t ∈ W, MapsTo (rawSliceShift ζ t) Q (U ×ˢ V))
    (hθ : ∀ q ∈ Q, q.2.2 ∈ Ω)
    (hstrip : ∀ j : Fin J, ∀ x ∈ U, ∀ θ ∈ Ω, (τ * (2 : ℝ) ^ j.val, x, θ) ∈ Q)
    (hshiftBand : ∀ j : Fin J, ∀ θ ∈ Ω, ζ + (τ * (2 : ℝ) ^ j.val) • θ ∈ V)
    (hshiftOriginal : ∀ j : Fin J, ∀ (η : Y), η ∈ wideBand (d + 1) j.val → ζ + τ • η ∈ V)
    (v : Fin s → X)
    (T : SliceDerivativeBranch s → (j : Fin J) →
      WideBandL2 (d + 1) j.val →L[ℂ] Lp Vₒ 2 (volume : Measure X))
    (hT : ∀ b j f, T b j f =ᵐ[volume]
      rawSliceNormalizedBranchIntegral (n := d + 1) S A χ
        (fun θ ↦ (Real.sqrt ‖θ‖ : ℂ) * weightedRadialBand (n := d + 1) mask j.val
          ((2 : ℝ) ^ j.val • θ)) ζ (τ * (2 : ℝ) ^ j.val) j.val v b L f)
    (f : WideInput (d + 1) J) :
    gradedWideBandOperatorSum T L f =ᵐ[volume] fun x ↦
      iteratedFDeriv ℝ s (fun y ↦ (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) •
        ((χ y : ℂ) • rawPrimaryDemodulatedIntegral S A ζ τ volume
          (weightedWideDensity (n := d + 1) mask f) y)) x v := by
  refine (gradedWideBandOperatorSum_coeFn T L f _ (fun b j ↦ hT b j (f j))).trans
    (Filter.Eventually.of_forall ?_)
  intro x
  let g (j : Fin J) (y : X) := (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) •
    rawSliceBandIntegral (n := d + 1) S A χ ζ τ (weightedRadialBand (n := d + 1) mask j.val) j.val (f j) y
  have hg (j : Fin J) : ContDiff ℝ ∞ (g j) :=
    contDiff_normalized_rawSliceBandIntegral (n := d + 1) (by omega) hU hΩ hband hS hA hχ hχU hζ hτ
      _ j.val (fun η hη ↦ weightedRadialBand_eq_zero_off_wideBand (n := d + 1) mask hη)
      (hm j) (hshiftBand j) (f j)
  have he : (fun y ↦ (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) •
      ((χ y : ℂ) • rawPrimaryDemodulatedIntegral S A ζ τ volume
        (weightedWideDensity (n := d + 1) mask f) y)) = fun y ↦ ∑ j : Fin J, g j y := by
    funext y
    simp only [g, ← Finset.smul_sum]
    congr 1
    symm
    apply sum_rawSliceBandIntegral_eq_weightedWideDensity (n := d + 1) S A χ ζ τ hmask hmaskb f y
    intro hy j
    have hyU := hχU (subset_tsupport χ hy)
    exact ((contDiffOn_rawPrimaryDemodulatedAtom hS hA hζ (hshiftOriginal j)).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun η hη ↦ ⟨hyU, hη⟩)).continuousOn
  rw [he]
  dsimp only
  rw [iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := s) (x := x) (u := Finset.univ)
    (fun j _ ↦ (hg j).contDiffAt.of_le (by simp)), sum_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (iteratedFDeriv_normalized_rawSliceBandIntegral_eq_normalizedBranches (n := d + 1)
    (by omega) hU hV hΩ hQ hW hIW hband hS hA hχ hχU hζ hτ
    _ j.val (fun η hη ↦ weightedRadialBand_eq_zero_off_wideBand (n := d + 1) mask hη)
    (hm j) hshift hθ (hstrip j) (f j) s x v hL).symm

end JanetCartan.RawPrimary.SliceBounds
