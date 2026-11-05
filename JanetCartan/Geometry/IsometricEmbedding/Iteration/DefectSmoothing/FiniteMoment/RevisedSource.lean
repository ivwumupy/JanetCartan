module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.FiniteMoment
public import JanetCartan.Geometry.IsometricEmbedding.Scales.Revised

/-!
# The actual finite-moment source at the revised fixed Sobolev order

The target contribution in Step 3 of `app:prop:ordered-scale-selection` is
not just a numerical power comparison. The same real finite-moment output
is normalized with the revised forcing exponent and has all of its analytic
properties proved from original source smoothness and defect smallness.

The fixed support and general profile precede every varying input. At the
revised order `s₀ > n`, both norms are bounded by `C R⁻¹`, hence `C R^(-β)`.
This closes the normalized target input, not the remaining same-family
sampling background or the complete source iteration in `main:prop:mean`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.DefectSmoothing
open BallSmoothing LocalSobolev

/-- The literal finite-moment target normalized by the REVISED forcing scale.
This is the source in `paper-v2.tex`, `main:lem:smoothing` and Step 3 of
`app:prop:ordered-scale-selection`, not the legacy periodic source. -/
def revisedFiniteMomentSource {n : ℕ} (D : LocalDomain) (R : ℝ) (m : ℕ)
    (δ : ℝ) (e : MetricField n) : MetricField n :=
  ((δ * R ^ RevisedScales.forcingExponent n) ^ 2)⁻¹ • finiteMomentTensor D R m e

/-- The actual normalized target in the revised fixed source order.

One compact support, threshold and all profile constants precede the source,
frequency and defect size. Only original tensor smoothness and the genuine
zeroth defect bound are inputs. The SAME source is globally smooth, has finite
Sobolev jets, preserves symmetry, satisfies the full derivative profile, and
has `C^s₀ + H^s₀ ≤ C R⁻¹ ≤ C R^(-β)` with the paper's `s₀ > n`.

This instantiates the actual finite-moment producer and the revised forcing
order; it does not assume a normalized-source estimate or construct the
remaining sampling background of `main:prop:mean`. -/
theorem exists_revisedFiniteMomentSource_bounds {n : ℕ} (D : LocalDomain)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ (K : Set (Euclidean n)) (Rmin : ℝ) (L : ℕ → ℝ),
      IsCompact K ∧ K ⊆ D.chart n ∧ 1 ≤ Rmin ∧ (2 : ℝ) * m ≤ Rmin ∧
      (∀ r, 0 ≤ L r) ∧ n < RevisedScales.sourceOrder n ∧
      ∀ R : ℝ, Rmin ≤ R → ∀ e : MetricField n,
        ContDiffOn ℝ ∞ e (D.chart n) → ∀ δ : ℝ, 0 < δ →
        cNorm (D.core n) 0 e ≤ δ ^ 2 →
        let source := revisedFiniteMomentSource D R m δ e
        ContDiff ℝ ∞ source ∧ tsupport source ⊆ K ∧ HasCompactSupport source ∧
        ((∀ x ∈ D.core n, (e x).IsSymm) → ∀ x, (source x).IsSymm) ∧
        (∀ r, MemLp (iteratedFDeriv ℝ r source) 2 volume) ∧
        (∀ r, cNorm univ r source +
          cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j source) ≤
            L r * R ^ ((r : ℝ) - 2 * RevisedScales.forcingExponent n)) ∧
        (cNorm univ (RevisedScales.sourceOrder n) source +
          cartesianJetNorm univ (RevisedScales.sourceOrder n)
            (fun j ↦ iteratedFDeriv ℝ j source) ≤
              L (RevisedScales.sourceOrder n) * R ^ (-1 : ℝ)) ∧
        (cNorm univ (RevisedScales.sourceOrder n) source +
          cartesianJetNorm univ (RevisedScales.sourceOrder n)
            (fun j ↦ iteratedFDeriv ℝ j source) ≤
              L (RevisedScales.sourceOrder n) * R ^ (-separationExponent)) := by
  obtain ⟨K, Rg, hK, hKD, hRg, hsupp⟩ :=
    exists_affineSmoothing_fixed_support (F := MetricTensor n) (0 : Euclidean n)
      D.coreRadius_pos isOpen_ball (closedBall_subset_ball D.coreRadius_lt_chartRadius)
  obtain ⟨Rn, L, hRn, hRm, hL, hb⟩ := exists_finiteMoment_normalized_bounds (n := n) D m hm
  refine ⟨K, max Rg Rn, L, hK, hKD, hRg.trans (le_max_left _ _),
    hRm.trans (le_max_right _ _), hL, (RevisedScales.source_order_and_forcing_gap n).2.1, ?_⟩
  intro R hR e he δ hδ hsmall
  dsimp only
  have hRnorm : Rn ≤ R := (le_max_right _ _).trans hR
  have hRgeom : Rg ≤ R := (le_max_left _ _).trans hR
  have hRone : 1 ≤ R := hRn.trans hRnorm
  have hRorder : (2 : ℝ) * m ≤ R := hRm.trans hRnorm
  have hecore : ContinuousOn e (D.core n) :=
    he.continuousOn.mono (closedBall_subset_ball D.coreRadius_lt_chartRadius)
  have hu : ContDiff ℝ ∞ (finiteMomentTensor D R m e) :=
    contDiff_affineSmoothing 0 D.coreRadius_pos hm hRorder hecore
  have hsource : ContDiff ℝ ∞ (revisedFiniteMomentSource D R m δ e) :=
    hu.const_smul (((δ * R ^ RevisedScales.forcingExponent n) ^ 2)⁻¹)
  have hsupport : tsupport (revisedFiniteMomentSource D R m δ e) ⊆ K :=
    (tsupport_smul_subset_right
      (fun _ : Euclidean n ↦ ((δ * R ^ RevisedScales.forcingExponent n) ^ 2)⁻¹)
      (finiteMomentTensor D R m e)).trans (hsupp R hRgeom m e)
  have hcompact : HasCompactSupport (revisedFiniteMomentSource D R m δ e) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hsupport
  have hprofile := hb R hRnorm e he δ hδ hsmall (RevisedScales.forcingExponent n)
  have hpower := RevisedScales.normalized_target_power_le n hRone
  refine ⟨hsource, hsupport, hcompact, ?_,
    fun r ↦ memLp_iteratedFDeriv_of_contDiff_hasCompactSupport hsource hcompact r,
    hprofile, ?_, ?_⟩
  · intro hsym x
    exact (finiteMomentTensor_isSymm D hm hRorder hecore hsym x).smul
      (((δ * R ^ RevisedScales.forcingExponent n) ^ 2)⁻¹)
  · exact (hprofile (RevisedScales.sourceOrder n)).trans_eq
      (congrArg (fun p : ℝ ↦ L (RevisedScales.sourceOrder n) * p) hpower.1)
  · exact (hprofile (RevisedScales.sourceOrder n)).trans
      (mul_le_mul_of_nonneg_left hpower.2 (hL _))

/-- One ORIGINAL compact source carrier is chosen before the approximation
order or accuracy. For each later `m ≥ 1`, the same revised finite-moment source
has all the existing analytic bounds after enlarging its frequency threshold.

This is the quantifier order needed to fix `B_F`, the source cutoff and its
domains before accuracy in the Section 15 source admission. The geometric
support producer already precedes every order; the analytic estimates are
reused unchanged from `exists_revisedFiniteMomentSource_bounds`. -/
theorem exists_revisedFiniteMomentSource_common_support {n : ℕ} (D : LocalDomain) :
    ∃ (K : Set (Euclidean n)) (Rgeom : ℝ),
      IsCompact K ∧ K ⊆ D.chart n ∧ 1 ≤ Rgeom ∧
      ∀ m : ℕ, 1 ≤ m → ∃ (Rmin : ℝ) (L : ℕ → ℝ),
        Rgeom ≤ Rmin ∧ 1 ≤ Rmin ∧ (2 : ℝ) * m ≤ Rmin ∧
        (∀ r, 0 ≤ L r) ∧ n < RevisedScales.sourceOrder n ∧
        ∀ R : ℝ, Rmin ≤ R → ∀ e : MetricField n,
          ContDiffOn ℝ ∞ e (D.chart n) → ∀ δ : ℝ, 0 < δ →
          cNorm (D.core n) 0 e ≤ δ ^ 2 →
          let source := revisedFiniteMomentSource D R m δ e
          ContDiff ℝ ∞ source ∧ tsupport source ⊆ K ∧ HasCompactSupport source ∧
          ((∀ x ∈ D.core n, (e x).IsSymm) → ∀ x, (source x).IsSymm) ∧
          (∀ r, MemLp (iteratedFDeriv ℝ r source) 2 volume) ∧
          (∀ r, cNorm univ r source +
            cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j source) ≤
              L r * R ^ ((r : ℝ) - 2 * RevisedScales.forcingExponent n)) ∧
          (cNorm univ (RevisedScales.sourceOrder n) source +
            cartesianJetNorm univ (RevisedScales.sourceOrder n)
              (fun j ↦ iteratedFDeriv ℝ j source) ≤
                L (RevisedScales.sourceOrder n) * R ^ (-1 : ℝ)) ∧
          (cNorm univ (RevisedScales.sourceOrder n) source +
            cartesianJetNorm univ (RevisedScales.sourceOrder n)
              (fun j ↦ iteratedFDeriv ℝ j source) ≤
                L (RevisedScales.sourceOrder n) * R ^ (-separationExponent)) := by
  obtain ⟨K, Rgeom, hK, hKD, hRg, hsupp⟩ :=
    exists_affineSmoothing_fixed_support (F := MetricTensor n) (0 : Euclidean n)
      D.coreRadius_pos isOpen_ball (closedBall_subset_ball D.coreRadius_lt_chartRadius)
  refine ⟨K, Rgeom, hK, hKD, hRg, ?_⟩
  intro m hm
  obtain ⟨_, Rold, L, _, _, _, hRm, hL, hn, hb⟩ :=
    exists_revisedFiniteMomentSource_bounds (n := n) D m hm
  refine ⟨max Rgeom Rold, L, le_max_left _ _, hRg.trans (le_max_left _ _),
    hRm.trans (le_max_right _ _), hL, hn, ?_⟩
  intro R hR e he δ hδ hsmall
  dsimp only
  obtain ⟨hregular, _, hcompact, hsym, hmem, hprofile, hsource, hsmallSource⟩ :=
    hb R ((le_max_right _ _).trans hR) e he δ hδ hsmall
  refine ⟨hregular, ?_, hcompact, hsym, hmem, hprofile, hsource, hsmallSource⟩
  exact (tsupport_smul_subset_right
    (fun _ : Euclidean n ↦ ((δ * R ^ RevisedScales.forcingExponent n) ^ 2)⁻¹)
    (finiteMomentTensor D R m e)).trans
      (hsupp R ((le_max_left _ _).trans hR) m e)

end JanetCartan.DefectSmoothing
