module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.EnvelopeJets.FourierNorm

/-!
# Full-source words in the physical vector channels

The strain producer measures a Hilbert-valued weighted Fourier transform,
while the elapsed graph takes a finite vector of scalar Fourier channels.
A fixed complex-linear channel operation commutes with the parameter
derivative and with physical Fourier transformation on the original compact
source. Its operator norm is the only constant in this change of fiber.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory FourierTransform
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.FullSourceEnvelopes
open Pseudodifferential SourceNegative JanetCartan.ResponseTransfer.Complement
variable {n d r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "E" => Euclidean n
local notation "P" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Read the original Hilbert source profile in the exact vector Fourier norm
used by `exists_fullSource_mixedL2_profile` and both elapsed orientations.
For a fixed channel operation this applies to the derivative of the original
projected datum and costs no spatial derivative. The identity channel covers
a source already in graph coordinates; the original compact strain profiles
are supplied by `exists_fullSource_strainWord_profiles`
(`app:ch_response:eq:fixed-factor-transfer`,
`app:ch_response:eq:response-graded-source`). -/
theorem fullSource_channelWord_fourier_profile
    (R : H →L[ℂ] F) (a : P → E → H) (c : P)
    (ha : ∀ x, ContDiffAt ℝ ∞ (fun b ↦ a b x) c) (k : ℕ) (v : Fin k → P)
    (A K : ℝ) (C : ℕ → ℝ) :
    let f := fun x ↦ iteratedFDeriv ℝ k (fun b ↦ a b x) c v
    let g := fun x ↦ iteratedFDeriv ℝ k (fun b ↦ R (a b x)) c v
    ∀ hf : MemLp f 2 volume, HasCompactSupport f →
      SobolevEnvelopeBounds f hf (A * K ^ k) K C →
      ∃ hg : MemLp g 2 volume, ∀ s : ℕ,
        MemVectorFourierSobolev (s : ℝ) (hg.toLp g) ∧
          vectorFourierSobolevNorm (s : ℝ) (hg.toLp g) ≤
            (‖R‖ * C s) * A * K ^ (s + k) := by
  intro f g hf hc h
  have he : g = R ∘ f := by
    funext x
    exact congrArg (fun D : P [×k]→L[ℝ] F ↦ D v)
      ((R.restrictScalars ℝ).iteratedFDeriv_comp_left (ha x) (i := k) (by simp))
  rw [he]
  let hg := R.comp_memLp' hf
  refine ⟨hg, ?_⟩
  let u := hf.toLp f
  let b := hg.toLp (R ∘ f)
  have hi : Integrable f := h.smooth.continuous.integrable_of_hasCompactSupport hc
  have huw : (𝓕 u : Lp (α := E) H 2 volume) =ᵐ[volume] 𝓕 f :=
    (Localization.fourierTransform_coeFn_ae_integral_hilbert u (hi.congr hf.coeFn_toLp.symm)).trans
      (Eventually.of_forall (Real.fourier_congr_ae hf.coeFn_toLp))
  have hbw : (𝓕 b : Lp (α := E) F 2 volume) =ᵐ[volume] 𝓕 (R ∘ f) :=
    (Localization.fourierTransform_coeFn_ae_integral_hilbert b
      ((R.integrable_comp hi).congr hg.coeFn_toLp.symm)).trans
      (Eventually.of_forall (Real.fourier_congr_ae hg.coeFn_toLp))
  have hproj (ξ : E) : R (𝓕 f ξ) = 𝓕 (R ∘ f) ξ := by
    rw [Real.fourier_eq, Real.fourier_eq, ← R.integral_comp_comm
      ((Real.fourierIntegral_convergent_iff ξ).mpr hi)]
    congr 1
    funext x
    exact R.map_smul_of_tower _ _
  intro s
  let w := fun ξ ↦ euclideanSobolevWeight (s : ℝ) ξ • (𝓕 u : Lp (α := E) H 2 volume) ξ
  let q := fun ξ ↦ euclideanSobolevWeight (s : ℝ) ξ • (𝓕 b : Lp (α := E) F 2 volume) ξ
  have hw : MemLp w 2 volume := h.fourier_memLp s
  have hqeq : q =ᵐ[volume] R ∘ w := by
    filter_upwards [huw, hbw] with ξ hu hb
    simp only [w, q, Function.comp_apply, hu, hb, R.map_smul_of_tower, hproj]
  have hq := (R.comp_memLp' hw).ae_eq hqeq.symm
  have hm : MemVectorFourierSobolev (s : ℝ) b := by
    intro j
    apply (hq.eval_piLp j).ae_eq
    filter_upwards [finiteL2Coordinates_apply_ae volume (𝓕 b) j] with ξ hj
    change (finiteL2CoordinateIsometry volume (𝓕 b) j) ξ = _ at hj
    rw [coordinate_fourier] at hj
    change euclideanSobolevWeight (s : ℝ) ξ • (𝓕 b : Lp (α := E) F 2 volume) ξ j =
      euclideanSobolevWeight (s : ℝ) ξ • (𝓕 (finiteL2CoordinateIsometry volume b j)) ξ
    rw [hj]
  have hclass : hq.toLp q = R.compLp (hw.toLp w) := by
    apply Lp.ext
    filter_upwards [hq.coeFn_toLp, hqeq, R.coeFn_compLp (hw.toLp w), hw.coeFn_toLp] with ξ h₁ h₂ h₃ h₄
    exact h₁.trans (h₂.trans ((congrArg R h₄.symm).trans h₃.symm))
  refine ⟨hm, ?_⟩
  calc
    vectorFourierSobolevNorm (s : ℝ) b = (eLpNorm q 2 volume).toReal :=
      (InactiveSource.eLpNorm_weighted_vectorFourier _ b hm).symm
    _ = ‖R.compLp (hw.toLp w)‖ := by rw [← Lp.norm_toLp q hq, hclass]
    _ ≤ ‖R‖ * ‖hw.toLp w‖ := R.norm_compLp_le _
    _ ≤ ‖R‖ * (C s * (A * K ^ k) * K ^ s) :=
      mul_le_mul_of_nonneg_left (by rw [Lp.norm_toLp]; exact h.fourier_bound s) (norm_nonneg _)
    _ = _ := by rw [pow_add]; ring

end JanetCartan.ResponseTransfer.FullSourceEnvelopes
