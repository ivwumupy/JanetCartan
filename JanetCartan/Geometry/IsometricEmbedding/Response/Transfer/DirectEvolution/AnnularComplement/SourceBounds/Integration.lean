module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.Support
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.PhaseJets

/-!
# Source integration with the original carrier phase

This is the integration step in `app:ch_response:lem:energy-carrier-jets`.
The existing nonstationary calculus is used with the actual source phases;
their gradient gap and higher grades are derived from the primitive phase
inputs. The physical Fourier constant and fixed source volume are explicit.

The remaining amplitude input here is a source derivative profile. Its producer
must prove it for the literal vector amplitude (and later every modified
amplitude) from the original symbol, masks, and supported envelope Sobolev
profiles. These conditional integration lemmas do not assert that producer or
the final complementary estimate has been completed.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral JanetCartan.Localization
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- The fixed constant in the normalized source integral. Its arguments
precede physical frequency, carrier parameter, envelope, and variable scales;
only the integration order `N` varies for arbitrary precision. -/
def annularSourceKernelConstant (n : ℕ) (S : Set (Euclidean n)) (c G : ℝ)
    (P C : ℕ → ℝ) (N : ℕ) : ℝ :=
  ‖((2 * Real.pi) ^ n : ℂ)⁻¹‖ *
    transposeDerivativeConstant (EuclideanSpace.basisFun (Fin n) ℝ)
      (phaseCoefficientDerivativeBound (EuclideanSpace.basisFun (Fin n) ℝ)
        (c ^ 2) G P) C N 0 * volume.real S

/-- Nonnegativity needed for the zero-frequency-selector branch and support
enlargement in `app:ch_response:lem:energy-carrier-jets`. -/
theorem annularSourceKernelConstant_nonneg (S : Set E) (c G : ℝ)
    (P C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (N : ℕ) :
    0 ≤ annularSourceKernelConstant n S c G P C N := by
  exact mul_nonneg (mul_nonneg (norm_nonneg _)
    (transposeDerivativeConstant_nonneg _
      (phaseCoefficientDerivativeBound_nonneg _ _ _ _) hC N 0)) measureReal_nonneg

/-- The normalized vector source integral with a fixed compact support. The
mixed-amplitude assembly uses this with the actual normalized external jet;
the following two lemmas discharge its phase inputs for the original kernels.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_annularSourceIntegral_le
    {Ω S : Set E} (hΩ : IsOpen Ω) (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    (ψ : E → ℝ) (u : E → F) (ξ : E) (N : ℕ)
    (hψ : ContDiffOn ℝ ∞ ψ Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hs : tsupport u ⊆ S) {c G H K lam : ℝ}
    (hc : 0 < c) (hH : 0 ≤ H) (hK : 0 ≤ K) (hlam : 0 < lam)
    (P C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hgap : ∀ z ∈ Ω, c * (lam + ‖ξ‖) ≤ ‖fderiv ℝ ψ z‖)
    (hupper : ∀ z ∈ Ω, ‖fderiv ℝ ψ z‖ ≤ G * (lam + ‖ξ‖))
    (hp : ∀ z ∈ S, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) ψ z‖ ≤ P j * (lam + ‖ξ‖) * K ^ j)
    (hb : ∀ z ∈ S, ∀ j, ‖iteratedFDeriv ℝ j u z‖ ≤ C j * (H * K ^ j)) :
    ‖((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z, phaseOscillation ψ z • u z‖ ≤
      annularSourceKernelConstant n S c G P C N * (H * (K / (lam + ‖ξ‖)) ^ N) := by
  have hcompact : HasCompactSupport u := hS.of_isClosed_subset (isClosed_tsupport _) hs
  have hcoeff := transposeDerivativeConstant_nonneg (EuclideanSpace.basisFun (Fin n) ℝ)
    (phaseCoefficientDerivativeBound_nonneg (EuclideanSpace.basisFun (Fin n) ℝ)
      (c ^ 2) G P) hC N 0
  have h := norm_vector_oscillatory_integral_le (μ := volume) hΩ
    (EuclideanSpace.basisFun (Fin n) ℝ) ψ u N hψ hu (hs.trans hSΩ) hcompact
    (sq_pos_of_pos hc) hH hK (add_pos_of_pos_of_nonneg hlam (norm_nonneg ξ))
    (fun z hz => by
      rw [phaseGradientSquare_orthonormalBasis]
      simpa only [mul_pow] using pow_le_pow_left₀
        (mul_nonneg hc.le (add_nonneg hlam.le (norm_nonneg ξ))) (hgap z hz) 2)
    hupper hC (fun z hz => hp z (hs hz)) (fun z hz => hb z (hs hz))
  have hvol : volume.real (tsupport u) ≤ volume.real S :=
    measureReal_mono hs hS.measure_lt_top.ne
  have hfac : 0 ≤ H * (K / (lam + ‖ξ‖)) ^ N := by positivity
  rw [norm_smul]
  refine (mul_le_mul_of_nonneg_left (h.trans
    (mul_le_mul_of_nonneg_left hvol (mul_nonneg hcoeff hfac))) (norm_nonneg _)).trans_eq ?_
  unfold annularSourceKernelConstant
  ring

/-- Forward source decay from the ORIGINAL carrier phase and a source
amplitude profile, using the gap of the actual normalized annulus. The profile
`C` is the output of the amplitude producer, not a differentiated kernel bound.
The separate scales satisfy `L ≤ K`; the gain is `(K/(λ+|ξ|))^N`. -/
theorem norm_forwardAnnularSourceKernel_of_source_jets
    {Ω S : Set E} (hΩ : IsOpen Ω) (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ) (φ : E → ℝ)
    (a : E → F) (x ξ : E) (N : ℕ)
    {a₀ B m M lam L K H : ℝ} (ha₀ : 0 < a₀) (hB : 0 < B)
    (hm : 0 < m) (hm1 : m ≤ 1) (hM1 : 1 ≤ M)
    (hlam : 0 < lam) (hL : 0 ≤ L) (hLK : L ≤ K) (hH : 0 ≤ H)
    (hφ : ContDiffOn ℝ ∞ φ Ω) (hs : tsupport a ⊆ S)
    (hu : ContDiffOn ℝ ∞ (forwardAnnularSourceAmplitude A π lam a x ξ) Ω)
    (hl : ∀ z ∈ Ω, a₀ ≤ ‖fderiv ℝ φ z‖)
    (hb : ∀ z ∈ Ω, ‖fderiv ℝ φ z‖ ≤ B)
    (hfar : 1 - annularSelector (a₀ / (2 * M)) (2 * B / m)
      (by positivity) (by positivity) (lam⁻¹ • ξ) ≠ 0)
    (Pφ C : ℕ → ℝ) (hPφ : ∀ j, 0 ≤ Pφ j) (hC : ∀ j, 0 ≤ C j)
    (hφj : ∀ z ∈ S, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) φ z‖ ≤ Pφ j * L ^ j)
    (huj : ∀ z ∈ S, ∀ j,
      ‖iteratedFDeriv ℝ j (forwardAnnularSourceAmplitude A π lam a x ξ) z‖ ≤
        C j * (H * K ^ j)) :
    ‖forwardAnnularSourceKernel Θ A π φ lam a x ξ‖ ≤
      annularSourceKernelConstant n S (radialGapConstant a₀ B * m) (B + 1) Pφ C N *
        (H * (K / (lam + ‖ξ‖)) ^ N) := by
  have hψ : ContDiffOn ℝ ∞ (forwardCarrierSourcePhase Θ φ lam x ξ) Ω :=
    (contDiffOn_const.sub ((contDiff_id.inner ℝ contDiff_const).contDiffOn)).add
      (hφ.const_smul lam)
  exact norm_annularSourceIntegral_le hΩ hS hSΩ _ _ ξ N hψ hu
    ((tsupport_forwardAnnularSourceAmplitude_subset A π lam a x ξ).trans hs)
    (mul_pos (radialGapConstant_pos ha₀ hB) hm) hH (hL.trans hLK) hlam Pφ C hC
    (fun z hz => forwardCarrierSourcePhase_gap Θ φ ha₀ hB hm hm1 hM1 hlam x ξ z
      ((hφ.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp)) (hl z hz) (hb z hz) hfar)
    (fun z hz => norm_fderiv_forwardCarrierSourcePhase_le Θ φ hlam.le x ξ z
      ((hφ.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp)) (hb z hz))
    (fun z hz => norm_iteratedFDeriv_forwardCarrierSourcePhase_le Θ φ hlam.le hL hLK
      x ξ z (hφ.contDiffAt (hΩ.mem_nhds (hSΩ hz))) Pφ hPφ (hφj z hz)) huj

/-- Adjoint source decay from primitive jets of the SAME original graph
phase and carrier. The radial comparison is the supported actual phase input
identified in `SourceGeometry`; no inverse chart or phase increment occurs. -/
theorem norm_adjointAnnularSourceKernel_of_source_jets
    {Ω S : Set E} (hΩ : IsOpen Ω) (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ) (φ : E → ℝ)
    (a : E → F) (x ξ : E) (N : ℕ)
    {a₀ B m M lam L K H : ℝ} (ha₀ : 0 < a₀) (hB : 0 < B)
    (hm : 0 < m) (hm1 : m ≤ 1) (hM : 0 < M)
    (hlam : 0 < lam) (hL : 0 ≤ L) (hLK : L ≤ K) (hH : 0 ≤ H)
    (hφ : ContDiffOn ℝ ∞ φ Ω) (hΘ : ContDiffOn ℝ ∞ (fun z => Θ z ξ) Ω)
    (hs : tsupport a ⊆ S)
    (hu : ContDiffOn ℝ ∞ (adjointAnnularSourceAmplitude A π lam a x ξ) Ω)
    (hl : ∀ z ∈ Ω, a₀ ≤ ‖fderiv ℝ φ z‖)
    (hb : ∀ z ∈ Ω, ‖fderiv ℝ φ z‖ ≤ B)
    (hvl : ∀ z ∈ Ω, m * ‖ξ‖ ≤ ‖fderiv ℝ (fun y => Θ y ξ) z‖)
    (hvu : ∀ z ∈ Ω, ‖fderiv ℝ (fun y => Θ y ξ) z‖ ≤ M * ‖ξ‖)
    (hfar : 1 - annularSelector (a₀ / (2 * M)) (2 * B / m)
      (by positivity) (by positivity) (lam⁻¹ • ξ) ≠ 0)
    (Pφ PΘ C : ℕ → ℝ) (hPφ : ∀ j, 0 ≤ Pφ j) (hPΘ : ∀ j, 0 ≤ PΘ j)
    (hC : ∀ j, 0 ≤ C j)
    (hφj : ∀ z ∈ S, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) φ z‖ ≤ Pφ j * L ^ j)
    (hΘj : ∀ z ∈ S, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ (j + 1) (fun y => Θ y ξ) z‖ ≤ PΘ j * ‖ξ‖ * L ^ j)
    (huj : ∀ z ∈ S, ∀ j,
      ‖iteratedFDeriv ℝ j (adjointAnnularSourceAmplitude A π lam a x ξ) z‖ ≤
        C j * (H * K ^ j)) :
    ‖adjointAnnularSourceKernel Θ A π φ lam a x ξ‖ ≤
      annularSourceKernelConstant n S (radialGapConstant a₀ B * m) (B + M)
        (fun j => Pφ j + PΘ j) C N * (H * (K / (lam + ‖ξ‖)) ^ N) := by
  have hψ : ContDiffOn ℝ ∞ (adjointCarrierSourcePhase Θ φ lam x ξ) Ω :=
    (contDiffOn_const.sub hΘ).add (hφ.const_smul lam)
  exact norm_annularSourceIntegral_le hΩ hS hSΩ _ _ ξ N hψ hu
    ((tsupport_adjointAnnularSourceAmplitude_subset A π lam a x ξ).trans hs)
    (mul_pos (radialGapConstant_pos ha₀ hB) hm) hH (hL.trans hLK) hlam
    (fun j => Pφ j + PΘ j) C hC
    (fun z hz => adjointCarrierSourcePhase_gap Θ φ ha₀ hB hm hm1 hM hlam x ξ z
      ((hφ.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp))
      ((hΘ.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp))
      (hl z hz) (hb z hz) (hvl z hz) (hvu z hz) hfar)
    (fun z hz => norm_fderiv_adjointCarrierSourcePhase_le Θ φ hlam.le hM.le x ξ z
      ((hφ.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp))
      ((hΘ.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp)) (hb z hz) (hvu z hz))
    (fun z hz => norm_iteratedFDeriv_adjointCarrierSourcePhase_le Θ φ hlam.le hL hLK
      x ξ z (hΘ.contDiffAt (hΩ.mem_nhds (hSΩ hz)))
      (hφ.contDiffAt (hΩ.mem_nhds (hSΩ hz))) Pφ PΘ hPφ hPΘ (hφj z hz) (hΘj z hz)) huj

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
