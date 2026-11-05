module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedFullMask
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.AngularGap
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ScaleGap
public import JanetCartan.Geometry.IsometricEmbedding.Waves.ProductSum.Estimates

/-!
# Original stage powers for the complete reduced signed-source tail

Apply the actual reduced-vector estimate on the full complementary mask, using
the original signed angular buffer and the original scale window. The threshold
is chosen before the accuracy, and the accuracy constant before every source,
sample, target, finite history and mask realization. The source cutoff and reduced cutoff are never
removed. This closes the source-tail calculation in Step 1 of
`app:ch_pairs:prop:pairs-lag-sum`; the complete fixed-response residual chains
and physical response-size estimates remain separate producer obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff ComplexConjugate Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.SignedProductEstimates
open Sampling.BackgroundModulation

open JanetCartan.Localization ResponseTransfer.SourceNegative
open ResponseTransfer.Complement.InactiveSource

variable {n N : ℕ}

/-- The complete complementary tail of each actual reduced signed source has the
original stage decay, derived from signed angular protection, primitive phase
jets, the original row/cutoff jets and individual amplitude jets (`app:ch_pairs:eq:pairs-lag-one-error`,
source step; `main:eq:all-pair-scales`). `K` is the original common protected
covector set. No full Fourier gap, source-tail estimate or response estimate is
assumed. Applying this to the normalized plus/minus phases identified in
`ReducedSources` retains every doubled plus carrier and excludes only zero differences.
The fixed-response producer must still apply its full residual-chain theorem. -/
theorem exists_reduced_signed_protected_source_stage_constants
    {S : Set (Euclidean n)} (hS : IsCompact S)
    {a G δ cbeat : ℝ} (ha : 0 < a) (hG : 0 < G) (hδ : 0 < δ) (hbeat : 0 < cbeat)
    (W Cscale : ℝ) (hW : 0 ≤ W)
    (P X Y CQ C : ℕ → ℝ) (hP : ∀ r, 0 ≤ P r) (hX : ∀ r, 0 ≤ X r)
    (hY : ∀ r, 0 ≤ Y r) (hCQ : ∀ r, 0 ≤ CQ r) (hC : ∀ r, 0 ≤ C r)
    {s : ℝ} (hs : 0 ≤ s) :
    ∃ Rmin : ℝ, 2 ≤ Rmin ∧ ∀ q : ℕ, ∃ D : ℝ, 0 ≤ D ∧
      ∀ (U : Set (Euclidean n)), IsOpen U → S ⊆ U →
      ∀ (K : Set (Euclidean n →L[ℝ] ℝ)) (χ ψ φ : Euclidean n → ℝ)
        (Q : Euclidean n → Fin n → MetricTensor n) (A B : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
        (R L ρ : ℝ) (m : BoundedMask n),
      ContDiffOn ℝ ∞ χ U → ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ Q U →
      ContDiffOn ℝ ∞ φ U →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      tsupport χ ⊆ S → 1 ≤ L → Rmin ≤ R → m.bound ≤ W →
      cbeat * (R ^ carrierExponent * R ^ (-separationExponent)) ≤ ρ →
      L ≤ Cscale * R ^ (1 + meanSlack) →
      (∀ x ∈ U, a ≤ ‖fderiv ℝ φ x‖ ∧ ‖fderiv ℝ φ x‖ ≤ G) →
      (∀ x ∈ U, NormedSpace.normalize (fderiv ℝ φ x) ∈ K) →
      (∀ η, m.symbol η ≠ 0 → a * ρ / 2 ≤ ‖η‖ → ‖η‖ ≤ 2 * G * ρ →
        ∀ v ∈ K, δ ≤ dist v (NormedSpace.normalize (InnerProductSpace.toDual ℝ (Euclidean n) η))) →
      (∀ x ∈ S, ∀ r, 1 ≤ r → ‖iteratedFDeriv ℝ (r + 1) φ x‖ ≤ P r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r χ x‖ ≤ X r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r ψ x‖ ≤ Y r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r Q x‖ ≤ CQ r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r A x‖ ≤ C r * L ^ r) →
      (∀ x ∈ U, ∀ r, ‖iteratedFDeriv ℝ r B x‖ ≤ C r * L ^ r) →
      let Hp := fun η : Euclidean n ↦ m.symbol η • physicalFourierIntegral volume
        (modulatedSource χ φ (fun x ↦ ψ x • ((1 / 2 : ℝ) •
          complexStressContraction (Q x) (symmetricBilinearTensor (A x) (B x)))) ρ)
          (InnerProductSpace.toDual ℝ (Euclidean n) η)
      let Hm := fun η : Euclidean n ↦ m.symbol η • physicalFourierIntegral volume
        (modulatedSource χ φ (fun x ↦ ψ x • ((1 / 2 : ℝ) •
          complexStressContraction (Q x) (symmetricBilinearTensor (A x) ((B x).map conj)))) ρ)
          (InnerProductSpace.toDual ℝ (Euclidean n) η)
      (Integrable (fun η ↦ (1 + ‖η‖ ^ 2) ^ s * ‖Hp η‖ ^ 2) ∧
        fourierWeightedL2Norm volume s Hp ≤
          D * ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹) ∧
      (Integrable (fun η ↦ (1 + ‖η‖ ^ 2) ^ s * ‖Hm η‖ ^ 2) ∧
        fourierWeightedL2Norm volume s Hm ≤
          D * ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹) := by
  obtain ⟨Rmin, hmin, hscale⟩ := exists_signed_pair_scale_threshold hbeat Cscale
  refine ⟨Rmin, hmin, fun q ↦ ?_⟩
  obtain ⟨k, hk, ho⟩ := exists_tail_order (show (0 : ℝ) < 1 / 1000 by norm_num)
    (s + (n : ℝ) / 2) q
  let c := min (radialGapConstant a G) (min δ 1 * min a 1 / 4)
  have hc : 0 < c := buffered_mask_gap_constant_pos ha hG hδ
  obtain ⟨D, hD, htail⟩ := exists_reduced_signed_full_mask_tail_constant (N := N) hS hc G W hW
    P X Y CQ C hP hX hY hCQ hC hs k hk
  refine ⟨D * (cbeat ^ q)⁻¹, by positivity, ?_⟩
  intro U hU hSU K χ ψ φ Q A B R L ρ m hχ hψ hQ hφ hA hB hχs hL hR hm hρ hslow
    hband hprotected hbuffer hphase hχb hψb hQb hAb hBb
  obtain ⟨hρtwo, hgapscale⟩ := hscale R hR ρ L hρ hslow
  have hρpos : 0 < ρ := by linarith
  have hfullgap (η : Euclidean n) (hη : m.symbol η ≠ 0) (x : Euclidean n) (hx : x ∈ U) :
      c * (ρ + ‖η‖) ≤ ‖ρ • fderiv ℝ φ x - InnerProductSpace.toDual ℝ (Euclidean n) η‖ := by
    simpa only [LinearIsometryEquiv.norm_map] using
      full_frequency_gap_of_buffered_mask ha hG hδ hρpos
        (hband x hx).1 (hband x hx).2 (hprotected x hx)
        (η := InnerProductSpace.toDual ℝ (Euclidean n) η)
        (by simpa only [LinearIsometryEquiv.norm_map] using hbuffer η hη)
  obtain ⟨hp, hn⟩ := htail U hU hSU χ ψ φ Q A B L ρ m hχ hψ hQ hφ hA hB hχs hL
    (by linarith) hm hfullgap (fun x hx ↦ (hband x hx).2) hphase hχb hψb hQb hAb hBb
  have hdecay : ρ ^ (s + (n : ℝ) / 2) * (L / ρ) ^ k ≤ (ρ ^ q)⁻¹ := by
    simpa only [Real.rpow_neg hρpos.le, Real.rpow_natCast] using
      tail_factor_le_negative_power (by linarith : 1 ≤ ρ)
        (zero_le_one.trans hL) hgapscale ho
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) (hmin.trans hR)
  have hbeatpow : (ρ ^ q)⁻¹ ≤ (cbeat ^ q)⁻¹ *
      ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹ := by
    simpa only [mul_pow, mul_inv_rev, mul_comm] using
      ProductSum.inverse_pow_le_of_scale_le (by positivity) hρ q
  have hb : D * (ρ ^ (s + (n : ℝ) / 2) * (L / ρ) ^ k) ≤
      (D * (cbeat ^ q)⁻¹) * ((R ^ carrierExponent * R ^ (-separationExponent)) ^ q)⁻¹ :=
    (mul_le_mul_of_nonneg_left (hdecay.trans hbeatpow) hD).trans_eq (by ring)
  exact ⟨⟨hp.1, hp.2.trans hb⟩, ⟨hn.1, hn.2.trans hb⟩⟩

end JanetCartan.SignedProductEstimates
