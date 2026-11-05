module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.SupportedShell.Assembly
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.GlobalBounds

/-!
# Global cutoff bounds from the supported shell

The supported shell estimate feeds the existing rescaled-mask and mixed-jet
scaling identities. Low-frequency vanishing supplies the cone vertex. The
same spectator integral is estimated on all output frequencies, with a common
constant before the geometry, high norm and regularization. The only changed
geometric premise is shell containment on the closed transported support.
Consumer: the primitive norm variants in `SupportedShell.GlobalNormBounds`.
Sources: `app:ch_background:eq:bg-full-complex-amplitude` and `bg-frame`, Step 1.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

private theorem shellWeight_le {r ℓ : ℝ} (hℓ : 0 < ℓ) (hℓone : ℓ ≤ 1)
    (hr : ℓ ≤ r) {j s : ℕ} (hjs : j ≤ s) :
    (1 + r) ^ j * ((r / ℓ) ^ j)⁻¹ ≤ (2 : ℝ) ^ s := by
  have hr0 := hℓ.trans_le hr
  have ht : 1 ≤ r / ℓ := (le_div_iff₀ hℓ).mpr (by simpa using hr)
  have hrt : r ≤ r / ℓ := (le_div_iff₀ hℓ).mpr (mul_le_of_le_one_right hr0.le hℓone)
  calc
    _ ≤ (2 * (r / ℓ)) ^ j * ((r / ℓ) ^ j)⁻¹ := by gcongr; linarith
    _ = (2 : ℝ) ^ j := by
      rw [mul_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero j (div_pos hr0 hℓ).ne'), mul_one]
    _ ≤ (2 : ℝ) ^ s := pow_le_pow_right₀ (by norm_num) hjs

/-- Global weighted mixed jets from primitive coefficient and scalar mask
profiles. The fixed scalar profiles are produced by `RescaledCutoffs`; the
primitive finite-norm corollaries below discharge both profile premises.
No amplitude, inverse-jet or composed-mask estimate is assumed. The geometry
shift is two, and each frequency slot has one full symbol weight.
Source: `app:ch_background:eq:bg-symbol` and bg-frame Step 1. -/
theorem exists_transportAmplitude_supported_global_mixed_bound_of_maskProfiles
    (c : TransportSliceCoordinates n) (a : InputVariables n)
    (b : Variables n × Euclidean 2) {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ)
    {W K : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall a ρ ⊆ W) (hK : IsCompact K) (hWK : W ⊆ K)
    {O : Set (Variables n × Euclidean 2)} (hO : IsOpen O)
    (houtput : closedBall b τ ⊆ O)
    {V L : Set (Euclidean n × (ℝ × Euclidean 2))}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {T : Set ℝ} (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (hsegT : ∀ t ∈ T, MapsTo (transportSegmentInput n t) W V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W L)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {M E δ ε B : ℝ} (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hδ : 0 < δ) (hε : 0 < ε) (hB : 0 ≤ B)
    (hη : ∀ p ∈ closedBall a ρ, ε ≤ ‖p.2.2‖)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ)
    (hℓone : ℓ ≤ 1) (hlow : Cupper * ℓ ≤ 1)
    {S : Set (Euclidean 2)} (hS : IsCompact S) (s : ℕ) (hs : 2 ≤ s)
    {ι : Type*} (f : ι → ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hfzero : ∀ i r, r ≤ 1 → f i r = 0)
    {F : ℝ} (hF : 0 ≤ F)
    (hfjets : ∀ i t H, 1 ≤ t → 1 ≤ H → ∀ r, ε ≤ r →
      ShellJetProfile s H F (fun r ↦ f i (t * r)) r) :
    ∃ C > 0, ∀ (d : Coefficients n N)
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (J : InputVariables n → ℝ) (Ω : Set (Variables n × Euclidean 2))
      (U Z : Set (InputVariables n)) (X R : Set (Variables n)) (H : ℝ),
      ContDiffOn ℝ ∞ Y V → cNorm L 3 Y ≤ M →
      IsOpen Ω → O ⊆ Ω → ContDiffOn ℝ ∞ u Ω →
      MapsTo (inverseCoordinates u) (closedBall b τ) (closedBall a ρ) →
      (∀ q ∈ closedBall a ρ,
        ‖(A.symm : (Variables n × Euclidean 2) →L[ℝ] InputVariables n).comp
          (fderiv ℝ (augmentedTransportGradient Y) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ p ∈ Ω, transportAveragedGradient Y (inverseCoordinates u p) = p.1.2.2) →
      EqOn J (transportAbsoluteJacobian c Y) W → (∀ p ∈ W, J p ≠ 0) →
      (∀ q ∈ closedBall a ρ, δ ≤ transportAbsoluteJacobian c Y q) →
      1 ≤ H → 1 + cNorm L (s + 2) Y ≤ B * H →
      PrimitiveRegularity (homogeneousCoefficients d) J U → MapsTo (inverseCoordinates u) Ω U →
      (∀ p ∈ U, d.measurement p.1.1 ≠ 0 → d.measurement p.1.2 ≠ 0 →
        d.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z) →
      IsOpen R → X ⊆ R →
      closure (augmentedTransportGradient Y '' Z) ∩ (R ×ˢ univ) ⊆ Ω →
      (∀ x ∈ X, ∀ v ∈ S, (x, v) ∈ closure (augmentedTransportGradient Y '' Z) →
        (x, v) ∈ closedBall b τ) →
      (∀ p ∈ closedBall a ρ, CoefficientShellProfiles s H E (homogeneousCoefficients d) p) →
      (∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2)) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p)) →
      (∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖) →
      ∀ i, ∀ p : Variables n,
      (ℓ ≤ ‖p.2.2‖ → scaleFrequency (ℓ / ‖p.2.2‖) p ∈ X) →
      ∀ k ≤ s, ∀ I : Finset (Fin k), ∀ v : Fin k → Variables n,
      (∀ j ∈ I, (v j).1 = 0 ∧ (v j).2.1 = 0) →
      (∀ j ∉ I, (v j).2.2 = 0) →
      (1 + ‖p.2.2‖) ^ I.card *
        ‖iteratedFDeriv ℝ k (amplitude {d with high := f i} J u Ω S) p v‖ ≤
          C * H * ∏ j, ‖v j‖ := by
  obtain ⟨C, hC, hb⟩ := exists_transportAmplitude_supported_shell_bound (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM (add_nonneg hE hF) hδ hε hB hη hS s hs
  refine ⟨2 ^ s * C, by positivity, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
    hupper i p hp k hk I v hvk hvx
  by_cases hsmall : ‖p.2.2‖ < ℓ
  · rw [iteratedFDeriv_amplitude_eq_zero_of_low_frequency _ J u Ω S
      (hfzero i) hCupper hlow hupper p hsmall k]
    simp only [zero_apply, norm_zero, mul_zero]
    positivity
  have hr : ℓ ≤ ‖p.2.2‖ := le_of_not_gt hsmall
  have hr0 := hℓ.trans_le hr
  let t := ‖p.2.2‖ / ℓ
  have ht : 1 ≤ t := (le_div_iff₀ hℓ).mpr (by simpa using hr)
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  let x := scaleFrequency (ℓ / ‖p.2.2‖) p
  have hx : x ∈ X := hp hr
  have hback : scaleFrequency t x = p := by
    dsimp [x, t]
    simp [scaleFrequency, smul_smul, div_mul_div_cancel₀ hℓ.ne', hr0.ne']
  have hreg' : PrimitiveRegularity {d with high := f i} J U :=
    { hreg with high := hf i }
  have hcoeff' (q) (hq : q ∈ closedBall a ρ) :
      CoefficientShellProfiles s H (E + F) (rescaledCoefficients {d with high := f i} t) q :=
    (hcoeff q hq).replaceHigh (hfjets i t H ht hH _ (hη q hq)) hE hF
      (zero_le_one.trans hH)
  have hj := hb (rescaledCoefficients {d with high := f i} t) Y u J Ω U Z X R H
    hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet hH hhigh (hreg'.rescaled t)
    hmap (fun q hq h₁ h₂ h₃ _ ↦ hsupp q hq h₁ h₂ h₃)
    hR hXR hbuffer hshell hcoeff' x hx k hk
  have hscaled : ‖iteratedFDeriv ℝ k (amplitude {d with high := f i} J u Ω S) p v‖ ≤
      (t ^ I.card)⁻¹ * (C * H) * ∏ j, ‖v j‖ := by
    rw [← hback, iteratedFDeriv_amplitude_rescaled _ J u Ω S ht0
      (hscale t ht0) (huScale t ht0) (hJScale t ht0) x k I v hvk hvx,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos ht0 _))]
    calc
      _ ≤ (t ^ I.card)⁻¹ *
          (‖iteratedFDeriv ℝ k (amplitude (rescaledCoefficients {d with high := f i} t)
            J u Ω S) x‖ * ∏ j, ‖v j‖) :=
        mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.le_opNorm _ v) (by positivity)
      _ ≤ (t ^ I.card)⁻¹ * (C * H * ∏ j, ‖v j‖) := by gcongr
      _ = _ := by ring
  have hcard : I.card ≤ s := (by simpa using I.card_le_univ : I.card ≤ k).trans hk
  calc
    _ ≤ (1 + ‖p.2.2‖) ^ I.card *
        ((t ^ I.card)⁻¹ * (C * H) * ∏ j, ‖v j‖) := by gcongr
    _ = ((1 + ‖p.2.2‖) ^ I.card * (t ^ I.card)⁻¹) * (C * H * ∏ j, ‖v j‖) := by ring
    _ ≤ (2 : ℝ) ^ s * (C * H * ∏ j, ‖v j‖) :=
      mul_le_mul_of_nonneg_right (shellWeight_le hℓ hℓone hr hcard) (by positivity)
    _ = _ := by ring

end JanetCartan.ContinuumNormalReduction.TransportSymbol
