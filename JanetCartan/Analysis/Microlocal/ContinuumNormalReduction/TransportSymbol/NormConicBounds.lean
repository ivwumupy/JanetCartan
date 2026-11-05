module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.NormAssembly
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.ConicBounds

/-!
# Homogeneous symbol estimates from primitive finite norms

For `app:ch_background:eq:bg-symbol`, all quantitative profiles are now proved
from finite norms of the original primitives. Conic scaling is still an exact
geometric input, whose actual construction belongs to the chart owner.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- One-high mixed conic bounds from original primitive finite norms. Neither
coefficient profiles nor inverse/Jacobian profiles are assumptions. Every
frequency slot lowers the degree by one; physical position slots retain order
zero. The fixed high-order geometry shift is two. Source:
`app:ch_background:eq:bg-symbol` and `app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_transportAmplitude_conic_mixed_bound_of_primitiveNorms
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
    {M M₀ B₀ δ ε B : ℝ} (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀) (hB₀ : 1 ≤ B₀)
    (hδ : 0 < δ) (hε : 0 < ε) (hB : 0 ≤ B)
    (hη : ∀ p ∈ closedBall a ρ, ε ≤ ‖p.2.2‖)
    (D : CoefficientNormCharts n)
    (hfoot : ∀ p ∈ closedBall a ρ, D.Contains p)
    {S : Set (Euclidean 2)} (hS : IsCompact S) (s : ℕ) (hs : 2 ≤ s) :
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
      (∀ x ∈ X, ∀ v ∈ S, (x, v) ∈ Ω → (x, v) ∈ closedBall b τ) →
      D.Controls s M₀ B₀ H d →
      (∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2)) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p)) →
      ∀ x ∈ X, ∀ t : ℝ, 0 < t → ∀ k ≤ s, ∀ I : Finset (Fin k),
      ∀ v : Fin k → Variables n,
      (∀ i ∈ I, (v i).1 = 0 ∧ (v i).2.1 = 0) →
      (∀ i ∉ I, (v i).2.2 = 0) →
      ‖iteratedFDeriv ℝ k (amplitude (homogeneousCoefficients d) J u Ω S)
          (scaleFrequency t x) v‖ ≤
        (t ^ I.card)⁻¹ * (C * H) * ∏ i, ‖v i‖ := by
  obtain ⟨E, hE, hc⟩ := D.exists_profiles (N := N) hs hM₀ hB₀
  obtain ⟨C, hC, hb⟩ := exists_transportAmplitude_conic_mixed_bound (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM (show 0 ≤ E + 1 by linarith) hδ hε hB hη hS s hs
  refine ⟨C, hC, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
  exact hb d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell
    (fun p hp ↦ (hc d H hH hcoeff p (hfoot p hp)).homogeneous hE.le (zero_le_one.trans hH))
    hscale huScale hJScale

private theorem inhomogeneousWeight_mul_inv_pow_le {t : ℝ} (ht : 1 ≤ t)
    (j s : ℕ) (hjs : j ≤ s) : (1 + t) ^ j * (t ^ j)⁻¹ ≤ (2 : ℝ) ^ s := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  calc
    _ ≤ (2 * t) ^ j * (t ^ j)⁻¹ := by
      gcongr
      linarith
    _ = (2 : ℝ) ^ j := by
      rw [mul_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero j ht0.ne'), mul_one]
    _ ≤ (2 : ℝ) ^ s := pow_le_pow_right₀ (by norm_num) hjs

/-- The inhomogeneous order-zero symbol estimate on exterior frequencies
whose normalized covectors lie in the working shell. Every frequency slot is
weighted by `1 + ‖k‖`, and the constant is independent of the output frequency.
The only analytic bounds assumed are finite primitive norms; the homogeneous
shell estimate is instantiated inside this proof. No assertion at zero is
made for the uncompleted homogeneous amplitude. Source:
`app:ch_background:eq:bg-symbol`. -/
theorem exists_transportAmplitude_exterior_mixed_bound_of_primitiveNorms
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
    {M M₀ B₀ δ ε B : ℝ} (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀) (hB₀ : 1 ≤ B₀)
    (hδ : 0 < δ) (hε : 0 < ε) (hB : 0 ≤ B)
    (hη : ∀ p ∈ closedBall a ρ, ε ≤ ‖p.2.2‖)
    (D : CoefficientNormCharts n)
    (hfoot : ∀ p ∈ closedBall a ρ, D.Contains p)
    {S : Set (Euclidean 2)} (hS : IsCompact S) (s : ℕ) (hs : 2 ≤ s) :
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
      (∀ x ∈ X, ∀ v ∈ S, (x, v) ∈ Ω → (x, v) ∈ closedBall b τ) →
      D.Controls s M₀ B₀ H d →
      (∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2)) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p)) →
      ∀ p : Variables n, 1 ≤ ‖p.2.2‖ → scaleFrequency ‖p.2.2‖⁻¹ p ∈ X →
      ∀ k ≤ s, ∀ I : Finset (Fin k),
      ∀ v : Fin k → Variables n,
      (∀ i ∈ I, (v i).1 = 0 ∧ (v i).2.1 = 0) →
      (∀ i ∉ I, (v i).2.2 = 0) →
      (1 + ‖p.2.2‖) ^ I.card *
      ‖iteratedFDeriv ℝ k (amplitude (homogeneousCoefficients d) J u Ω S)
          p v‖ ≤ C * H * ∏ i, ‖v i‖ := by
  obtain ⟨C, hC, hb⟩ := exists_transportAmplitude_conic_mixed_bound_of_primitiveNorms
    (N := N) c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hS s hs
  refine ⟨2 ^ s * C, mul_pos (pow_pos (by norm_num) _) hC, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
    p hp hnorm k hk I v hvk hvx
  have ht : 0 < ‖p.2.2‖ := zero_lt_one.trans_le hp
  have hj := hb d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
    _ hnorm ‖p.2.2‖ ht k hk I v hvk hvx
  have hscaleBack : scaleFrequency ‖p.2.2‖ (scaleFrequency ‖p.2.2‖⁻¹ p) = p := by
    simp [scaleFrequency, smul_smul, ht.ne']
  rw [hscaleBack] at hj
  have hcard : I.card ≤ s := (by simpa using I.card_le_univ : I.card ≤ k).trans hk
  calc
    _ ≤ (1 + ‖p.2.2‖) ^ I.card *
        ((‖p.2.2‖ ^ I.card)⁻¹ * (C * H) * ∏ i, ‖v i‖) := by
      gcongr
    _ = ((1 + ‖p.2.2‖) ^ I.card * (‖p.2.2‖ ^ I.card)⁻¹) *
        (C * H * ∏ i, ‖v i‖) := by ring
    _ ≤ (2 : ℝ) ^ s * (C * H * ∏ i, ‖v i‖) :=
      mul_le_mul_of_nonneg_right (inhomogeneousWeight_mul_inv_pow_le hp _ _ hcard)
        (by positivity)
    _ = _ := by ring

end JanetCartan.ContinuumNormalReduction.TransportSymbol
