module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Assembly
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.FrequencyBounds

/-!
# Quantitative mixed conic jets from the literal spectator formula

This combines the primitive shell estimate with the exact dilation law.
It is the homogeneous part of `app:ch_background:eq:bg-symbol`: each frequency
slot contributes one inverse power of the dilation, and both position slots
retain order zero. No amplitude estimate is among the inputs.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- One-high mixed frequency estimates along every positive dilation of the
working shell. The inverse and Jacobian bounds are derived from `Y`, and the
frequency powers are obtained by differentiating the actual homogeneous
spectator integral. The constants precede the geometry and the common high
norm `H`. When the working shell has unit covectors, `t` is exactly the output
frequency norm. This is the homogeneous estimate used in
`app:ch_background:eq:bg-symbol` and `app:ch_background:prop:bg-frame`, Step 1.
The open region `R` may be the punctured frequency space, so the relative
buffer imposes no smoothness at the cone vertex. Actual conic chart identities
and primitive support buffers remain explicit
geometric inputs; no evenness of the angular mask is imposed. -/
theorem exists_transportAmplitude_conic_mixed_bound
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
      (∀ p ∈ closedBall a ρ, CoefficientShellProfiles s H E (homogeneousCoefficients d) p) →
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
  obtain ⟨C, hC, hbound⟩ := exists_transportAmplitude_shell_bound (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hE hδ hε hB hη hS s hs
  refine ⟨C, hC, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
    x hx t ht k hk I v hvk hvx
  have hb := hbound (homogeneousCoefficients d) Y u J Ω U Z X R H hY hYM hΩ hOΩ
    hu hrange hgap heq hJ hne hdet hH hhigh hreg hmap
    (fun p hp hm hm' ha _ ↦ hsupp p hp hm hm' ha)
    hR hXR hbuffer hshell hcoeff x hx k hk
  rw [iteratedFDeriv_homogeneousAmplitude_mixed_scaling d J u Ω S ht
    (hscale t ht) (huScale t ht) (hJScale t ht) x k I v hvk hvx,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos ht _))]
  calc
    _ ≤ (t ^ I.card)⁻¹ *
        (‖iteratedFDeriv ℝ k (amplitude (homogeneousCoefficients d) J u Ω S) x‖ *
          ∏ i, ‖v i‖) :=
      mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.le_opNorm _ v)
        (inv_nonneg.mpr (pow_nonneg ht.le _))
    _ ≤ (t ^ I.card)⁻¹ * (C * H * ∏ i, ‖v i‖) := by gcongr
    _ = _ := by ring

end JanetCartan.ContinuumNormalReduction.TransportSymbol
