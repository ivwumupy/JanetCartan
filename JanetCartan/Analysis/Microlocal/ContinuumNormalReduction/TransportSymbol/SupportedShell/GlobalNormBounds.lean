module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.SupportedShell.GlobalBounds
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.GlobalNormBounds

/-!
# Global primitive-norm symbol bounds with supported shell containment

These variants of `GlobalNormBounds` replace only whole-domain shell
containment by containment on `closure (augmentedTransportGradient Y '' Z)`.
The original primitive mask hypotheses imply vanishing of every density jet
off this set. All primitive norms, inverse/Jacobian identities, derivative
gaps, homogeneity hypotheses, derivative orders and quantifier order are
preserved. In particular the single high norm enters linearly, the geometry
shift remains two, and the regularized constant precedes `Q ≥ 1`.

The global conclusions use the same literal spectator measure, squared
regularization and genuine initial multiplier. Their consumer is
`jc-carrier-supported-shell-construction`; actual geometric instantiation
remains with `jc-continuum-canonical-conic-inputs`.
Sources: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-mixed-input` and `app:ch_background:prop:bg-frame`, Step 1.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- Global high-cutoff order-zero mixed symbol estimate.
The inputs contain only primitive finite norms and exact geometric chart data.
The common high bound enters once, with coefficient order `s` and geometry
order `s+2`; the low geometry order is three. Every frequency slot lowers
symbol order by one.
Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-symbol`, and bg-frame Step 1. -/
theorem exists_transportAmplitude_supported_global_mixed_bound_of_primitiveNorms
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
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ)
    (hℓone : ℓ ≤ 1) (hlow : Cupper * ℓ ≤ 1)
    {S : Set (Euclidean 2)} (hS : IsCompact S) (s : ℕ) (hs : 2 ≤ s)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hzero : ∀ r, r ≤ 1 → h r = 0) (htail : ∀ r, 2 ≤ r → h r = 1) :
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
      PrimitiveRegularity d J U → MapsTo (inverseCoordinates u) Ω U →
      (∀ p ∈ U, d.measurement p.1.1 ≠ 0 → d.measurement p.1.2 ≠ 0 →
        d.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z) →
      IsOpen R → X ⊆ R →
      closure (augmentedTransportGradient Y '' Z) ∩ (R ×ˢ univ) ⊆ Ω →
      (∀ x ∈ X, ∀ v ∈ S, (x, v) ∈ closure (augmentedTransportGradient Y '' Z) →
        (x, v) ∈ closedBall b τ) →
      D.Controls s M₀ B₀ H d →
      (∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2)) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p)) →
      (∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖) →
      ∀ p : Variables n,
      (ℓ ≤ ‖p.2.2‖ → scaleFrequency (ℓ / ‖p.2.2‖) p ∈ X) →
      ∀ k ≤ s, ∀ I : Finset (Fin k), ∀ v : Fin k → Variables n,
      (∀ j ∈ I, (v j).1 = 0 ∧ (v j).2.1 = 0) →
      (∀ j ∉ I, (v j).2.2 = 0) →
      (1 + ‖p.2.2‖) ^ I.card *
        ‖iteratedFDeriv ℝ k (amplitude {d with high := h} J u Ω S) p v‖ ≤
          C * H * ∏ j, ‖v j‖ := by
  obtain ⟨E, hE, he⟩ := D.exists_profiles (N := N) hs hM₀ hB₀
  obtain ⟨F, hF, hf⟩ := exists_rescaledHigh_shellJetProfile hh htail hε s hs
  let f : Unit → ℝ → ℝ := fun _ ↦ h
  obtain ⟨C, hC, hb⟩ := exists_transportAmplitude_supported_global_mixed_bound_of_maskProfiles (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM (show 0 ≤ E + 1 by linarith) hδ hε hB hη hCupper hℓ hℓone hlow hS s hs
    f (fun _ ↦ hh) (fun _ ↦ hzero) hF.le (fun _ ↦ hf)
  refine ⟨C, hC, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale hupper
  have hp (p) (hp : p ∈ closedBall a ρ) :=
    (he d H hH hcoeff p (hfoot p hp)).homogeneous hE.le (zero_le_one.trans hH)
  exact hb d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg.homogeneous hmap hsupp hR hXR hbuffer hshell hp hscale huScale hJScale hupper ()

/-- Uniform regularized global order-zero mixed symbol estimate.
The inputs contain only primitive finite norms and exact geometric chart data.
The common high bound enters once, with coefficient order `s` and geometry
order `s+2`; the low geometry order is three. Every frequency slot lowers
symbol order by one. The constant is independent of `Q ≥ 1`, and the carrier
regularization stays squared.
Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-symbol`, and bg-frame Step 1. -/
theorem exists_transportAmplitude_supported_regularized_global_mixed_bound_of_primitiveNorms
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
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ)
    (hℓone : ℓ ≤ 1) (hlow : Cupper * ℓ ≤ 1)
    {S : Set (Euclidean 2)} (hS : IsCompact S) (s : ℕ) (hs : 2 ≤ s)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hzero : ∀ r, r ≤ 1 → h r = 0) (htail : ∀ r, 2 ≤ r → h r = 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
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
      PrimitiveRegularity d J U → MapsTo (inverseCoordinates u) Ω U →
      (∀ p ∈ U, d.measurement p.1.1 ≠ 0 → d.measurement p.1.2 ≠ 0 →
        d.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z) →
      IsOpen R → X ⊆ R →
      closure (augmentedTransportGradient Y '' Z) ∩ (R ×ˢ univ) ⊆ Ω →
      (∀ x ∈ X, ∀ v ∈ S, (x, v) ∈ closure (augmentedTransportGradient Y '' Z) →
        (x, v) ∈ closedBall b τ) →
      D.Controls s M₀ B₀ H d →
      (∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2)) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p)) →
      (∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖) →
      ∀ Q : ℝ, 1 ≤ Q → ∀ p : Variables n,
      (ℓ ≤ ‖p.2.2‖ → scaleFrequency (ℓ / ‖p.2.2‖) p ∈ X) →
      ∀ k ≤ s, ∀ I : Finset (Fin k), ∀ v : Fin k → Variables n,
      (∀ j ∈ I, (v j).1 = 0 ∧ (v j).2.1 = 0) →
      (∀ j ∉ I, (v j).2.2 = 0) →
      (1 + ‖p.2.2‖) ^ I.card *
        ‖iteratedFDeriv ℝ k (amplitude (regularizedCoefficients {d with high := h} χ Q) J u Ω S) p v‖ ≤
          C * H * ∏ j, ‖v j‖ := by
  obtain ⟨E, hE, he⟩ := D.exists_profiles (N := N) hs hM₀ hB₀
  obtain ⟨F, hF, hf⟩ := exists_rescaledRegularizedHigh_shellJetProfile
    hh htail hχ hcχ hε s hs
  let f : {Q : ℝ // 1 ≤ Q} → ℝ → ℝ := fun Q r ↦ h r * χ (r / Q.val)
  have hfs (Q) : ContDiff ℝ ∞ (f Q) := hh.mul (hχ.comp (contDiff_id.div_const Q.val))
  have hfz (Q) (r) (hr : r ≤ 1) : f Q r = 0 := by simp [f, hzero r hr]
  obtain ⟨C, hC, hb⟩ := exists_transportAmplitude_supported_global_mixed_bound_of_maskProfiles (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM (show 0 ≤ E + 1 by linarith) hδ hε hB hη hCupper hℓ hℓone hlow hS s hs
    f hfs hfz hF.le (fun Q t H ht hH r hr ↦ hf t Q.val H ht Q.property hH r hr)
  refine ⟨C, hC, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale hupper
  have hp (p) (hp : p ∈ closedBall a ρ) :=
    (he d H hH hcoeff p (hfoot p hp)).homogeneous hE.le (zero_le_one.trans hH)
  intro Q hQ
  exact hb d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg.homogeneous hmap hsupp hR hXR hbuffer hshell hp hscale huScale hJScale hupper ⟨Q, hQ⟩

/-- Global high-cutoff order-zero mixed symbol estimate with the genuine initial multiplier `r(z,Y)`.
The inputs contain only primitive finite norms and exact geometric chart data.
The common high bound enters once, with coefficient order `s` and geometry
order `s+2`; the low geometry order is three. Every frequency slot lowers
symbol order by one.
Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-symbol`, and bg-frame Step 1. -/
theorem exists_transportAmplitude_supported_initial_global_mixed_bound_of_primitiveNorms
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
    (Dr : PrimitiveNormChart ((ℝ × Euclidean 2) × Euclidean (n - 1)))
    (hfoot : ∀ p ∈ closedBall a ρ, D.Contains p)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ)
    (hℓone : ℓ ≤ 1) (hlow : Cupper * ℓ ≤ 1)
    {S : Set (Euclidean 2)} (hS : IsCompact S) (s : ℕ) (hs : 2 ≤ s)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hzero : ∀ r, r ≤ 1 → h r = 0) (htail : ∀ r, 2 ≤ r → h r = 1) :
    ∃ C > 0, ∀ (d : Coefficients n N)
      (r : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ)
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
      PrimitiveRegularity d J U → MapsTo (inverseCoordinates u) Ω U →
      (∀ p ∈ U, d.measurement p.1.1 ≠ 0 → d.measurement p.1.2 ≠ 0 →
        d.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z) →
      IsOpen R → X ⊆ R →
      closure (augmentedTransportGradient Y '' Z) ∩ (R ×ˢ univ) ⊆ Ω →
      (∀ x ∈ X, ∀ v ∈ S, (x, v) ∈ closure (augmentedTransportGradient Y '' Z) →
        (x, v) ∈ closedBall b τ) →
      D.Controls s M₀ B₀ H d →
      Dr.Controls s M₀ B₀ H r → D.field.Controls s M₀ B₀ H Y →
      (∀ p ∈ D.field.carrier, (p.2, Y p) ∈ Dr.carrier) →
      MapsTo (fun p : InputVariables n ↦ (p.1.1, p.2.1)) U D.field.region →
      MapsTo (fun p : InputVariables n ↦ (p.1.2, p.2.1)) U D.field.region →
      MapsTo (fun p ↦ (p.2, Y p)) D.field.region Dr.region →
      (∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2)) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p)) →
      (∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖) →
      ∀ p : Variables n,
      (ℓ ≤ ‖p.2.2‖ → scaleFrequency (ℓ / ‖p.2.2‖) p ∈ X) →
      ∀ k ≤ s, ∀ I : Finset (Fin k), ∀ v : Fin k → Variables n,
      (∀ j ∈ I, (v j).1 = 0 ∧ (v j).2.1 = 0) →
      (∀ j ∉ I, (v j).2.2 = 0) →
      (1 + ‖p.2.2‖) ^ I.card *
        ‖iteratedFDeriv ℝ k (amplitude {withInitialMultiplier d r Y with high := h} J u Ω S) p v‖ ≤
          C * H * ∏ j, ‖v j‖ := by
  obtain ⟨E, hE, he⟩ := exists_initialMultiplier_coefficientShellProfiles_of_norms
    (N := N) D Dr hs hM₀ hB₀
  obtain ⟨F, hF, hf⟩ := exists_rescaledHigh_shellJetProfile hh htail hε s hs
  let f : Unit → ℝ → ℝ := fun _ ↦ h
  obtain ⟨C, hC, hb⟩ := exists_transportAmplitude_supported_global_mixed_bound_of_maskProfiles (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM (show 0 ≤ E + 1 by linarith) hδ hε hB hη hCupper hℓ hℓone hlow hS s hs
    f (fun _ ↦ hh) (fun _ ↦ hzero) hF.le (fun _ ↦ hf)
  refine ⟨C, hC, ?_⟩
  intro d r Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hr hYnorm hfootY hl hrr hregion hscale huScale hJScale hupper
  have hreg' := hreg.withInitialMultiplier hr.smooth hYnorm.smooth hl hrr hregion
  have hp (p) (hp : p ∈ closedBall a ρ) :=
    (he d r Y H hH hcoeff hr hYnorm hfootY p (hfoot p hp)).homogeneous hE.le (zero_le_one.trans hH)
  exact hb (withInitialMultiplier d r Y) Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg'.homogeneous hmap hsupp hR hXR hbuffer hshell hp hscale huScale hJScale hupper ()

/-- Uniform regularized global order-zero mixed symbol estimate with the genuine initial multiplier `r(z,Y)`.
The inputs contain only primitive finite norms and exact geometric chart data.
The common high bound enters once, with coefficient order `s` and geometry
order `s+2`; the low geometry order is three. Every frequency slot lowers
symbol order by one. The constant is independent of `Q ≥ 1`, and the carrier
regularization stays squared.
Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-symbol`, and bg-frame Step 1. -/
theorem exists_transportAmplitude_supported_initial_regularized_global_mixed_bound_of_primitiveNorms
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
    (Dr : PrimitiveNormChart ((ℝ × Euclidean 2) × Euclidean (n - 1)))
    (hfoot : ∀ p ∈ closedBall a ρ, D.Contains p)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ)
    (hℓone : ℓ ≤ 1) (hlow : Cupper * ℓ ≤ 1)
    {S : Set (Euclidean 2)} (hS : IsCompact S) (s : ℕ) (hs : 2 ≤ s)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hzero : ∀ r, r ≤ 1 → h r = 0) (htail : ∀ r, 2 ≤ r → h r = 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    ∃ C > 0, ∀ (d : Coefficients n N)
      (r : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ)
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
      PrimitiveRegularity d J U → MapsTo (inverseCoordinates u) Ω U →
      (∀ p ∈ U, d.measurement p.1.1 ≠ 0 → d.measurement p.1.2 ≠ 0 →
        d.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z) →
      IsOpen R → X ⊆ R →
      closure (augmentedTransportGradient Y '' Z) ∩ (R ×ˢ univ) ⊆ Ω →
      (∀ x ∈ X, ∀ v ∈ S, (x, v) ∈ closure (augmentedTransportGradient Y '' Z) →
        (x, v) ∈ closedBall b τ) →
      D.Controls s M₀ B₀ H d →
      Dr.Controls s M₀ B₀ H r → D.field.Controls s M₀ B₀ H Y →
      (∀ p ∈ D.field.carrier, (p.2, Y p) ∈ Dr.carrier) →
      MapsTo (fun p : InputVariables n ↦ (p.1.1, p.2.1)) U D.field.region →
      MapsTo (fun p : InputVariables n ↦ (p.1.2, p.2.1)) U D.field.region →
      MapsTo (fun p ↦ (p.2, Y p)) D.field.region Dr.region →
      (∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2)) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p)) →
      (∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖) →
      ∀ Q : ℝ, 1 ≤ Q → ∀ p : Variables n,
      (ℓ ≤ ‖p.2.2‖ → scaleFrequency (ℓ / ‖p.2.2‖) p ∈ X) →
      ∀ k ≤ s, ∀ I : Finset (Fin k), ∀ v : Fin k → Variables n,
      (∀ j ∈ I, (v j).1 = 0 ∧ (v j).2.1 = 0) →
      (∀ j ∉ I, (v j).2.2 = 0) →
      (1 + ‖p.2.2‖) ^ I.card *
        ‖iteratedFDeriv ℝ k (amplitude (regularizedCoefficients {withInitialMultiplier d r Y with high := h} χ Q) J u Ω S) p v‖ ≤
          C * H * ∏ j, ‖v j‖ := by
  obtain ⟨E, hE, he⟩ := exists_initialMultiplier_coefficientShellProfiles_of_norms
    (N := N) D Dr hs hM₀ hB₀
  obtain ⟨F, hF, hf⟩ := exists_rescaledRegularizedHigh_shellJetProfile
    hh htail hχ hcχ hε s hs
  let f : {Q : ℝ // 1 ≤ Q} → ℝ → ℝ := fun Q r ↦ h r * χ (r / Q.val)
  have hfs (Q) : ContDiff ℝ ∞ (f Q) := hh.mul (hχ.comp (contDiff_id.div_const Q.val))
  have hfz (Q) (r) (hr : r ≤ 1) : f Q r = 0 := by simp [f, hzero r hr]
  obtain ⟨C, hC, hb⟩ := exists_transportAmplitude_supported_global_mixed_bound_of_maskProfiles (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM (show 0 ≤ E + 1 by linarith) hδ hε hB hη hCupper hℓ hℓone hlow hS s hs
    f hfs hfz hF.le (fun Q t H ht hH r hr ↦ hf t Q.val H ht Q.property hH r hr)
  refine ⟨C, hC, ?_⟩
  intro d r Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hr hYnorm hfootY hl hrr hregion hscale huScale hJScale hupper
  have hreg' := hreg.withInitialMultiplier hr.smooth hYnorm.smooth hl hrr hregion
  have hp (p) (hp : p ∈ closedBall a ρ) :=
    (he d r Y H hH hcoeff hr hYnorm hfootY p (hfoot p hp)).homogeneous hE.le (zero_le_one.trans hH)
  intro Q hQ
  exact hb (withInitialMultiplier d r Y) Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg'.homogeneous hmap hsupp hR hXR hbuffer hshell hp hscale huScale hJScale hupper ⟨Q, hQ⟩

end JanetCartan.ContinuumNormalReduction.TransportSymbol
