module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.RemainderSobolev.MixedLow

/-!
# Primitive producers for both frequency regimes of the actual remainder

The error paragraph following `app:ch_background:eq:bg-real-symbol` requires
both a shell bound and a separate bound near zero. Here both are instantiated
from the same fixed chart data and primitive norms. No completed-amplitude
replacement is made, and the high norm occurs only once.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction TransportSymbol Pseudodifferential
variable {n N : ℕ}

/-- Joint smoothness, order-minus-one shells, and a global unweighted bound
for the original reflected Taylor remainder. Coefficient order is `r+2`,
geometric order is `r+4`, and fixed source-cutoff jets through `r+1` enter
the constant before the amplitude and its high norm. The shell component
uses the exact producer in `RemainderBounds`; the low-frequency component
uses `GlobalNormBounds` and `GlobalSmooth`. Consumer: the localized integer
Sobolev estimate following `app:ch_background:eq:bg-real-symbol`. -/
theorem exists_reflectedEntry_diagonalRemainder_joint_bounds_of_primitiveNorms
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
    {S : Set (Euclidean 2)} (hS : IsCompact S) (r : ℕ)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hzero : ∀ r, r ≤ 1 → h r = 0) (htail : ∀ r, 2 ≤ r → h r = 1)
    (basis : OrthonormalBasis (Fin n) ℝ (Euclidean n))
    (β : Euclidean n → ℝ) (hβ : ContDiff ℝ ∞ β)
    {Bβ : ℝ} (hBβ : 0 ≤ Bβ)
    (hβBound : ∀ k ≤ r + 1, ∀ y, ‖iteratedFDeriv ℝ k β y‖ ≤ Bβ)
    (i j : Fin n) :
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
      1 ≤ H → 1 + cNorm L (r + 4) Y ≤ B * H →
      PrimitiveRegularity d J U → MapsTo (inverseCoordinates u) Ω U →
      (∀ p ∈ U, d.measurement p.1.1 ≠ 0 → d.measurement p.1.2 ≠ 0 →
        d.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z) →
      IsOpen R → X ⊆ R →
      closure (augmentedTransportGradient Y '' Z) ∩ (R ×ˢ univ) ⊆ Ω →
      (∀ x ∈ X, ∀ v ∈ S, (x, v) ∈ Ω → (x, v) ∈ closedBall b τ) →
      D.Controls (r + 2) M₀ B₀ H d →
      (∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2)) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p)) →
      (∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖) →
      (closure (augmentedTransportGradient Y '' Z) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) →
      (∀ p : Variables n, ℓ ≤ ‖p.2.2‖ → scaleFrequency (ℓ / ‖p.2.2‖) p ∈ X) →
      ContDiff ℝ ∞ (fun p : Variables n ↦
        (diagonalRemainderAmplitude basis
          (fun x y ξ ↦ (reflectedSymbolAmplitude {d with high := h} J u Ω S
            (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) p.1 p.2.1 p.2.2) ∧
      HasAmplitudeShellBound
        (diagonalRemainderAmplitude basis
          (fun x y ξ ↦ (reflectedSymbolAmplitude {d with high := h} J u Ω S
            (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) (-1) r (C * H) ∧
      ∀ p : Variables n, ∀ k ≤ r,
        ‖iteratedFDeriv ℝ k (fun q : Variables n ↦
          (diagonalRemainderAmplitude basis
          (fun x y ξ ↦ (reflectedSymbolAmplitude {d with high := h} J u Ω S
            (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) q.1 q.2.1 q.2.2) p‖ ≤ C * H := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_transportAmplitude_global_mixed_bound_of_primitiveNorms (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hℓ hℓone hlow hS
    (r + 2) (by omega) hh hzero htail
  obtain ⟨C₁, hC₁, hlowBound⟩ := exists_reflectedEntry_diagonalRemainder_global_bound_of_mixed
    (N := N) r basis β hβ hBβ hβBound i j
  obtain ⟨C₂, hC₂, hshellBound⟩ := exists_reflectedEntry_diagonalRemainder_bound_of_primitiveNorms
    (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hℓ hℓone hlow hS
    r hh hzero htail basis β hβ hBβ hβBound i j
  refine ⟨C₂ + C₁ * C₀, by positivity, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
    hupper hpunctured hnormalize
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hhigh' : 1 + cNorm L (r + 2 + 2) Y ≤ B * H := by
    simpa [Nat.add_assoc] using hhigh
  have hm := hb d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh' hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale hupper
  have hreg' : PrimitiveRegularity {d with high := h} J U := {hreg with high := hh}
  have ha := (amplitude_smooth_and_derivatives_of_punctured_buffer
    {d with high := h} J u (augmentedTransportGradient Y) hΩ hreg' hu hmap
    (augmentedTransportGradient_inverseCoordinates Y u heq) hsupp hpunctured
    hzero hCupper hℓ hlow hupper hS).1
  have hr : ContDiff ℝ ∞ (reflectedSymbolAmplitude {d with high := h} J u Ω S) :=
    (ha.add (ha.comp (contDiff_fst.prodMk
      (contDiff_snd.fst.prodMk contDiff_snd.snd.neg)))).const_smul _
  have hc := Complex.ofRealCLM.contDiff.comp (((realMatrixEntry i j).contDiff.comp hr).comp
    (contDiff_fst.prodMk (contDiff_snd.fst.prodMk (contDiff_snd.snd.const_smul (2 * Real.pi)))))
  refine ⟨contDiff_diagonalRemainderAmplitude_joint basis _ β hc hβ, ?_, ?_⟩
  · have hs := hshellBound d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
      hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
      hupper hpunctured hnormalize
    intro t ht p hp₁ hp₂ k hk
    apply (hs t ht p hp₁ hp₂ k hk).trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hH₀
  · have hl := hlowBound {d with high := h} J u Ω S ha (C₀ * H) (by positivity)
      (fun p ↦ hm p (hnormalize p))
    intro p k hk
    apply (hl p k hk).trans
    calc
      C₁ * (C₀ * H) = (C₁ * C₀) * H := by ring
      _ ≤ (C₂ + C₁ * C₀) * H :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₂.le) hH₀

end JanetCartan.ContinuumRow.TransportKernel
