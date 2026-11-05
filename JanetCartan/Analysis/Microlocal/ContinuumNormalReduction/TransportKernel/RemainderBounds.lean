module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.RemainderBounds.MixedJets

/-!
# The actual reflected diagonal remainder

Quantitative order minus one for the Taylor/divergence remainder following
`app:ch_background:eq:bg-real-symbol`, retaining reflection and `k = 2πξ`.
The primitive-norm theorem below uses coefficient order `r+2` and geometric
order `r+4`, with one common high norm. Source-cutoff jets are explicit.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction TransportSymbol Pseudodifferential
variable {n N : ℕ}

/-- The mixed bounds produced by `GlobalNormBounds` imply the shell bounds of
the literal normalized reflected scalar entry, without an even-mask premise.
Source: `app:ch_background:eq:bg-real-symbol`. -/
theorem reflectedEntry_shellBound_of_mixed
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (ha : ContDiff ℝ ∞ (amplitude a J u Ω K))
    (s : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ p : Variables n, ∀ k ≤ s, ∀ I : Finset (Fin k),
      ∀ v : Fin k → Variables n,
      (∀ j ∈ I, (v j).1 = 0 ∧ (v j).2.1 = 0) →
      (∀ j ∉ I, (v j).2.2 = 0) →
      (1 + ‖p.2.2‖) ^ I.card * ‖iteratedFDeriv ℝ k (amplitude a J u Ω K) p v‖ ≤
        A * ∏ j, ‖v j‖)
    (i j : Fin n) :
    HasAmplitudeShellBound
      (fun x y ξ ↦ (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ))
      0 s (‖Complex.ofRealCLM.comp (realMatrixEntry i j)‖ *
        (4 * (2 * Real.pi) ^ n) * 2 ^ s * A) := by
  intro ρ _ p hp _ k hk
  let f (t : ℝ) := fun q : Variables n ↦ amplitude a J u Ω K (q.1, q.2.1, t • q.2.2)
  have hf (t : ℝ) : ContDiff ℝ ∞ (f t) :=
    ha.comp (contDiff_fst.prodMk (contDiff_snd.fst.prodMk (contDiff_snd.snd.const_smul t)))
  let t := 2 * Real.pi * ρ
  let L := Complex.ofRealCLM.comp (realMatrixEntry i j)
  let g := fun q ↦ (2 * (2 * Real.pi) ^ n) • (f t q + f (-t) q)
  have hg : ContDiff ℝ ∞ g := ((hf t).add (hf (-t))).const_smul _
  have he : (fun q : Variables n ↦
      (reflectedSymbolAmplitude a J u Ω K
        (q.1, q.2.1, (2 * Real.pi) • (ρ • q.2.2)) i j : ℂ)) = L ∘ g := by
    funext q
    change _ = ((g q) i j : ℂ)
    simp [g, f, t, reflectedSymbolAmplitude, smul_smul, mul_add]
  rw [he, Real.rpow_zero, one_mul]
  apply (L.norm_iteratedFDeriv_comp_left hg.contDiffAt (by simp)).trans
  have hgp : ‖iteratedFDeriv ℝ k g p‖ ≤
      (4 * (2 * Real.pi) ^ n) * 2 ^ s * A := by
    rw [show g = (2 * (2 * Real.pi) ^ n) • (f t + f (-t)) from rfl,
      iteratedFDeriv_const_smul_apply (i := k) (f := f t + f (-t)) (((hf t).add (hf (-t))).contDiffAt.of_le (by simp)),
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * (2 * Real.pi) ^ n),
      iteratedFDeriv_add_apply (i := k) (f := f t) (g := f (-t)) ((hf t).contDiffAt.of_le (by simp))
        ((hf (-t)).contDiffAt.of_le (by simp))]
    have h₁ := norm_iteratedFDeriv_frequencyScale_le_of_mixed
      _ ha s hA hb t p hp k hk
    have h₂ := norm_iteratedFDeriv_frequencyScale_le_of_mixed
      _ ha s hA hb (-t) p hp k hk
    calc
      _ ≤ (2 * (2 * Real.pi) ^ n) * (2 ^ s * A + 2 ^ s * A) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h₁ h₂)) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ‖L‖ * ((4 * (2 * Real.pi) ^ n) * 2 ^ s * A) :=
      mul_le_mul_of_nonneg_left hgp (norm_nonneg _)
    _ = _ := by ring

/-- The actual Taylor/divergence remainder has order minus one and costs two
amplitude derivatives. The sole analytic input here is exactly the mixed-jet
conclusion of `GlobalNormBounds`; the final theorem instantiates it.
Source: the paragraph following `app:ch_background:eq:bg-real-symbol`. -/
theorem reflectedEntry_diagonalRemainder_shellBound_of_mixed
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (ha : ContDiff ℝ ∞ (amplitude a J u Ω K))
    (r : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ p : Variables n, ∀ k ≤ r + 2, ∀ I : Finset (Fin k),
      ∀ v : Fin k → Variables n,
      (∀ j ∈ I, (v j).1 = 0 ∧ (v j).2.1 = 0) →
      (∀ j ∉ I, (v j).2.2 = 0) →
      (1 + ‖p.2.2‖) ^ I.card * ‖iteratedFDeriv ℝ k (amplitude a J u Ω K) p v‖ ≤
        A * ∏ j, ‖v j‖)
    (b : OrthonormalBasis (Fin n) ℝ (Euclidean n)) (β : Euclidean n → ℝ)
    (hβ : ContDiff ℝ ∞ β) {Bβ : ℝ} (hBβ : 0 ≤ Bβ)
    (hβBound : ∀ k ≤ r + 1, ∀ y, ‖iteratedFDeriv ℝ k β y‖ ≤ Bβ)
    (i j : Fin n) :
    HasAmplitudeShellBound
      (diagonalRemainderAmplitude b
        (fun x y ξ ↦ (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β)
      (-1) r
      (‖(2 * Real.pi * Complex.I)⁻¹‖ * n * 2 ^ (r + 1) * Bβ *
        (‖Complex.ofRealCLM.comp (realMatrixEntry i j)‖ *
          (4 * (2 * Real.pi) ^ n) * 2 ^ (r + 2) * A)) := by
  have hr : ContDiff ℝ ∞ (reflectedSymbolAmplitude a J u Ω K) :=
    (ha.add (ha.comp (contDiff_fst.prodMk
      (contDiff_snd.fst.prodMk contDiff_snd.snd.neg)))).const_smul _
  have hc := Complex.ofRealCLM.contDiff.comp (((realMatrixEntry i j).contDiff.comp hr).comp
    (contDiff_fst.prodMk (contDiff_snd.fst.prodMk (contDiff_snd.snd.const_smul (2 * Real.pi)))))
  simpa using HasAmplitudeShellBound.diagonalRemainderAmplitude b _ β hc hβ 0 r _ Bβ
    (by positivity) hBβ (reflectedEntry_shellBound_of_mixed a J u Ω K ha (r + 2) hA hb i j)
    hβBound

/-- Primitive finite norms produce the actual order-minus-one reflected
remainder. The fixed high mask and source-cutoff jets precede the constant;
coefficients use order `r+2`, geometry uses order `r+4`, and `H` occurs once.
The chart containment, conic identities and both support buffers are explicit.
No shell bound or remainder estimate is assumed. The consumer is the normal
kernel assembly following `app:ch_background:eq:bg-real-symbol`. -/
theorem exists_reflectedEntry_diagonalRemainder_bound_of_primitiveNorms
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
      HasAmplitudeShellBound
        (diagonalRemainderAmplitude basis
          (fun x y ξ ↦ (reflectedSymbolAmplitude {d with high := h} J u Ω S
            (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) (-1) r (C * H) := by
  obtain ⟨C, hC, hb⟩ := exists_transportAmplitude_global_mixed_bound_of_primitiveNorms (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hℓ hℓone hlow hS
    (r + 2) (by omega) hh hzero htail
  let E := ‖(2 * Real.pi * Complex.I)⁻¹‖ * n * 2 ^ (r + 1) * Bβ *
    (‖Complex.ofRealCLM.comp (realMatrixEntry i j)‖ *
      (4 * (2 * Real.pi) ^ n) * 2 ^ (r + 2) * C)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨E + 1, by positivity, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
    hupper hpunctured hnormalize
  have hhigh' : 1 + cNorm L (r + 2 + 2) Y ≤ B * H := by
    simpa [Nat.add_assoc] using hhigh
  have hm := hb d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh' hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale hupper
  have hreg' : PrimitiveRegularity {d with high := h} J U := {hreg with high := hh}
  have ha := (amplitude_smooth_and_derivatives_of_punctured_buffer
    {d with high := h} J u (augmentedTransportGradient Y) hΩ hreg' hu hmap
    (augmentedTransportGradient_inverseCoordinates Y u heq) hsupp hpunctured
    hzero hCupper hℓ hlow hupper hS).1
  have hrem := reflectedEntry_diagonalRemainder_shellBound_of_mixed
    {d with high := h} J u Ω S ha r (mul_nonneg hC.le (zero_le_one.trans hH))
    (fun p ↦ hm p (hnormalize p)) basis β hβ hBβ hβBound i j
  have hrem' : HasAmplitudeShellBound
      (diagonalRemainderAmplitude basis
        (fun x y ξ ↦ (reflectedSymbolAmplitude {d with high := h} J u Ω S
          (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β) (-1) r (E * H) := by
    simpa only [E, mul_assoc] using hrem
  intro t ht p hp₁ hp₂ k hk
  exact (hrem' t ht p hp₁ hp₂ k hk).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (zero_le_one.trans hH)) (Real.rpow_nonneg (by linarith) _))

end JanetCartan.ContinuumRow.TransportKernel
