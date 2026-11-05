module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Completion
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.CompletionBounds
/-!
# Quantitative reflected completion error

For the bounded-frequency term following `app:ch_background:eq:bg-symbol`,
reflection doubles the complex discrepancy bound and keeps the literal PDO
normalization. The final theorem instantiates the existing primitive-norm
producer; it assumes no amplitude, inverse-jet, or discrepancy estimate.
The geometric owner must supply the two frequency comparisons, relative
support buffer and annular chart containment. The physical working set must
contain the reflected frequencies; the angular mask need not be even.
These finite joint-jet estimates do not yet assert Sobolev gains of the kernel.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius ComplexConjugate
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction TransportSymbol
variable {n N : ℕ}
private def frequencyReflection : Variables n ≃ₗᵢ[ℝ] Variables n where
  toLinearEquiv := {
    toFun := fun p ↦ (p.1, p.2.1, -p.2.2)
    invFun := fun p ↦ (p.1, p.2.1, -p.2.2)
    left_inv := by intro p; simp
    right_inv := by intro p; simp
    map_add' := by intros; simp [add_comm]
    map_smul' := by intros; simp }
  norm_map' := by intro p; simp [Prod.norm_def]

private theorem completionDiscrepancy_contDiffAt
    (d : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    {R X : Set (Variables n)} (hR : IsOpen R)
    (ha : ContDiffOn ℝ ∞ (amplitude d J u Ω S) R)
    (hh : ContDiffOn ℝ ∞ (amplitude (homogeneousCoefficients d) J u Ω S) R)
    {Cupper Clower ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hClower : 0 < Clower)
    (hℓone : ℓ ≤ 1) (hlow : Cupper * ℓ ≤ 1)
    (hXR : completionAnnulus X ℓ Clower ⊆ R)
    (hzero : ∀ r : ℝ, r ≤ 1 → d.high r = 0)
    (hone : ∀ r : ℝ, 2 ≤ r → d.high r = 1)
    (hupper : ∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖)
    (hlower : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ Clower * ‖(u p).2‖)
    {x : Variables n} (hx : x ∈ X) :
    ContDiffAt ℝ ∞ (fun p ↦ amplitude d J u Ω S p - completedAmplitude d J u Ω S p) x := by
  by_cases hlowx : ‖x.2.2‖ < ℓ
  · apply (contDiffAt_const (c := (0 : Matrix (Fin n) (Fin n) ℝ))).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_snd.snd.norm continuous_const).mem_nhds hlowx]
      with p hp
    rw [amplitude_eq_zero_of_low_frequency d J u Ω S hzero hupper p
      ((mul_le_mul_of_nonneg_left hp.le hCupper).trans hlow)]
    simp [completedAmplitude, completionCutoff_eq_zero (hp.le.trans hℓone)]
  by_cases hhighx : max 2 (2 * Clower) < ‖x.2.2‖
  · apply (contDiffAt_const (c := (0 : Matrix (Fin n) (Fin n) ℝ))).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const continuous_snd.snd.norm).mem_nhds hhighx]
      with p hp
    exact sub_eq_zero.mpr (amplitude_eq_completed_of_large_frequency
      d J u Ω S hone hClower hlower p hp.le)
  have hxR := hXR ⟨hx, le_of_not_gt hlowx, le_of_not_gt hhighx⟩
  exact (ha.contDiffAt (hR.mem_nhds hxR)).sub
    (((completionCutoff_contDiff.comp contDiff_snd.snd).contDiffAt).smul
      (hh.contDiffAt (hR.mem_nhds hxR)))

/-- Reflection of the actual completion discrepancy retains the exact
normalization, with no frequency-evenness hypothesis
(`app:ch_background:eq:bg-symbol`). -/
theorem norm_iteratedFDeriv_reflectedCompletionError_le
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (p : Variables n) (r : ℕ)
    (h₁ : ContDiffAt ℝ ∞
      (fun q ↦ amplitude a J u Ω K q - completedAmplitude a J u Ω K q) p)
    (h₂ : ContDiffAt ℝ ∞
      (fun q ↦ amplitude a J u Ω K q - completedAmplitude a J u Ω K q)
      (p.1, p.2.1, -p.2.2)) :
    ‖iteratedFDeriv ℝ r (reflectedCompletionError a J u Ω K) p‖ ≤
      (2 * (2 * Real.pi) ^ n) *
        (‖iteratedFDeriv ℝ r
          (fun q ↦ amplitude a J u Ω K q - completedAmplitude a J u Ω K q) p‖ +
         ‖iteratedFDeriv ℝ r
          (fun q ↦ amplitude a J u Ω K q - completedAmplitude a J u Ω K q)
          (p.1, p.2.1, -p.2.2)‖) := by
  let f := fun q ↦ amplitude a J u Ω K q - completedAmplitude a J u Ω K q
  let L : Variables n ≃ₗᵢ[ℝ] Variables n := frequencyReflection
  have he : reflectedCompletionError a J u Ω K =
      (2 * (2 * Real.pi) ^ n) • (f + f ∘ L) := by
    funext q
    dsimp [reflectedCompletionError, reflectedSymbolAmplitude,
      completedReflectedAmplitude, f, L, frequencyReflection]
    module
  have h₂' : ContDiffAt ℝ ∞ (f ∘ L) p := h₂.comp p L.contDiff.contDiffAt
  have h₁' : ContDiffAt ℝ ∞ f p := h₁
  rw [he, iteratedFDeriv_const_smul_apply (i := r) (f := f + f ∘ L)
    ((h₁'.add h₂').of_le (by simp)), norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 2 * (2 * Real.pi) ^ n),
    iteratedFDeriv_add_apply (i := r) (f := f) (g := f ∘ L) (h₁'.of_le (by simp)) (h₂'.of_le (by simp))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_add_le _ _).trans (by rw [L.norm_iteratedFDeriv_comp_right f p r]; rfl)

/-- Uniform joint jets of the normalized real completion error, directly from
primitive finite norms. The one-high factor and geometric shift two of
`TransportSymbol.exists_transportCompletion_discrepancy_bound_of_primitiveNorms`
are preserved. Reflection contributes the fixed factor `4 (2π)^n`.
This closes the amplitude-jet part of the bounded-frequency correction in
`app:ch_background:eq:bg-real-symbol`; its operator gains remain a consumer
obligation. No evenness of the angular mask or output-measure change is used. -/
theorem exists_reflectedCompletionError_bound_of_primitiveNorms
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
    {Cupper Clower ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hClower : 0 < Clower)
    (hℓ : 0 < ℓ) (hℓone : ℓ ≤ 1) (hlow : Cupper * ℓ ≤ 1)
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
      PrimitiveRegularity d J U → MapsTo (inverseCoordinates u) Ω U →
      (∀ p ∈ U, d.measurement p.1.1 ≠ 0 → d.measurement p.1.2 ≠ 0 →
        d.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z) →
      IsOpen R → completionAnnulus X ℓ Clower ⊆ R →
      closure (augmentedTransportGradient Y '' Z) ∩ (R ×ˢ univ) ⊆ Ω →
      (∀ x ∈ completionAnnulus X ℓ Clower, ∀ v ∈ S, (x, v) ∈ Ω → (x, v) ∈ closedBall b τ) →
      D.Controls s M₀ B₀ H d →
      (∀ r : ℝ, r ≤ 1 → d.high r = 0) →
      (∀ r : ℝ, 2 ≤ r → d.high r = 1) →
      (∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖) →
      (∀ p ∈ Ω, ‖p.1.2.2‖ ≤ Clower * ‖(u p).2‖) →
      (∀ x ∈ X, (x.1, x.2.1, -x.2.2) ∈ X) →
      ∀ x ∈ X, ∀ k ≤ s,
        ‖iteratedFDeriv ℝ k (reflectedCompletionError d J u Ω S) x‖ ≤ C * H := by
  obtain ⟨C, hC, hb⟩ := exists_transportCompletion_discrepancy_bound_of_primitiveNorms
    (N := N) c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hClower hℓ hℓone hlow hS s hs
  refine ⟨(4 * (2 * Real.pi) ^ n) * C, by positivity, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hzero hone hupper hlower hreflect
  have hbound := hb d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hzero hone hupper hlower
  have hright := augmentedTransportGradient_inverseCoordinates Y u heq
  have ha := amplitude_contDiffOn_of_relative_buffer d J u (augmentedTransportGradient Y)
    hΩ hR hreg hu hmap hright (fun p hp h₁ h₂ h₃ _ ↦ hsupp p hp h₁ h₂ h₃) hbuffer hS
  have hh := amplitude_contDiffOn_of_relative_buffer (homogeneousCoefficients d) J u
    (augmentedTransportGradient Y) hΩ hR hreg.homogeneous hu hmap hright
    (fun p hp h₁ h₂ h₃ _ ↦ hsupp p hp h₁ h₂ h₃) hbuffer hS
  have hsm (x : Variables n) (hx : x ∈ X) := completionDiscrepancy_contDiffAt d J u Ω S
    hR ha hh hCupper hClower hℓone hlow hXR hzero hone hupper hlower hx
  intro x hx k hk
  calc
    _ ≤ (2 * (2 * Real.pi) ^ n) *
        (‖iteratedFDeriv ℝ k
          (fun p ↦ amplitude d J u Ω S p - completedAmplitude d J u Ω S p) x‖ +
         ‖iteratedFDeriv ℝ k
          (fun p ↦ amplitude d J u Ω S p - completedAmplitude d J u Ω S p)
          (x.1, x.2.1, -x.2.2)‖) :=
      norm_iteratedFDeriv_reflectedCompletionError_le d J u Ω S x k
        (hsm x hx) (hsm _ (hreflect x hx))
    _ ≤ (2 * (2 * Real.pi) ^ n) * (C * H + C * H) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (hbound x hx k hk) (hbound _ (hreflect x hx) k hk)
    _ = _ := by ring

private def positionSwap : Variables n ≃ₗᵢ[ℝ] Variables n where
  toLinearEquiv := {
    toFun := fun p ↦ (p.2.1, p.1, p.2.2)
    invFun := fun p ↦ (p.2.1, p.1, p.2.2)
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  norm_map' := by intro p; simp only [Prod.norm_def]; exact max_left_comm _ _ _
private def matrixTranspose :
    Matrix (Fin n) (Fin n) ℝ ≃ₗᵢ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toLinearEquiv := Matrix.transposeLinearEquiv _ _ _ _
  norm_map' := Matrix.frobenius_norm_transpose

/-- The conjugate-transpose correction amplitude has exactly the same joint
jet norms at the reversed positions. There is no derivative loss in its
literal adjoint (`app:ch_background:eq:bg-real-symbol`). -/
theorem norm_iteratedFDeriv_adjoint_reflectedCompletionError
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (p : Variables n) (r : ℕ) :
    ‖iteratedFDeriv ℝ r (fun q : Variables n ↦
      (reflectedCompletionError a J u Ω K (q.2.1, q.1, q.2.2)).transpose) p‖ =
      ‖iteratedFDeriv ℝ r (reflectedCompletionError a J u Ω K) (p.2.1, p.1, p.2.2)‖ := by
  change ‖iteratedFDeriv ℝ r ((matrixTranspose (n := n)) ∘
    ((reflectedCompletionError a J u Ω K) ∘ (positionSwap (n := n)))) p‖ = _
  rw [matrixTranspose.norm_iteratedFDeriv_comp_left,
    positionSwap.norm_iteratedFDeriv_comp_right]
  rfl

/-- The reversed matrix amplitude is the actual conjugate-transpose kernel,
with the same Fourier normalization. Thus its jet bound controls the literal
adjoint correction (`app:ch_background:eq:bg-real-symbol`). -/
theorem completionErrorKernel_adjoint_eq_amplitudeKernel
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (i j : Fin n) (x y : Euclidean n) :
    conj (completionErrorKernel a J u Ω K j i y x) =
      Pseudodifferential.amplitudeKernel (fun x y ξ ↦
        (reflectedCompletionError a J u Ω K (y, x, (2 * Real.pi) • ξ) j i : ℂ)) x y := by
  rw [amplitudeKernel_eq_physicalFrequency_integral
    (fun x y k ↦ (reflectedCompletionError a J u Ω K (y, x, k) j i : ℂ)) x y]
  unfold completionErrorKernel
  rw [map_mul, map_inv₀, map_pow, map_mul, Complex.conj_ofReal,
    Complex.conj_ofNat, ← integral_conj]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with k
  simp only [map_mul, Complex.conj_ofReal]
  congr 1
  simp only [NormalComparison.oscillatoryFactor, one_mul, ← Complex.exp_conj,
    map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  simp only [inner_sub_left, Complex.ofReal_sub]
  ring

end JanetCartan.ContinuumRow.TransportKernel
