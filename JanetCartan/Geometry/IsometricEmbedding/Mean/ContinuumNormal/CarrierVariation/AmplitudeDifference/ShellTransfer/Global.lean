module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.AmplitudeDifference.Integration
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.GlobalSmooth
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.SupportedShell.Localization

/-!
# Transfer of supported shell differences to global amplitude jets

The shell input for `app:ch_osc:prop:osc-normal`, Step 4', is the finite norm
of the substituted primitive density difference, uniformly over dilations.
Its producer is `jc-carrier-amplitude-primitive-density`; the parent must
instantiate that estimate. Only supported points on the fixed positive shell
must lie in the compact norm domain. The cone vertex is handled by the
primitive high-mask gap, and the spectator measure is unchanged.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
open ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

private theorem norm_frequencyDilation_inverse_le_one {t : ℝ} (ht : 1 ≤ t) :
    ‖(frequencyDilationEquiv (n := n) t (by linarith)).symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖scaleFrequency t⁻¹ p‖ ≤ 1 * ‖p‖
  simp only [scaleFrequency, Prod.norm_def, one_mul]
  apply max_le_max (le_refl _)
  apply max_le_max (le_refl _)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ t⁻¹)]
  exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ ht)

private theorem norm_iteratedFDeriv_of_rescaling_le
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f g : Variables n → G) (hg : ContDiff ℝ ∞ g)
    {t : ℝ} (ht : 1 ≤ t) (he : ∀ p, f (scaleFrequency t p) = g p)
    (p : Variables n) (j : ℕ) :
    ‖iteratedFDeriv ℝ j f (scaleFrequency t p)‖ ≤ ‖iteratedFDeriv ℝ j g p‖ := by
  let e := frequencyDilationEquiv (n := n) t (by linarith)
  have hf : f = g ∘ e.symm.toContinuousLinearMap := by
    funext q
    change f q = g (scaleFrequency t⁻¹ q)
    simpa [scaleFrequency, smul_smul,
      show t ≠ 0 by linarith] using he (scaleFrequency t⁻¹ q)
  rw [hf]
  rw [e.symm.toContinuousLinearMap.iteratedFDeriv_comp_right hg _ (by simp)]
  have hinv : e.symm.toContinuousLinearMap (scaleFrequency t p) = p := e.symm_apply_apply p
  rw [hinv]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (norm_frequencyDilation_inverse_le_one ht))

section PrimitiveInputs
variable (a : Fin 2 → Coefficients n N) (J : Fin 2 → InputVariables n → ℝ)
  (u : Fin 2 → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
  (F : Fin 2 → InputVariables n → Variables n × Euclidean 2)
  {Ω : Set (Variables n × Euclidean 2)} (W Z : Fin 2 → Set (InputVariables n))
  (hΩ : IsOpen Ω) (hreg : ∀ i, PrimitiveRegularity (a i) (J i) (W i))
  (hu : ∀ i, ContDiffOn ℝ ∞ (u i) Ω)
  (hmap : ∀ i, MapsTo (inverseCoordinates (u i)) Ω (W i))
  (hright : ∀ i p, p ∈ Ω → F i (inverseCoordinates (u i) p) = p)
  (hsupp : ∀ i p, p ∈ W i → (a i).measurement p.1.1 ≠ 0 →
    (a i).measurement p.1.2 ≠ 0 →
    (a i).angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z i)
  (hbuffer : ∀ i, closure (F i '' Z i) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω)
  (hzero : ∀ i r, r ≤ 1 → (a i).high r = 0)
  {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ)
  (hlow : Cupper * ℓ ≤ 1)
  (hupper : ∀ i p, p ∈ Ω → ‖(u i p).2‖ ≤ Cupper * ‖p.1.2.2‖)
  (hscale : ∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
  (huScale : ∀ i t, 0 < t → ∀ p ∈ Ω,
    u i (scaleFrequency t p.1, p.2) = ((u i p).1, t • (u i p).2))
  (hJScale : ∀ i t, 0 < t → ∀ p ∈ Ω,
    J i (scaleInput t (inverseCoordinates (u i) p)) = t * J i (inverseCoordinates (u i) p))

include hΩ hreg hu hmap hright hsupp hbuffer hzero hCupper hℓ hlow hupper
  hscale huScale hJScale

/-- Uniform compact-shell density differences bound every global joint jet
of the literal spectator amplitude difference. Smoothness and low-frequency
vanishing follow from primitive regularity, masks and the punctured buffer.
The sole quantitative difference input is supplied by the primitive-density
task, and must be instantiated by the parent. Consumer: the physical complex
and reflected bounds in `ShellTransfer`. Source:
`app:ch_osc:prop:osc-normal`, Step 4', and
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem amplitude_sub_global_jets_of_supported_shell
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    {Q : Set (Variables n × Euclidean 2)} (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hshell : ∀ p : Variables n, ‖p.2.2‖ = ℓ → ∀ v ∈ S,
      (p, v) ∈ closure (F 0 '' Z 0) ∪ closure (F 1 '' Z 1) → (p, v) ∈ Q)
    (s : ℕ) {B d : ℝ} (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hb : ∀ t : ℝ, 1 ≤ t → cNorm Q s
      (fun p ↦ inputDensity (rescaledCoefficients (a 0) t) (J 0) (inverseCoordinates (u 0) p) -
        inputDensity (rescaledCoefficients (a 1) t) (J 1) (inverseCoordinates (u 1) p)) ≤ B * d) :
    ContDiff ℝ ∞ (amplitude (a 0) (J 0) (u 0) Ω S - amplitude (a 1) (J 1) (u 1) Ω S) ∧
    ∀ p : Variables n, ∀ j ≤ s,
      ‖iteratedFDeriv ℝ j
        (amplitude (a 0) (J 0) (u 0) Ω S - amplitude (a 1) (J 1) (u 1) Ω S) p‖ ≤
        B * d * volume.real S := by
  have hext (i : Fin 2) : ContDiff ℝ ∞ (extendedDensity (a i) (J i) (u i) Ω) :=
    extendedDensity_contDiff_of_punctured_buffer (a i) (J i) (u i) (F i)
      hΩ (hreg i) (hu i) (hmap i) (hright i) (hsupp i) (hbuffer i)
      (hzero i) hCupper hℓ hlow (hupper i)
  have ha (i : Fin 2) : ContDiff ℝ ∞ (amplitude (a i) (J i) (u i) Ω S) :=
    (amplitude_smooth_and_derivatives_of_punctured_buffer (a i) (J i) (u i) (F i)
      hΩ (hreg i) (hu i) (hmap i) (hright i) (hsupp i) (hbuffer i)
      (hzero i) hCupper hℓ hlow (hupper i) hS).1
  have hextScale (t : ℝ) (ht : 0 < t) (i : Fin 2) :
      ContDiff ℝ ∞ (extendedDensity (rescaledCoefficients (a i) t) (J i) (u i) Ω) := by
    have he : extendedDensity (rescaledCoefficients (a i) t) (J i) (u i) Ω =
        fun p ↦ extendedDensity (a i) (J i) (u i) Ω (scaleFrequency t p.1, p.2) :=
      funext fun p ↦ (extendedDensity_rescaled (a i) (J i) (u i) Ω ht
        (hscale t ht) (huScale i t ht) (hJScale i t ht) p).symm
    rw [he]
    exact (hext i).comp (((frequencyDilationEquiv t ht.ne').contDiff.comp contDiff_fst).prodMk
      contDiff_snd)
  have haScale (t : ℝ) (ht : 0 < t) (i : Fin 2) :
      ContDiff ℝ ∞ (amplitude (rescaledCoefficients (a i) t) (J i) (u i) Ω S) := by
    have he : amplitude (rescaledCoefficients (a i) t) (J i) (u i) Ω S =
        amplitude (a i) (J i) (u i) Ω S ∘ frequencyDilationEquiv t ht.ne' :=
      funext fun p ↦ (amplitude_rescaled (a i) (J i) (u i) Ω S ht
        (hscale t ht) (huScale i t ht) (hJScale i t ht) p).symm
    rw [he]
    exact (ha i).comp (frequencyDilationEquiv t ht.ne').contDiff
  have hbound (t : ℝ) (ht : 1 ≤ t) (p : Variables n) (hp : ‖p.2.2‖ = ℓ)
      (j : ℕ) (hj : j ≤ s) :
      ‖iteratedFDeriv ℝ j
        (amplitude (rescaledCoefficients (a 0) t) (J 0) (u 0) Ω S -
          amplitude (rescaledCoefficients (a 1) t) (J 1) (u 1) Ω S) p‖ ≤
        B * d * volume.real S := by
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    rw [amplitude_sub_eq_spectatorIntegral_sub _ J u Ω hS (hextScale t ht0)]
    apply norm_iteratedFDeriv_spectatorIntegral_le
      ((hextScale t ht0 0).sub (hextScale t ht0 1)) hS j p
    intro v hv
    change ‖iteratedFDeriv ℝ j
      (extendedDensity (rescaledCoefficients (a 0) t) (J 0) (u 0) Ω -
        extendedDensity (rescaledCoefficients (a 1) t) (J 1) (u 1) Ω) (p, v)‖ ≤ B * d
    by_cases hsupport : (p, v) ∈ closure (F 0 '' Z 0) ∪ closure (F 1 '' Z 1)
    · have hpQ := hshell p hp v hv hsupport
      rw [iteratedFDeriv_extendedDensity_sub_of_mem
        (rescaledCoefficients (a 0) t) (rescaledCoefficients (a 1) t)
        (J 0) (J 1) (u 0) (u 1) hΩ (hQΩ hpQ) j]
      apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hQ ?_ hpQ hj).trans (hb t ht)
      intro q hq
      have hr (i : Fin 2) := ((inputDensity_contDiffOn ((hreg i).rescaled t)).comp
        (inverseCoordinates_contDiffOn (hu i)) (hmap i)).contDiffAt (hΩ.mem_nhds (hQΩ hq))
      exact ((hr 0).sub (hr 1)).of_le (by simp)
    · rw [iteratedFDeriv_sub_apply
        ((hextScale t ht0 0).contDiffAt.of_le (by simp))
        ((hextScale t ht0 1).contDiffAt.of_le (by simp))]
      have hz (i : Fin 2) (hi : (p, v) ∉ closure (F i '' Z i)) :=
        iteratedFDeriv_extendedDensity_eq_zero_off_closure_image
          (rescaledCoefficients (a i) t) (J i) (u i) (F i) (hmap i) (hright i)
          (fun q hq h₁ h₂ h₃ _ ↦ hsupp i q hq h₁ h₂ h₃) hi j
      rw [hz 0 (fun h ↦ hsupport (Or.inl h)), hz 1 (fun h ↦ hsupport (Or.inr h))]
      simpa using mul_nonneg hB hd
  refine ⟨(ha 0).sub (ha 1), ?_⟩
  intro p j hj
  by_cases hp : ‖p.2.2‖ < ℓ
  · rw [iteratedFDeriv_sub_apply ((ha 0).contDiffAt.of_le (by simp))
      ((ha 1).contDiffAt.of_le (by simp))]
    rw [iteratedFDeriv_amplitude_eq_zero_of_low_frequency (a 0) (J 0) (u 0) Ω S
      (hzero 0) hCupper hlow (hupper 0) p hp j,
      iteratedFDeriv_amplitude_eq_zero_of_low_frequency (a 1) (J 1) (u 1) Ω S
      (hzero 1) hCupper hlow (hupper 1) p hp j]
    simp only [sub_self, norm_zero]
    positivity
  · have hr : ℓ ≤ ‖p.2.2‖ := le_of_not_gt hp
    have hr0 := hℓ.trans_le hr
    let t := ‖p.2.2‖ / ℓ
    have ht : 1 ≤ t := (le_div_iff₀ hℓ).mpr (by simpa using hr)
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    let q := scaleFrequency (ℓ / ‖p.2.2‖) p
    have hq : ‖q.2.2‖ = ℓ := by
      dsimp [q, scaleFrequency]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hℓ hr0), div_mul_cancel₀ _ hr0.ne']
    have hback : scaleFrequency t q = p := by
      simp [q, t, scaleFrequency, smul_smul, div_mul_div_cancel₀ hℓ.ne', hr0.ne']
    rw [← hback]
    apply (norm_iteratedFDeriv_of_rescaling_le _ _
      ((haScale t ht0 0).sub (haScale t ht0 1)) ht ?_ q j).trans (hbound t ht q hq j hj)
    intro x
    exact congrArg₂ (fun A B ↦ A - B)
      (amplitude_rescaled (a 0) (J 0) (u 0) Ω S ht0
        (hscale t ht0) (huScale 0 t ht0) (hJScale 0 t ht0) x)
      (amplitude_rescaled (a 1) (J 1) (u 1) Ω S ht0
        (hscale t ht0) (huScale 1 t ht0) (hJScale 1 t ht0) x)

end PrimitiveInputs
end JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
