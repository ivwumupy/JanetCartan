module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Leakage.Support
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.Integral
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev.Basic

/-!
# Compact kernels for the literal retarded shell estimates

Joint smoothness and compact base supports for `app:ch_regular:eq:chain-tail`
are derived from the primitive weights, symbols and regularizer. A continuous
linear coordinate equivalence transports the actual kernel to the existing
Cartesian jet spaces; no alternative inner product on those spaces is used.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
attribute [local fun_prop] ContDiff.inner
namespace JanetCartan.FiniteChain.Retarded.Leakage
open LocalizedKernel KernelDecay

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem contDiff_normalizedIntegrand_bases (upper : Bool)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi))
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (fun p : ((ℝ × E) × (ℝ × E)) × (ℝ × TangentialVariables E) =>
      normalizedIntegrand upper 1 α β mi mo r p.1.1 p.1.2 p.2) := by
  have hi' : ContDiff ℝ ∞ (fun p : ((ℝ × E) × (ℝ × E)) × (ℝ × TangentialVariables E) =>
      mi p.1.1 p.2.2.2.2) := hi.comp
        (show ContDiff ℝ ∞ (fun p : ((ℝ × E) × (ℝ × E)) × (ℝ × TangentialVariables E) =>
          (p.1.1, p.2.2.2.2)) from by fun_prop)
  have ho' : ContDiff ℝ ∞ (fun p : ((ℝ × E) × (ℝ × E)) × (ℝ × TangentialVariables E) =>
      mo p.1.2 p.2.2.2.1) := ho.comp
        (show ContDiff ℝ ∞ (fun p : ((ℝ × E) × (ℝ × E)) × (ℝ × TangentialVariables E) =>
          (p.1.2, p.2.2.2.1)) from by fun_prop)
  have hcoe : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  cases upper <;>
    simp only [normalizedIntegrand, normalizedAmplitude, literalPhase, lowerAmplitude,
      upperAmplitude, Localization.phaseOscillation, packedPhase, packedUpperPhase,
      phase, adjointPhase, Bool.false_eq_true, ↓reduceIte, one_smul] <;> fun_prop

/-- Smoothness in both external bases of the concrete Fourier kernel.
All parameter domination comes from primitive common compact carriers
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem contDiff_fourierKernel_joint (upper : Bool)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi))
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (hr : ContDiff ℝ ∞ r)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β)
    (hsi : HasCompactSupport (Function.uncurry mi)) (hsr : HasCompactSupport r) :
    ContDiff ℝ ∞ (fun p : (ℝ × E) × (ℝ × E) =>
      if upper then upperFourierKernel α β mi mo r p.1 p.2
      else lowerFourierKernel α β mi mo r p.1 p.2) := by
  let Ki := Prod.snd '' tsupport (Function.uncurry mi)
  have hKi : IsCompact Ki := hsi.isCompact.image continuous_snd
  have hslice (xi : ℝ × E) : tsupport (fun ξ => mi xi ((1 : ℝ) • ξ)) ⊆ Ki := by
    simp only [one_smul]
    apply closure_minimal _ hKi.isClosed
    intro ξ hξ
    exact ⟨(xi, ξ), subset_tsupport (Function.uncurry mi) hξ, rfl⟩
  let K := amplitudeCarrier (tsupport α) (tsupport β) (tsupport r) Ki
  have hK : IsCompact K := isCompact_amplitudeCarrier hsα hsβ hsr hKi
  let μ : Measure (ℝ × TangentialVariables E) :=
    (volume.prod volume).restrict (Ici (0 : ℝ) ×ˢ (univ : Set (TangentialVariables E)))
  have hf := contDiff_normalizedIntegrand_bases upper α β mi mo r hα hβ hi ho hr
  have hz (p : (ℝ × E) × (ℝ × E)) (x : ℝ × TangentialVariables E) (hx : x ∉ K) :
      normalizedIntegrand upper 1 α β mi mo r p.1 p.2 x = 0 :=
    normalizedIntegrand_eq_zero_off_carrier upper 1 α β mi mo r p.1
      hsα hsβ hsr hKi Subset.rfl Subset.rfl (by simp) (hslice p.1) p.2 x hx
  have he : (fun p : (ℝ × E) × (ℝ × E) =>
      if upper then upperFourierKernel α β mi mo r p.1 p.2
      else lowerFourierKernel α β mi mo r p.1 p.2) =
      fun p => ((normalization (E := E)) ^ 2 : ℝ) •
        ∫ x, normalizedIntegrand upper 1 α β mi mo r p.1 p.2 x ∂μ := by
    funext p
    have hc : HasCompactSupport (normalizedAmplitude upper 1 α β mi mo r p.1 p.2) :=
      hK.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_normalizedAmplitude_subset upper 1 α β mi mo r p.1 p.2
          hsα hsβ hsr hKi Subset.rfl Subset.rfl (by simp) (hslice p.1))
    simpa only [one_pow, mul_one, HalfSpace.halfSpaceOscillatoryIntegral,
      HalfSpace.halfSpaceIntegral, normalizedIntegrand, μ] using
      fourierKernel_eq_halfSpace upper zero_lt_one α β mi mo r p.1 p.2
        (contDiff_normalizedAmplitude upper 1 α β mi mo r hα hβ hi ho hr p.1 p.2) hc
  rw [he]
  exact (contDiff_integral_commonCarrier (μ := μ) hf hK hz).const_smul _

/-- The regularized kernel retains the right symbol's input base support,
even though its identity contribution has output tails
(`app:ch_regular:eq:chain-tail`). -/
theorem fourierKernel_eq_zero_off_input (upper : Bool)
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo : ℝ × E) (hx : xi ∉ Prod.fst '' tsupport (Function.uncurry mi)) :
    (if upper then upperFourierKernel α β mi mo r xi xo
      else lowerFourierKernel α β mi mo r xi xo) = 0 := by
  have hz (ξ : ℝ × E) : mi xi ξ = 0 :=
    image_eq_zero_of_notMem_tsupport (f := Function.uncurry mi)
      (fun h => hx ⟨(xi, ξ), h, rfl⟩)
  cases upper <;> simp [lowerFourierKernel, upperFourierKernel,
    lowerIntegrand, upperIntegrand, lowerAmplitude, upperAmplitude, hz]

/-- Joint smoothness of the kernel with the fixed physical output cutoff
(`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_baseCutFourierKernel (upper : Bool)
    (χ α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi))
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (hr : ContDiff ℝ ∞ r)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β)
    (hsi : HasCompactSupport (Function.uncurry mi)) (hsr : HasCompactSupport r) :
    ContDiff ℝ ∞ (Function.uncurry (baseCutFourierKernel upper χ α β mi mo r)) :=
  (Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_snd)).mul
    (contDiff_fourierKernel_joint upper α β mi mo r hα hβ hi ho hr hsα hsβ hsi hsr)

/-- Actual compact kernel in the existing Cartesian coordinates. The
coordinate equivalence is explicit; the integral measure is supplied to
`KernelSobolev` by the consumer (`app:ch_regular:eq:chain-tail`). -/
def supportedFourierKernel {n : ℕ} (J : (Fin n → ℝ) ≃L[ℝ] E) (upper : Bool)
    (χ α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β)
    (hi : ContDiff ℝ ∞ (Function.uncurry mi))
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (hr : ContDiff ℝ ∞ r)
    (hsχ : HasCompactSupport χ) (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β)
    (hsi : HasCompactSupport (Function.uncurry mi)) (hsr : HasCompactSupport r) :
    KernelSobolev.SupportedSmoothKernel n n where
  toFun x y := baseCutFourierKernel upper χ α β mi mo r (y.2, J y.1) (x.1, J x.2)
  smooth := (contDiff_baseCutFourierKernel upper χ α β mi mo r hχ hα hβ hi ho hr
    hsα hsβ hsi hsr).comp
      ((contDiff_snd.snd.prodMk (J.contDiff.comp contDiff_snd.fst)).prodMk
        (contDiff_fst.fst.prodMk (J.contDiff.comp contDiff_fst.snd)))
  inputSupport := (fun y : (Fin n → ℝ) × ℝ => (y.2, J y.1)) ⁻¹'
    (Prod.fst '' tsupport (Function.uncurry mi))
  outputSupport := (fun x : ℝ × (Fin n → ℝ) => (x.1, J x.2)) ⁻¹' tsupport χ
  compact_inputSupport := by
    let H := (Homeomorph.prodComm (Fin n → ℝ) ℝ).trans
      ((Homeomorph.refl ℝ).prodCongr J.toHomeomorph)
    exact H.isCompact_preimage.mpr (hsi.isCompact.image continuous_fst)
  compact_outputSupport := by
    let H := (Homeomorph.refl ℝ).prodCongr J.toHomeomorph
    exact H.isCompact_preimage.mpr hsχ
  zero_off_input x y hy := by
    unfold baseCutFourierKernel
    rw [fourierKernel_eq_zero_off_input upper α β mi mo r (y.2, J y.1) (x.1, J x.2) hy,
      mul_zero]
  zero_off_output x y hx := by
    have hz : χ (x.1, J x.2) = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [baseCutFourierKernel, hz]

end JanetCartan.FiniteChain.Retarded.Leakage
