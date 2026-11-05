module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.Factorization
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.BufferedGeometry.Supports
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Localizers.PhysicalMasks

/-!
# Complementary supports of output derivatives

Output differentiation preserves the joint complementary symbol support in
`app:ch_regular:lem:finite-chain`. This is the support needed to apply the
buffered gaps, including when an output symbol vanishes only at a single base.
-/

@[expose] public noncomputable section
open Set
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
open LocalizedKernel
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every output jet retains the joint complementary output support. The
support is joint in base and frequency, as required for the buffered geometry
in `app:ch_regular:eq:chain-tail`. -/
theorem tsupport_outputDifferentiatedAmplitude_subset_outputComplement
    (upper : Bool) (ρ : ℝ) (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo : ℝ × E) (m : ℕ) (v : Fin m → ℝ × E) :
    tsupport (outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v) ⊆
      {x | (xo, ρ • x.2.2.1) ∈ tsupport
        (fun p : (ℝ × E) × (ℝ × E) => 1 - mo p.1 p.2)} := by
  apply closure_minimal ?_ ((isClosed_tsupport _).preimage (by fun_prop))
  intro x hx
  have hj : iteratedFDeriv ℝ m
      (fun y => normalizedIntegrand upper ρ α β mi mo r xi y x) xo ≠ 0 := by
    intro hz
    apply hx
    simp [outputDifferentiatedAmplitude, hz]
  have hs := support_iteratedFDeriv_subset (𝕜 := ℝ) m hj
  have he : (fun y => normalizedIntegrand upper ρ α β mi mo r xi y x) =
      (fun y => Localization.phaseOscillation (ρ • literalPhase upper xi y) x *
        outputIndependentAmplitude upper ρ α β mi r xi x) *
      (fun y => 1 - mo y (ρ • x.2.2.1)) := by
    funext y
    simp only [normalizedIntegrand, normalizedAmplitude_eq_outputIndependent_mul,
      Pi.mul_apply, mul_assoc]
  rw [he] at hs
  exact tsupport_comp_subset_preimage
    (f := fun y : ℝ × E => (y, ρ • x.2.2.1))
    (fun p : (ℝ × E) × (ℝ × E) => 1 - mo p.1 p.2)
    (by fun_prop) (tsupport_mul_subset_right hs)

/-- Output derivatives retain the input symbol's joint support, as needed by
the buffered gaps in `app:ch_regular:lem:finite-chain`. -/
theorem tsupport_outputDifferentiatedAmplitude_subset_inputSupport
    (upper : Bool) (ρ : ℝ) (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo : ℝ × E) (m : ℕ) (v : Fin m → ℝ × E) :
    tsupport (outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v) ⊆
      {x | (xi, ρ • x.2.2.2) ∈ tsupport (Function.uncurry mi)} := by
  apply closure_minimal ?_ ((isClosed_tsupport _).preimage (by fun_prop))
  intro x hx
  apply subset_tsupport
  intro hz
  have he : (fun y => normalizedIntegrand upper ρ α β mi mo r xi y x) = 0 := by
    funext y
    cases upper <;> simp [normalizedIntegrand, normalizedAmplitude, lowerAmplitude,
      upperAmplitude, Function.uncurry] at hz ⊢ <;> simp [hz]
  apply hx
  simp [outputDifferentiatedAmplitude, he]

/-- The common support for every output jet, including both symbol supports.
Its rectangular carrier provides uniform volume constants in
`app:ch_regular:eq:chain-tail`. -/
def outputDerivativeCarrier (ρ : ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (xi xo : ℝ × E) (C : Set (ℝ × TangentialVariables E)) :
    Set (ℝ × TangentialVariables E) :=
  (C ∩ {x | (xi, ρ • x.2.2.2) ∈ tsupport (Function.uncurry mi)}) ∩
    {x | (xo, ρ • x.2.2.1) ∈ tsupport
      (fun p : (ℝ × E) × (ℝ × E) => 1 - mo p.1 p.2)}

/-- Compactness of the common differentiated support
(`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_outputDerivativeCarrier (ρ : ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (xi xo : ℝ × E)
    {C : Set (ℝ × TangentialVariables E)} (hC : IsCompact C) :
    IsCompact (outputDerivativeCarrier ρ mi mo xi xo C) :=
  (hC.inter_right ((isClosed_tsupport _).preimage (by fun_prop))).inter_right
    ((isClosed_tsupport _).preimage (by fun_prop))

/-- The common complementary carrier contains every output jet, with no
additional support premise on differentiated amplitudes
(`app:ch_regular:eq:chain-tail`). -/
theorem tsupport_outputDifferentiatedAmplitude_subset_carrier
    (upper : Bool) (ρ : ℝ) (α β : ℝ × E → ℝ)
    (mi mo : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (xi xo : ℝ × E) (m : ℕ) (v : Fin m → ℝ × E)
    {Kα Kβ Ko Ki : Set (ℝ × E)}
    (hKα : IsCompact Kα) (hKβ : IsCompact Kβ) (hKo : IsCompact Ko) (hKi : IsCompact Ki)
    (hsα : tsupport α ⊆ Kα) (hsβ : tsupport β ⊆ Kβ)
    (hsr : tsupport (fun ξ => r (ρ • ξ)) ⊆ Ko)
    (hsi : tsupport (fun ξ => mi xi (ρ • ξ)) ⊆ Ki) :
    tsupport (outputDifferentiatedAmplitude upper ρ α β mi mo r xi xo m v) ⊆
      outputDerivativeCarrier ρ mi mo xi xo (amplitudeCarrier Kα Kβ Ko Ki) := by
  intro x hx
  exact ⟨⟨tsupport_outputDifferentiatedAmplitude_subset upper ρ α β mi mo r xi xo m v
    hKα hKβ hKo hKi hsα hsβ hsr hsi hx,
    tsupport_outputDifferentiatedAmplitude_subset_inputSupport upper ρ α β mi mo r xi xo m v hx⟩,
    tsupport_outputDifferentiatedAmplitude_subset_outputComplement upper ρ α β mi mo r xi xo m v hx⟩

/-- For physical masks, the differentiated carrier is exactly the
complementary fiber already used by buffered geometry. This bridge preserves
the identity term and requires no new gap hypothesis beyond that fiber
(`app:ch_regular:lem:finite-chain`). -/
theorem outputDerivativeCarrier_physicalMask_eq_complementaryJointSupport
    {ρ : ℝ} (hρ : 0 < ρ) (mi mo : CanonicalPhase E → ℝ) (xi xo : ℝ × E)
    (C : Set (ℝ × TangentialVariables E)) {B : Set ((ℝ × E) × (ℝ × E))}
    (hb : (xi, xo) ∈ B) :
    outputDerivativeCarrier ρ
      (fun y ξ => (physicalMask ρ mi (y, ξ) : ℂ))
      (fun y ξ => (physicalMask ρ mo (y, ξ) : ℂ)) xi xo C =
      {x | ((xi, xo), x) ∈ complementaryJointSupport B C mi mo} := by
  have hi : tsupport (Function.uncurry
      (fun y ξ => (physicalMask ρ mi (y, ξ) : ℂ))) =
      normalizeMaskCovector ρ ⁻¹' tsupport mi := by
    change tsupport (Complex.ofReal ∘ physicalMask ρ mi) = _
    rw [tsupport_comp_eq (by simp), tsupport_physicalMask mi hρ]
  have he : (fun p : (ℝ × E) × (ℝ × E) =>
      1 - (physicalMask ρ mo (p.1, p.2) : ℂ)) =
      Complex.ofReal ∘ physicalMask ρ (fun p => 1 - mo p) := by
    funext p
    simp [physicalMask]
  have ho : tsupport (fun p : (ℝ × E) × (ℝ × E) =>
      1 - (physicalMask ρ mo (p.1, p.2) : ℂ)) =
      normalizeMaskCovector ρ ⁻¹' tsupport (fun p => 1 - mo p) := by
    rw [he, tsupport_comp_eq (by simp), tsupport_physicalMask _ hρ]
  ext x
  simp [outputDerivativeCarrier, hi, ho, normalizeMaskCovector, hρ.ne',
    complementaryJointSupport, hb]

end JanetCartan.FiniteChain.Retarded.KernelDecay
