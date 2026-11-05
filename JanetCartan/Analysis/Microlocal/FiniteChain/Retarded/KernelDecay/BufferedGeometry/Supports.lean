module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.Basic
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Localizers.Grades

/-!
# Actual compact complementary supports

The support carrier for `exists_buffered_lower_geometry` and
`exists_buffered_upper_geometry` in `app:ch_regular:lem:finite-chain`.
Only the intersection with the input and complementary output mask supports
carries a gap. The rectangular carrier itself is used for volume bounds.
-/

@[expose] public noncomputable section
open Set
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
open LocalizedKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The compact joint support with both external bases included
(`app:ch_regular:lem:finite-chain`). The identity part of the complementary
output symbol remains present. -/
def complementaryJointSupport (B : Set ((ℝ × E) × (ℝ × E)))
    (C : Set (ℝ × TangentialVariables E)) (mi mo : CanonicalPhase E → ℝ) :
    Set (((ℝ × E) × (ℝ × E)) × (ℝ × TangentialVariables E)) :=
  (B ×ˢ C) ∩ {p | (p.1.1, p.2.2.2.2) ∈ tsupport mi} ∩
    {p | (p.1.2, p.2.2.2.1) ∈ tsupport (fun q => 1 - mo q)}

omit [InnerProductSpace ℝ E] in
/-- Compactness uses compact base/frequency carriers and closed mask supports;
it does not require compact support of `1 - mo`
(`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_complementaryJointSupport
    {B : Set ((ℝ × E) × (ℝ × E))} {C : Set (ℝ × TangentialVariables E)}
    (hB : IsCompact B) (hC : IsCompact C) (mi mo : CanonicalPhase E → ℝ) :
    IsCompact (complementaryJointSupport B C mi mo) :=
  ((hB.prod hC).inter_right ((isClosed_tsupport mi).preimage (by fun_prop))).inter_right
    ((isClosed_tsupport (fun q => 1 - mo q)).preimage (by fun_prop))

omit [InnerProductSpace ℝ E] in
/-- Each parameter-dependent complementary fiber is compact and lies in the
common volume carrier (`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_complementaryJointSupport_fiber
    {B : Set ((ℝ × E) × (ℝ × E))} {C : Set (ℝ × TangentialVariables E)}
    (hB : IsCompact B) (hC : IsCompact C) (mi mo : CanonicalPhase E → ℝ)
    (b : (ℝ × E) × (ℝ × E)) :
    IsCompact {x | (b, x) ∈ complementaryJointSupport B C mi mo} ∧
      {x | (b, x) ∈ complementaryJointSupport B C mi mo} ⊆ C := by
  have hs : {x | (b, x) ∈ complementaryJointSupport B C mi mo} ⊆ C :=
    fun _ hx => hx.1.1.2
  exact ⟨hC.of_isClosed_subset
    ((isCompact_complementaryJointSupport hB hC mi mo).isClosed.preimage
      (continuous_const.prodMk continuous_id)) hs, hs⟩

/-- The actual normalized lower and literal upper amplitudes lie in the
complementary fiber for the physical rescalings of canonical masks
(`app:ch_regular:lem:finite-chain`). The two literal weight positions and the
upper input mask are retained. This statement concerns the half-space amplitude;
it makes no claim about removal of an endpoint term without its input buffer. -/
theorem tsupport_normalizedAmplitude_subset_complementaryJointSupport
    (upper : Bool) {ρ : ℝ} (hρ : ρ ≠ 0) (α β : ℝ × E → ℝ)
    (mi mo : CanonicalPhase E → ℝ) (r : ℝ × E → ℂ) (xi xo : ℝ × E)
    {B : Set ((ℝ × E) × (ℝ × E))} {C : Set (ℝ × TangentialVariables E)}
    (hb : (xi, xo) ∈ B)
    (hcarrier : tsupport (normalizedAmplitude upper ρ α β
      (fun b ξ => (physicalMask ρ mi (b, ξ) : ℂ))
      (fun b ξ => (physicalMask ρ mo (b, ξ) : ℂ)) r xi xo) ⊆ C) :
    tsupport (normalizedAmplitude upper ρ α β
      (fun b ξ => (physicalMask ρ mi (b, ξ) : ℂ))
      (fun b ξ => (physicalMask ρ mo (b, ξ) : ℂ)) r xi xo) ⊆
        {x | ((xi, xo), x) ∈ complementaryJointSupport B C mi mo} := by
  have hmask : tsupport (normalizedAmplitude upper ρ α β
      (fun b ξ => (physicalMask ρ mi (b, ξ) : ℂ))
      (fun b ξ => (physicalMask ρ mo (b, ξ) : ℂ)) r xi xo) ⊆
      {x | (xi, x.2.2.2) ∈ tsupport mi} ∩
        {x | (xo, x.2.2.1) ∈ tsupport (fun q => 1 - mo q)} := by
    apply closure_minimal ?_
      (((isClosed_tsupport mi).preimage (by fun_prop)).inter
        ((isClosed_tsupport (fun q => 1 - mo q)).preimage (by fun_prop)))
    intro x hx
    have hi : mi (xi, x.2.2.2) ≠ 0 := by
      intro he
      apply hx
      cases upper <;> simp [normalizedAmplitude, lowerAmplitude, upperAmplitude,
        physicalMask, normalizeMaskCovector, smul_smul, hρ, he]
    have ho : 1 - mo (xo, x.2.2.1) ≠ 0 := by
      intro he
      have he' : mo (xo, x.2.2.1) = 1 := (sub_eq_zero.mp he).symm
      apply hx
      cases upper <;> simp [normalizedAmplitude, lowerAmplitude, upperAmplitude,
        physicalMask, normalizeMaskCovector, smul_smul, hρ, he']
    exact ⟨subset_tsupport mi hi, subset_tsupport (fun q => 1 - mo q) ho⟩
  intro x hx
  exact ⟨⟨⟨hb, hcarrier hx⟩, (hmask hx).1⟩, (hmask hx).2⟩

end JanetCartan.FiniteChain.Retarded.KernelDecay
