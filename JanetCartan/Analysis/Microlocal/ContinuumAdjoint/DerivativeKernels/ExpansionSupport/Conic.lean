module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.ExpansionSupport.Joint

/-!
# Common closed conic buffers for generated amplitudes

The support and qualitative fields needed by `exists_modifiedAdjoint_L2_bound`
are deduced from the original amplitude in `app:ch_background:prop:bg-adjoint`.
The mixed-jet field remains the separate quantitative interpolation obligation.
In particular a pointwise `BufferedSupport` for the original amplitude alone
is not silently treated as a buffer for its derivatives: the geometric input
below covers the closed primitive buffer.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint.DerivativeKernels
open ContinuumRow ModifiedNormalSymbol
variable {n : ℕ}

/-- Membership of every generated nonzero value in any original closed
joint buffer (`app:ch_background:prop:bg-adjoint`). -/
theorem adjointDerivativeExpansion_mem_closed (L V)
    (ds : List (InitialCarrierDerivative n)) (a : AdjointAmplitude n)
    {P : Set (AmplitudeVariables n)} (hP : IsClosed P)
    (ha : ∀ z x η, a z x η ≠ 0 → (z, x, η) ∈ P)
    (t : AdjointDerivativeTerm n) (ht : t ∈ adjointDerivativeExpansion L V ds a)
    (z x η) (hne : t.amplitude z x η ≠ 0) : (z, x, η) ∈ P := by
  apply closure_minimal (fun p hp ↦ ha p.1 p.2.1 p.2.2 hp) hP
  exact tsupport_adjointDerivativeExpansion_subset L V ds a t ht
    (subset_tsupport _ hne)

/-- Fixed carrier, measurement, angular and high-frequency buffer for
`app:ch_background:prop:bg-adjoint`. Frequency is unbounded above. -/
def adjointConicBuffer (X : Set (Euclidean n)) (Z : Set CarrierParameter)
    (Ω : Set (Euclidean (n - 1))) (ρ : ℝ) : Set (AmplitudeVariables n) :=
  Z ×ˢ (X ×ˢ {η | ‖η‖⁻¹ • η ∈ Ω ∧ ρ ≤ ‖η‖})

/-- A positive high-frequency threshold closes the primitive conic buffer
away from the singularity of angular normalization
(`app:ch_background:prop:bg-adjoint`). -/
theorem isClosed_adjointConicBuffer {X : Set (Euclidean n)} {Z : Set CarrierParameter}
    {Ω : Set (Euclidean (n - 1))} {ρ : ℝ}
    (hX : IsClosed X) (hZ : IsClosed Z) (hΩ : IsClosed Ω) (hρ : 0 < ρ) :
    IsClosed (adjointConicBuffer X Z Ω ρ) := by
  apply hZ.prod (hX.prod ?_)
  have hc : Continuous (fun η : Euclidean (n - 1) ↦ (max ρ ‖η‖)⁻¹ • η) :=
    ((continuous_const.max continuous_norm).inv₀
      (fun η ↦ ne_of_gt (hρ.trans_le (le_max_left _ _)))).smul continuous_id
  have he : {η : Euclidean (n - 1) | ‖η‖⁻¹ • η ∈ Ω ∧ ρ ≤ ‖η‖} =
      (fun η : Euclidean (n - 1) ↦ (max ρ ‖η‖)⁻¹ • η) ⁻¹' Ω ∩
        {η : Euclidean (n - 1) | ρ ≤ ‖η‖} := by
    ext η
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨by simpa [max_eq_right hb] using ha, hb⟩
  rw [he]
  exact (hΩ.preimage hc).inter (isClosed_le continuous_const continuous_norm)

/-- Carrier, angular and high-frequency support, and measurement support,
for each actual generated amplitude (`app:ch_background:prop:bg-adjoint`). -/
theorem adjointDerivativeExpansion_mem_conicBuffer (L V)
    (ds : List (InitialCarrierDerivative n)) (a : AdjointAmplitude n)
    {X : Set (Euclidean n)} {Z : Set CarrierParameter}
    {Ω : Set (Euclidean (n - 1))} {ρ : ℝ}
    (hX : IsClosed X) (hZ : IsClosed Z) (hΩ : IsClosed Ω) (hρ : 0 < ρ)
    (ha : ∀ z x η, a z x η ≠ 0 → z ∈ Z ∧ x ∈ X ∧ ‖η‖⁻¹ • η ∈ Ω ∧ ρ ≤ ‖η‖)
    (t : AdjointDerivativeTerm n) (ht : t ∈ adjointDerivativeExpansion L V ds a)
    (z x η) (hne : t.amplitude z x η ≠ 0) :
    z ∈ Z ∧ x ∈ X ∧ ‖η‖⁻¹ • η ∈ Ω ∧ ρ ≤ ‖η‖ :=
  adjointDerivativeExpansion_mem_closed L V ds a
    (isClosed_adjointConicBuffer hX hZ hΩ hρ) ha t ht z x η hne

/-- The compact measurement and spectator supports needed by the modified
normal transfer from the original amplitude (`app:ch_background:prop:bg-adjoint`). -/
theorem compactSupports_adjointDerivativeExpansion (L V)
    (ds : List (InitialCarrierDerivative n)) {a : AdjointAmplitude n}
    {X : Set (Euclidean n)} {K : Set (Euclidean 2)} (ha : CompactSupports a X K)
    (t : AdjointDerivativeTerm n) (ht : t ∈ adjointDerivativeExpansion L V ds a) :
    CompactSupports t.amplitude X K := by
  refine ⟨ha.measurement_compact, ha.spectator_compact, ?_⟩
  intro z x η hne
  exact adjointDerivativeExpansion_mem_closed L V ds a
    ((ha.measurement_compact.isClosed.preimage continuous_snd.fst).inter
      (ha.spectator_compact.isClosed.preimage continuous_fst.snd))
    ha.amplitude_support t ht z x η hne

/-- All amplitude-dependent qualitative obligations of the modified normal
are discharged for the generated term. The geometric fields are reused from
the original chart (`app:ch_background:prop:bg-adjoint`). -/
theorem primitiveRegularity_adjointDerivativeExpansion
    {g : Chart n} {a : AdjointAmplitude n} {m : CarrierVariable n → ℝ}
    (ha : PrimitiveRegularity g a m)
    {L : CarrierParameter → Euclidean n → Euclidean (n - 1) → Euclidean n}
    {V : CarrierParameter → Euclidean n → CarrierParameter → Euclidean n}
    (hL : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ L p.1 p.2 h))
    (hV : ∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ V p.1 p.2 h))
    (ds : List (InitialCarrierDerivative n)) (t : AdjointDerivativeTerm n)
    (ht : t ∈ adjointDerivativeExpansion L V ds a) :
    PrimitiveRegularity g t.amplitude m :=
  { ha with amplitude := contDiff_adjointDerivativeExpansion ha.amplitude hL hV ds t ht }

/-- A geometric buffer covering both copies of the closed primitive support
works for every generated amplitude. The parent supplies this geometric
inclusion from its fixed conic chart, once, not once per term
(`app:ch_background:prop:bg-adjoint`). -/
theorem bufferedSupport_adjointDerivativeExpansion (L V)
    (ds : List (InitialCarrierDerivative n)) (a : AdjointAmplitude n)
    {P : Set (AmplitudeVariables n)} (hP : IsClosed P)
    (ha : ∀ z x η, a z x η ≠ 0 → (z, x, η) ∈ P)
    (g : Chart n) (B : Set (JointVariables n))
    (hB : ∀ p ∈ g.inputDomain,
      ((g.carrier p).1, p.1.1, (g.carrier p).2) ∈ P →
      ((g.carrier p).1, p.1.2.1, (g.carrier p).2) ∈ P → p ∈ B)
    (hclosed : IsClosed (g.push '' B)) (himage : g.push '' B ⊆ g.outputDomain)
    (t : AdjointDerivativeTerm n) (ht : t ∈ adjointDerivativeExpansion L V ds a) :
    BufferedSupport g t.amplitude B := by
  refine ⟨?_, hclosed, himage⟩
  intro p hp hl hr
  exact hB p hp
    (adjointDerivativeExpansion_mem_closed L V ds a hP ha t ht _ _ _ hl)
    (adjointDerivativeExpansion_mem_closed L V ds a hP ha t ht _ _ _ hr)

/-- Instantiate all amplitude support fields of the low-bound reserve using
the explicit closed conic buffer. The spectator support is the projection of
the original compact carrier set. Only the primitive geometric buffer is an
input; no support property of a generated amplitude is assumed
(`app:ch_background:prop:bg-adjoint`). -/
theorem adjointDerivativeExpansion_conic_properties (L V)
    (ds : List (InitialCarrierDerivative n)) (a : AdjointAmplitude n)
    {X : Set (Euclidean n)} {Z : Set CarrierParameter}
    {Ω : Set (Euclidean (n - 1))} {ρ : ℝ}
    (hX : IsCompact X) (hZ : IsCompact Z) (hΩ : IsCompact Ω) (hρ : 0 < ρ)
    (ha : ∀ z x η, a z x η ≠ 0 → z ∈ Z ∧ x ∈ X ∧ ‖η‖⁻¹ • η ∈ Ω ∧ ρ ≤ ‖η‖)
    (g : Chart n) (B : Set (JointVariables n))
    (hB : ∀ p ∈ g.inputDomain,
      ((g.carrier p).1, p.1.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω ρ →
      ((g.carrier p).1, p.1.2.1, (g.carrier p).2) ∈ adjointConicBuffer X Z Ω ρ → p ∈ B)
    (hclosed : IsClosed (g.push '' B)) (himage : g.push '' B ⊆ g.outputDomain)
    (t : AdjointDerivativeTerm n) (ht : t ∈ adjointDerivativeExpansion L V ds a) :
    CompactSupports t.amplitude X (Prod.snd '' Z) ∧
      (∀ z x η, t.amplitude z x η ≠ 0 → z ∈ Z ∧ ‖η‖⁻¹ • η ∈ Ω ∧ ρ ≤ ‖η‖) ∧
      BufferedSupport g t.amplitude B := by
  have hs := adjointDerivativeExpansion_mem_conicBuffer L V ds a
    hX.isClosed hZ.isClosed hΩ.isClosed hρ ha t ht
  refine ⟨⟨hX, hZ.image continuous_snd, ?_⟩, ?_, ?_⟩
  · intro z x η hne
    exact ⟨(hs z x η hne).2.1, z, (hs z x η hne).1, rfl⟩
  · intro z x η hne
    exact ⟨(hs z x η hne).1, (hs z x η hne).2.2⟩
  · exact bufferedSupport_adjointDerivativeExpansion L V ds a
      (isClosed_adjointConicBuffer hX.isClosed hZ.isClosed hΩ.isClosed hρ)
      ha g B hB hclosed himage t ht

end JanetCartan.ContinuumAdjoint.DerivativeKernels
