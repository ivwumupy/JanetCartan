module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.NegativeBounds
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.SourceCut
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.Cutoffs

/-!
# Actual physical support of the signed retarded operator

The test action supplied by `exists_retardedOperator_signed_integer_bounds_of_primitive_data`
retains both physical masks. It therefore fixes a smooth outer plateau on all
L² inputs; its literal adjoint fixes the source plateau. These statements
close the support input for the local negative pairing, independently of the
primitive symbol estimates. No support of an unknown output is assumed.
Source: `app:ch_regular_base:eq:fixed-time-representation` and
`app:ch_regular_base:eq:negative-duality`.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.RetardedLocalization
open FourierIntegral LowBounds EvolutionIntegral EvolutionIntegral.KernelIdentification
open EvolutionIntegral.UncutTestAction
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q

/-- A finite family of original masks admits two common smooth plateaux
strictly inside the original source and measurement domains. All choices
precede the varying phase, amplitudes and operators. These are the masks used
in `zeroExtend_localRetardedOperator`, including its adjoint direction
(`app:ch_regular_base:eq:negative-duality`). -/
theorem exists_finite_retarded_domain_masks {ι : Type*} [Finite ι]
    (χout χsource : ι → E → ℂ) {U W : Set E} (hU : IsOpen U) (hW : IsOpen W)
    (hoc : ∀ i, HasCompactSupport (χout i))
    (hsc : ∀ i, HasCompactSupport (χsource i))
    (hos : ∀ i, tsupport (χout i) ⊆ W) (hss : ∀ i, tsupport (χsource i) ⊆ U) :
    ∃ ψout ψsource : E → ℝ,
      ContDiff ℝ ∞ ψout ∧ ContDiff ℝ ∞ ψsource ∧
      HasCompactSupport ψout ∧ HasCompactSupport ψsource ∧
      (∀ x, ‖ψout x‖ ≤ 1) ∧ (∀ x, ‖ψsource x‖ ≤ 1) ∧
      tsupport ψout ⊆ W ∧ tsupport ψsource ⊆ U ∧
      (∀ i, tsupport (χout i) ⊆ interior {x | ψout x = 1}) ∧
      (∀ i, tsupport (χsource i) ⊆ interior {x | ψsource x = 1}) := by
  obtain ⟨ψout, ho, hor, hoc', hos', hop⟩ :=
    CompatibleResponse.exists_compact_family_cutoff (isCompact_iUnion hoc) hW
      (iUnion_subset hos)
  obtain ⟨ψsource, hs, hsr, hsc', hss', hsp⟩ :=
    CompatibleResponse.exists_compact_family_cutoff (isCompact_iUnion hsc) hU
      (iUnion_subset hss)
  refine ⟨ψout, ψsource, ho, hs, hoc', hsc', ?_, ?_, hos', hss', ?_, ?_⟩
  · intro x
    simpa only [Real.norm_of_nonneg (hor x).1] using (hor x).2
  · intro x
    simpa only [Real.norm_of_nonneg (hsr x).1] using (hsr x).2
  · exact fun i x hx ↦ hop (mem_iUnion.mpr ⟨i, hx⟩)
  · exact fun i x hx ↦ hsp (mem_iUnion.mpr ⟨i, hx⟩)

/-- The physical test formula is unchanged by a source plateau. The source
mask stays before the Fourier multiplier; no commutation through that
multiplier is used (`fixed-time-representation`). -/
theorem retardedPhysicalIntegral_source_plateau
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource) (a : ℝ)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hp : ∀ x ∈ tsupport χsource, ψ x = 1)
    (u : graphTestSpace (d + 1) q) :
    retardedPhysicalIntegral Ψ b χout χsource β hs a (sourceCutTest ψ hψ u) =
      retardedPhysicalIntegral Ψ b χout χsource β hs a u := by
  have he : complexSourceMaskTest χsource hs (sourceCutTest ψ hψ u) =
      complexSourceMaskTest χsource hs u := by
    apply Subtype.ext
    funext x
    change χsource x • ((ψ x : ℂ) • u.val x) = χsource x • u.val x
    by_cases hx : χsource x = 0
    · simp only [hx, zero_smul]
    · simp only [hp x (subset_tsupport χsource hx), Complex.ofReal_one, one_smul]
  funext x
  unfold retardedPhysicalIntegral
  rw [he]

/-- The original output mask and the exchanged source mask fix the SAME
bounded retarded operator and its literal adjoint. The only operator input
is the actual test action proved by the primitive signed constructor.
Source: `app:ch_regular_base:eq:adjoint-integrated-term`. -/
theorem retarded_mask_identities
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource) (a : ℝ)
    (Q : H →L[ℂ] H)
    (hQ : ∀ u : graphTestSpace (d + 1) q, Q (graphTestToLp u) =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (retardedPhysicalIntegral Ψ b χout χsource β hs a u x))
    (ψout ψsource : E → ℝ) (ho : Continuous ψout) (hs' : ContDiff ℝ ∞ ψsource)
    (hob : ∀ x, ‖ψout x‖ ≤ 1) (hsb : ∀ x, ‖ψsource x‖ ≤ 1)
    (hop : ∀ x ∈ tsupport χout, ψout x = 1)
    (hsp : ∀ x ∈ tsupport χsource, ψsource x = 1) :
    (sourceCutMultiplier ψout ho hob).comp Q = Q ∧
      (sourceCutMultiplier ψsource hs'.continuous hsb).comp Q.adjoint = Q.adjoint := by
  constructor
  · apply DFunLike.coe_injective
    apply denseRange_graphTestToLp.equalizer
      ((sourceCutMultiplier ψout ho hob).comp Q).continuous Q.continuous
    funext u
    apply Lp.ext
    filter_upwards [sourceCutMultiplier_coeFn ψout ho hob (Q (graphTestToLp u)), hQ u]
      with x hx hy
    change sourceCutMultiplier ψout ho hob (Q (graphTestToLp u)) x = Q (graphTestToLp u) x
    rw [hx, hy]
    by_cases hm : χout x = 0
    · simp [retardedPhysicalIntegral, hm]
    · simp only [hop x (subset_tsupport χout hm), Complex.ofReal_one, one_smul]
  · have he : Q.comp (sourceCutMultiplier ψsource hs'.continuous hsb) = Q := by
      apply DFunLike.coe_injective
      apply denseRange_graphTestToLp.equalizer
        (Q.comp (sourceCutMultiplier ψsource hs'.continuous hsb)).continuous Q.continuous
      funext u
      change Q (sourceCutMultiplier ψsource hs'.continuous hsb (graphTestToLp u)) = _
      rw [sourceCutMultiplier_graphTestToLp]
      apply Lp.ext
      have hu := hQ (sourceCutTest ψsource hs' u)
      rw [retardedPhysicalIntegral_source_plateau Ψ b χout χsource β hs a
        ψsource hs' hsp u] at hu
      exact hu.trans (hQ u).symm
    have he' := congrArg ContinuousLinearMap.adjoint he
    simpa only [ContinuousLinearMap.adjoint_comp, sourceCutMultiplier_adjoint] using he'

end JanetCartan.RegularSector.Characteristic.RetardedLocalization
