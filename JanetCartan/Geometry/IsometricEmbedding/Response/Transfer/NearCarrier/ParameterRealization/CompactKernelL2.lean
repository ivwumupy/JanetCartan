module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.CompactKernelL2.Operator
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Operator-norm differentiation of compact kernel realizations

For `app:ch_response:eq:direct-envelope-profile`, a jointly smooth scalar kernel
with common compact physical support gives a differentiable family of bounded
operators on actual Lebesgue L². Only its identification on Schwartz tests is
required of the supplied realization. The derivative is constructed from the
literal pointwise parameter differential and is identified on arbitrary L² data.
The last results include the independent derivative of a varying datum.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan.ResponseTransfer.NearCarrierParameter.CompactKernelL2
open JanetCartan.ResponseTransfer.ParameterRealization.L2Family

variable {d p : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin p)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

variable {U : Set (EuclideanSpace ℝ (Fin p))}
  {Kx Ky : Set (EuclideanSpace ℝ (Fin d))}
  {k : EuclideanSpace ℝ (Fin p) →
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℂ}

private lemma differential_zero_off_support (hU : IsOpen U)
    (hs : ∀ a ∈ U, tsupport (k a) ⊆ Kx ×ˢ Ky) {c : P} (hc : c ∈ U)
    {z : E × E} (hz : z ∉ Kx ×ˢ Ky) (v : P) :
    fderiv ℝ (fun a ↦ k a z) c v = 0 := by
  have he : (fun a ↦ k a z) =ᶠ[𝓝 c] (fun _ ↦ (0 : ℂ)) := by
    filter_upwards [hU.mem_nhds hc] with a ha
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hs a ha h))
  rw [he.fderiv_eq]
  simp

/-- Joint classical smoothness and common compact support construct the actual
operator-norm derivative, with its literal integral on every L² datum.
This is the parameter differentiation step in
`app:ch_response:eq:direct-envelope-profile`; no continuity or differentiability
of the supplied operator family is assumed. -/
theorem exists_hasFDerivAt_realization (hU : IsOpen U)
    (hKx : IsCompact Kx) (hKy : IsCompact Ky)
    (hk : ContDiffOn ℝ ∞ (Function.uncurry k) (U ×ˢ univ))
    (hs : ∀ a ∈ U, tsupport (k a) ⊆ Kx ×ˢ Ky)
    (T : P → L² →L[ℂ] L²)
    (hT : ∀ a ∈ U, ∀ f : SchwartzMap E ℂ,
      T a (f.toLp 2 volume) =ᵐ[volume] fun x ↦ ∫ y, k a (x, y) * f y)
    {c : P} (hc : c ∈ U) :
    ∃ D : P →L[ℝ] (L² →L[ℂ] L²), HasFDerivAt T D c ∧
      ∀ v f, D v f =ᵐ[volume]
        fun x ↦ ∫ y, fderiv ℝ (fun a ↦ k a (x, y)) c v * f y := by
  let : CompactSpace Kx := isCompact_iff_compactSpace.mp hKx
  let : CompactSpace Ky := isCompact_iff_compactSpace.mp hKy
  let : CompactSpace (Kx ×ˢ Ky) := isCompact_iff_compactSpace.mp (hKx.prod hKy)
  let B := (kernelOperator hKx hKy).restrictScalars ℝ
  let dk := compactFamily (K := Kx ×ˢ Ky) (fun a z ↦ fderiv ℝ (fun b ↦ k b z) a) c
  let D : P →L[ℝ] (L² →L[ℂ] L²) := B.comp (compactLinearFlip dk)
  refine ⟨D, ?_, ?_⟩
  · have hd := B.hasFDerivAt.comp c (compactFamily_hasFDerivAt (K := Kx ×ˢ Ky) hU hk hc)
    apply hd.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hc] with a ha
    exact eq_kernelOperator_of_schwartz hKx hKy (compactFamily k a) (k a)
      (compactFamily_apply hk ha)
      (fun z hz ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hs a ha h))) (T a) (hT a ha)
  · intro v f
    change kernelOperator hKx hKy (compactLinearFlip dk v) f =ᵐ[volume] _
    apply kernelOperator_ae hKx hKy _ (fun z ↦ fderiv ℝ (fun a ↦ k a z) c v)
    · intro z
      change dk z v = _
      rw [show dk z = fderiv ℝ (fun a ↦ k a z) c from
        compactFamily_apply
          (JanetCartan.ResponseTransfer.ParameterRealization.L2Family.contDiffOn_parameterFDeriv
            hU hk) hc z]
    · intro z hz
      exact differential_zero_off_support hU hs hc hz v

/-- The supplied realization is differentiable in operator norm at each point
of the open parameter domain (`app:ch_response:eq:direct-envelope-profile`). -/
theorem differentiableAt_realization (hU : IsOpen U)
    (hKx : IsCompact Kx) (hKy : IsCompact Ky)
    (hk : ContDiffOn ℝ ∞ (Function.uncurry k) (U ×ˢ univ))
    (hs : ∀ a ∈ U, tsupport (k a) ⊆ Kx ×ˢ Ky)
    (T : P → L² →L[ℂ] L²)
    (hT : ∀ a ∈ U, ∀ f : SchwartzMap E ℂ,
      T a (f.toLp 2 volume) =ᵐ[volume] fun x ↦ ∫ y, k a (x, y) * f y)
    {c : P} (hc : c ∈ U) : DifferentiableAt ℝ T c := by
  obtain ⟨D, hd, _⟩ := exists_hasFDerivAt_realization hU hKx hKy hk hs T hT hc
  exact hd.differentiableAt

/-- Every directional operator derivative acts by the literal differentiated
kernel on arbitrary L² data, as required by the parameter amplitude transfer in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem fderiv_realization_ae (hU : IsOpen U)
    (hKx : IsCompact Kx) (hKy : IsCompact Ky)
    (hk : ContDiffOn ℝ ∞ (Function.uncurry k) (U ×ˢ univ))
    (hs : ∀ a ∈ U, tsupport (k a) ⊆ Kx ×ˢ Ky)
    (T : P → L² →L[ℂ] L²)
    (hT : ∀ a ∈ U, ∀ f : SchwartzMap E ℂ,
      T a (f.toLp 2 volume) =ᵐ[volume] fun x ↦ ∫ y, k a (x, y) * f y)
    {c : P} (hc : c ∈ U) (v : P) (f : L²) :
    fderiv ℝ T c v f =ᵐ[volume]
      fun x ↦ ∫ y, fderiv ℝ (fun a ↦ k a (x, y)) c v * f y := by
  obtain ⟨D, hd, he⟩ := exists_hasFDerivAt_realization hU hKx hKy hk hs T hT hc
  rw [hd.fderiv]
  exact he v f

/-- The actual product rule for a varying L² datum. Only a line derivative of
the datum is needed; the operator-norm derivative is derived from the primitive
kernel hypotheses. The independent `T c pf` term is retained, as required in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem hasLineDerivAt_realization_apply (hU : IsOpen U)
    (hKx : IsCompact Kx) (hKy : IsCompact Ky)
    (hk : ContDiffOn ℝ ∞ (Function.uncurry k) (U ×ˢ univ))
    (hs : ∀ a ∈ U, tsupport (k a) ⊆ Kx ×ˢ Ky)
    (T : P → L² →L[ℂ] L²)
    (hT : ∀ a ∈ U, ∀ f : SchwartzMap E ℂ,
      T a (f.toLp 2 volume) =ᵐ[volume] fun x ↦ ∫ y, k a (x, y) * f y)
    {c : P} (hc : c ∈ U) (v : P) {f : P → L²} {pf : L²}
    (hf : HasLineDerivAt ℝ f pf c v) :
    HasLineDerivAt ℝ (fun a ↦ T a (f a))
      (fderiv ℝ T c v (f c) + T c pf) c v := by
  have hd := (differentiableAt_realization hU hKx hKy hk hs T hT hc).hasFDerivAt
  have hr := (ContinuousLinearMap.restrictScalarsL ℂ L² L² ℝ ℝ).hasFDerivAt.comp c hd
  have hh := (hr.hasLineDerivAt v).clm_apply hf
  simpa only [HasLineDerivAt, Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrict_scalarsL', ContinuousLinearMap.coe_restrictScalars',
    zero_smul, add_zero] using hh

/-- The varying-datum rule together with the literal representative of its
kernel contribution. This form is ready for the source-integration identities
in `app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_hasLineDerivAt_realization_apply (hU : IsOpen U)
    (hKx : IsCompact Kx) (hKy : IsCompact Ky)
    (hk : ContDiffOn ℝ ∞ (Function.uncurry k) (U ×ˢ univ))
    (hs : ∀ a ∈ U, tsupport (k a) ⊆ Kx ×ˢ Ky)
    (T : P → L² →L[ℂ] L²)
    (hT : ∀ a ∈ U, ∀ g : SchwartzMap E ℂ,
      T a (g.toLp 2 volume) =ᵐ[volume] fun x ↦ ∫ y, k a (x, y) * g y)
    {c : P} (hc : c ∈ U) (v : P) {f : P → L²} {pf : L²}
    (hf : HasLineDerivAt ℝ f pf c v) :
    ∃ df : L², HasLineDerivAt ℝ (fun a ↦ T a (f a)) (df + T c pf) c v ∧
      df =ᵐ[volume] fun x ↦ ∫ y, fderiv ℝ (fun a ↦ k a (x, y)) c v * f c y :=
  ⟨fderiv ℝ T c v (f c), hasLineDerivAt_realization_apply hU hKx hKy hk hs T hT hc v hf,
    fderiv_realization_ae hU hKx hKy hk hs T hT hc v (f c)⟩

end JanetCartan.ResponseTransfer.NearCarrierParameter.CompactKernelL2
