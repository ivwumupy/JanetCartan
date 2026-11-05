module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.Transfer
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Compact frequency integration for parameter transfer

The frequency selection in `app:ch_response:eq:direct-envelope-profile`
allows differentiation before the frequency integral. All domination and
integrability conditions follow from smoothness and compactness. The source
identity is first proved at each frequency; this module passes it to the
physical kernel used by the L² realization theorem.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan.ResponseTransfer.NearCarrierParameter

variable {d p : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin p)

/-- The literal compact frequency integral of the full scalar kernel, with
both physical positions retained (`app:ch_response:eq:direct-envelope-profile`).
Any fixed Fourier normalization can be included in the integrand. -/
def frequencyKernel (F : Set E) (k : E × E → E → ℂ) (z : E × E) : ℂ :=
  ∫ δ in F, k z δ

/-- Smoothness and compactness justify a directional derivative through the
frequency integral, without an assumed domination estimate.
Consumer: `frequencyKernel_source_identity` for
`app:ch_response:eq:direct-envelope-profile`. -/
theorem compactFrequency_fderiv
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    {V : Set Q} (hV : IsOpen V) {F : Set E} (hF : IsCompact F)
    {k : Q × E → ℂ} (hk : ContDiffOn ℝ ∞ k (V ×ˢ univ))
    {q : Q} (hq : q ∈ V) (v : Q) :
    fderiv ℝ (fun a ↦ ∫ δ in F, k (a, δ)) q v =
      ∫ δ in F, fderiv ℝ (fun a ↦ k (a, δ)) q v := by
  let : IsFiniteMeasure ((volume : Measure E).restrict F) :=
    isFiniteMeasure_restrict.mpr hF.measure_lt_top.ne
  rw [(hasFDerivAt_compactParameterIntegral hV isOpen_univ hF (subset_univ _) hk hq).fderiv]
  exact ContinuousLinearMap.integral_apply
    (integrableOn_parameterFDeriv hV isOpen_univ hF (subset_univ _) hk hq) v

/-- Compact frequency integration preserves joint local smoothness in the
carrier parameter and both physical positions. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiffOn_frequencyKernel
    {U : Set P} (hU : IsOpen U) {F : Set E} (hF : IsCompact F)
    {k : P → E × E → E → ℂ}
    (hk : ContDiffOn ℝ ∞ (fun q : (P × (E × E)) × E ↦ k q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun q : P × (E × E) ↦ frequencyKernel F (k q.1) q.2)
      (U ×ˢ univ) := by
  let : IsFiniteMeasure ((volume : Measure E).restrict F) :=
    isFiniteMeasure_restrict.mpr hF.measure_lt_top.ne
  exact contDiffOn_compactParameterIntegral (hU.prod isOpen_univ) isOpen_univ hF
    (subset_univ _) hk

/-- The integrated kernel retains the original physical support. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem tsupport_frequencyKernel
    {X Y F : Set E} (hX : IsClosed X) (hY : IsClosed Y)
    {k : E × E → E → ℂ}
    (hs : ∀ δ ∈ F, tsupport (fun z ↦ k z δ) ⊆ X ×ˢ Y) :
    tsupport (frequencyKernel F k) ⊆ X ×ˢ Y := by
  apply closure_minimal _ (hX.prod hY)
  intro z hz
  by_contra hn
  apply hz
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro δ hδ
  exact image_eq_zero_of_notMem_tsupport (f := fun z ↦ k z δ) (fun h ↦ hn (hs δ hδ h))

/-- Frequency integration preserves the exact signed parameter/source kernel
identity. The pointwise identity is produced by the forward or reverse phase
calculation, and its integral is consumed by
`hasLineDerivAt_compact_kernel_transfer` in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem frequencyKernel_source_identity
    {U : Set P} (hU : IsOpen U) {F : Set E} (hF : IsCompact F)
    {k : P → E × E → E → ℂ}
    (hk : ContDiffOn ℝ ∞ (fun q : (P × (E × E)) × E ↦ k q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ univ))
    {c : P} (hc : c ∈ U) (v : P)
    (r : E × E → E → ℂ) (b : Fin d → E × E → E → ℂ)
    (hr : ContDiff ℝ ∞ (Function.uncurry r))
    (hb : ∀ j, ContDiff ℝ ∞ (Function.uncurry (b j)))
    (hid : ∀ x y δ, δ ∈ F → fderiv ℝ (fun a ↦ k a (x, y) δ) c v =
      r (x, y) δ -
        ∑ j, fderiv ℝ (fun z ↦ b j (x, z) δ) y (EuclideanSpace.single j 1))
    (x y : E) :
    fderiv ℝ (fun a ↦ frequencyKernel F (k a) (x, y)) c v =
      frequencyKernel F r (x, y) -
        ∑ j, fderiv ℝ (fun z ↦ frequencyKernel F (b j) (x, z)) y
          (EuclideanSpace.single j 1) := by
  let : IsFiniteMeasure ((volume : Measure E).restrict F) :=
    isFiniteMeasure_restrict.mpr hF.measure_lt_top.ne
  have hk' : ContDiffOn ℝ ∞ (fun q : P × E ↦ k q.1 (x, y) q.2) (U ×ˢ univ) :=
    hk.comp ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd).contDiffOn
      (fun q hq ↦ ⟨⟨hq.1, mem_univ _⟩, mem_univ _⟩)
  have hb' (j : Fin d) : ContDiff ℝ ∞ (fun q : E × E ↦ b j (x, q.1) q.2) :=
    (hb j).comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
  have hi : IntegrableOn (fun δ ↦ r (x, y) δ) F :=
    integrableOn_compactParameter (U := (univ : Set (E × E))) hF (subset_univ _)
      hr.continuous.continuousOn (mem_univ _)
  have hdi (j : Fin d) : IntegrableOn
      (fun δ ↦ fderiv ℝ (fun z ↦ b j (x, z) δ) y (EuclideanSpace.single j 1)) F :=
    (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single j 1 : E)).integrable_comp
      (integrableOn_parameterFDeriv isOpen_univ isOpen_univ hF (subset_univ _)
        (hb' j).contDiffOn (mem_univ y))
  rw [show fderiv ℝ (fun a ↦ frequencyKernel F (k a) (x, y)) c v =
      ∫ δ in F, fderiv ℝ (fun a ↦ k a (x, y) δ) c v from
    compactFrequency_fderiv hU hF hk' hc v]
  calc
    _ = ∫ δ in F, r (x, y) δ -
        ∑ j, fderiv ℝ (fun z ↦ b j (x, z) δ) y (EuclideanSpace.single j 1) := by
      apply setIntegral_congr_fun hF.measurableSet
      exact fun δ hδ ↦ hid x y δ hδ
    _ = (∫ δ in F, r (x, y) δ) -
        ∑ j, ∫ δ in F, fderiv ℝ (fun z ↦ b j (x, z) δ) y
          (EuclideanSpace.single j 1) := by
      rw [integral_sub hi (integrable_finsetSum _ (fun j _ ↦ hdi j)),
        integral_finsetSum _ (fun j _ ↦ hdi j)]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact (compactFrequency_fderiv isOpen_univ hF (hb' j).contDiffOn
        (mem_univ y) (EuclideanSpace.single j 1)).symm

/-- The frozen compact frequency kernel is smooth in both physical positions.
Consumer: the L² source transfer in `app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiff_frequencyKernel {F : Set E} (hF : IsCompact F)
    {k : E × E → E → ℂ} (hk : ContDiff ℝ ∞ (Function.uncurry k)) :
    ContDiff ℝ ∞ (frequencyKernel F k) := by
  let : IsFiniteMeasure ((volume : Measure E).restrict F) :=
    isFiniteMeasure_restrict.mpr hF.measure_lt_top.ne
  exact contDiffOn_univ.mp (contDiffOn_compactParameterIntegral
    isOpen_univ isOpen_univ hF (subset_univ _) hk.contDiffOn)

/-- The actual L² derivative after compact frequency integration. Its only
identity input concerns the pointwise integrand, before frequency or source
integration and before choosing a datum. The selected forward/reverse kernel
calculations produce that input. All analytic interchanges and the weak source
step are proved here for `app:ch_response:eq:direct-envelope-profile`. -/
theorem hasLineDerivAt_frequency_kernel_transfer
    {U : Set P} (hU : IsOpen U) {X Y F : Set E}
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {k : P → E × E → E → ℂ}
    (hk : ContDiffOn ℝ ∞ (fun q : (P × (E × E)) × E ↦ k q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ univ))
    (hs : ∀ a ∈ U, ∀ δ ∈ F, tsupport (fun z ↦ k a z δ) ⊆ X ×ˢ Y)
    (T : P → Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (hT : ∀ a ∈ U, ∀ g : SchwartzMap E ℂ,
      T a (g.toLp 2 volume) =ᵐ[volume]
        fun x ↦ ∫ y, frequencyKernel F (k a) (x, y) * g y)
    {c : P} (hc : c ∈ U) (v : P)
    (r : E × E → E → ℂ) (b : Fin d → E × E → E → ℂ)
    (hr : ContDiff ℝ ∞ (Function.uncurry r))
    (hrs : ∀ δ ∈ F, tsupport (fun z ↦ r z δ) ⊆ X ×ˢ Y)
    (hb : ∀ j, ContDiff ℝ ∞ (Function.uncurry (b j)))
    (hbs : ∀ j δ, δ ∈ F → tsupport (fun z ↦ b j z δ) ⊆ X ×ˢ Y)
    (R : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (B : Fin d → Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (hR : ∀ g : SchwartzMap E ℂ, R (g.toLp 2 volume) =ᵐ[volume]
      fun x ↦ ∫ y, frequencyKernel F r (x, y) * g y)
    (hB : ∀ j, ∀ g : SchwartzMap E ℂ, B j (g.toLp 2 volume) =ᵐ[volume]
      fun x ↦ ∫ y, frequencyKernel F (b j) (x, y) * g y)
    (hid : ∀ x y δ, δ ∈ F → fderiv ℝ (fun a ↦ k a (x, y) δ) c v =
      r (x, y) δ -
        ∑ j, fderiv ℝ (fun z ↦ b j (x, z) δ) y (EuclideanSpace.single j 1))
    {f : P → Lp ℂ 2 (volume : Measure E)}
    {df : Fin d → Lp ℂ 2 (volume : Measure E)} {pf : Lp ℂ 2 (volume : Measure E)}
    (hdf : ∀ j, Pseudodifferential.HasEuclideanL2CoordinateDerivative j (f c) (df j))
    (hpf : HasLineDerivAt ℝ f pf c v) :
    HasLineDerivAt ℝ (fun a ↦ T a (f a))
      (R (f c) + ∑ j, B j (df j) + T c pf) c v := by
  exact hasLineDerivAt_compact_kernel_transfer (k := fun a ↦ frequencyKernel F (k a)) hU hX hY
    (contDiffOn_frequencyKernel hU hF hk)
    (fun a ha ↦ tsupport_frequencyKernel hX.isClosed hY.isClosed (hs a ha)) T hT hc v
    (frequencyKernel F r) (fun j ↦ frequencyKernel F (b j))
    (contDiff_frequencyKernel hF hr) (tsupport_frequencyKernel hX.isClosed hY.isClosed hrs)
    (fun j ↦ contDiff_frequencyKernel hF (hb j))
    (fun j ↦ tsupport_frequencyKernel hX.isClosed hY.isClosed (hbs j)) R B hR hB
    (frequencyKernel_source_identity hU hF hk hc v r b hr hb hid) hdf hpf

end JanetCartan.ResponseTransfer.NearCarrierParameter
