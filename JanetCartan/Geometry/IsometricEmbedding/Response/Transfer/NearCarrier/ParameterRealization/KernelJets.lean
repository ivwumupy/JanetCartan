module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterRealization.Frequency

/-!
# Closure of compact kernel jets under parameter transfer

For `app:ch_response:eq:direct-envelope-profile`, the smoothness and support
of the modified kernels follow from the original selected kernel and the
primitive coefficient jets. They are not additional analytic inputs. The
signed phase identities identify the constructed remainder with the literal
modified amplitude before a bounded realization is used.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ResponseTransfer.NearCarrierParameter
variable {d p : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin p)

/-- The source coordinate derivative of the full kernel. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
def sourceKernelDerivative (k : E × E → E → ℂ) (j : Fin d) (z : E × E) (δ : E) : ℂ :=
  fderiv ℝ (fun w ↦ k w δ) z (0, EuclideanSpace.single j 1)

/-- The full differential and the source-section differential agree. Consumer:
the source-divergence assembly in `app:ch_response:eq:direct-envelope-profile`. -/
theorem sourceKernelDerivative_eq
    {k : E × E → E → ℂ} {z : E × E} {δ : E}
    (hk : DifferentiableAt ℝ (fun w ↦ k w δ) z) (j : Fin d) :
    sourceKernelDerivative k j z δ =
      fderiv ℝ (fun y ↦ k (z.1, y) δ) z.2 (EuclideanSpace.single j 1) := by
  have h := hk.hasFDerivAt.comp z.2
    ((hasFDerivAt_const (𝕜 := ℝ) z.1 z.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) z.2))
  have he := congrArg (fun L : E →L[ℝ] ℂ ↦ L (EuclideanSpace.single j 1)) h.fderiv
  simpa only [Function.comp_def, id_eq, sourceKernelDerivative,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, zero_apply,
    ContinuousLinearMap.id_apply] using he.symm

/-- Source differentiation preserves smoothness of the full kernel, including
both physical positions and frequency (`app:ch_response:eq:direct-envelope-profile`). -/
theorem contDiff_sourceKernelDerivative
    {k : E × E → E → ℂ} (hk : ContDiff ℝ ∞ (Function.uncurry k)) (j : Fin d) :
    ContDiff ℝ ∞ (Function.uncurry (sourceKernelDerivative k j)) := by
  have h := contDiffOn_parameterFDeriv (U := (univ : Set (E × E)))
    isOpen_univ isOpen_univ hk.contDiffOn
  have h' : ContDiff ℝ ∞ (fun q : (E × E) × E ↦ fderiv ℝ (fun w ↦ k w q.2) q.1) :=
    contDiffOn_univ.mp (by simpa only [univ_prod_univ, Function.uncurry_def] using h)
  exact h'.clm_apply contDiff_const

/-- Source differentiation does not enlarge the physical carrier. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem tsupport_sourceKernelDerivative
    (k : E × E → E → ℂ) (j : Fin d) (δ : E) :
    tsupport (fun z ↦ sourceKernelDerivative k j z δ) ⊆ tsupport (fun z ↦ k z δ) :=
  tsupport_fderiv_apply_subset ℝ _

/-- The frozen parameter derivative is jointly smooth in both physical
positions and frequency. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiff_parameterKernel
    {U : Set P} (hU : IsOpen U) {k : P → E × E → E → ℂ}
    (hk : ContDiffOn ℝ ∞ (fun q : (P × (E × E)) × E ↦ k q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ univ)) {c : P} (hc : c ∈ U) (v : P) :
    ContDiff ℝ ∞ (fun q : (E × E) × E ↦ fderiv ℝ (fun a ↦ k a q.1 q.2) c v) := by
  have hk' : ContDiffOn ℝ ∞ (fun q : P × ((E × E) × E) ↦ k q.1 q.2.1 q.2.2)
      (U ×ˢ univ) :=
    hk.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd).contDiffOn
      (fun q hq ↦ ⟨⟨hq.1, mem_univ _⟩, mem_univ _⟩)
  have hd := contDiffOn_parameterFDeriv hU isOpen_univ hk'
  exact contDiffOn_univ.mp ((hd.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ _ ↦ ⟨hc, mem_univ _⟩)).clm_apply contDiffOn_const)

/-- Uniform physical support on an open parameter neighborhood also supports
the parameter derivative (`app:ch_response:eq:direct-envelope-profile`). -/
theorem tsupport_parameterKernel
    {U : Set P} (hU : IsOpen U) {X Y : Set E} (hX : IsClosed X) (hY : IsClosed Y)
    {k : P → E × E → E → ℂ} {δ : E}
    (hs : ∀ a ∈ U, tsupport (fun z ↦ k a z δ) ⊆ X ×ˢ Y)
    {c : P} (hc : c ∈ U) (v : P) :
    tsupport (fun z ↦ fderiv ℝ (fun a ↦ k a z δ) c v) ⊆ X ×ˢ Y := by
  apply closure_minimal _ (hX.prod hY)
  intro z hz
  by_contra hn
  have he : (fun a ↦ k a z δ) =ᶠ[𝓝 c] (fun _ ↦ (0 : ℂ)) := by
    filter_upwards [hU.mem_nhds hc] with a ha
    exact image_eq_zero_of_notMem_tsupport (f := fun z ↦ k a z δ)
      (fun h ↦ hn (hs a ha h))
  apply hz
  change fderiv ℝ (fun a ↦ k a z δ) c v = 0
  rw [he.fderiv_eq (𝕜 := ℝ)]
  simp

/-- Construct the remainder at kernel level, before identifying it with the
literal forward or reverse modified amplitude. This definition has no datum
and no operator realization (`app:ch_response:eq:direct-envelope-profile`). -/
def transferRemainderKernel (k : P → E × E → E → ℂ)
    (q : Fin d → E × E → E → ℂ) (c v : P) (z : E × E) (δ : E) : ℂ :=
  fderiv ℝ (fun a ↦ k a z δ) c v +
    ∑ j, sourceKernelDerivative (fun w η ↦ q j w η * k c w η) j z δ

/-- Primitive kernel and coefficient jets supply the remainder's smoothness.
Consumer: the actual parameter realization in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiff_transferRemainderKernel
    {U : Set P} (hU : IsOpen U) {k : P → E × E → E → ℂ}
    (hk : ContDiffOn ℝ ∞ (fun q : (P × (E × E)) × E ↦ k q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ univ)) {c : P} (hc : c ∈ U) (v : P)
    {q : Fin d → E × E → E → ℂ}
    (hq : ∀ j, ContDiff ℝ ∞ (Function.uncurry (q j))) :
    ContDiff ℝ ∞ (Function.uncurry (transferRemainderKernel k q c v)) := by
  have hcK : ContDiff ℝ ∞ (Function.uncurry (k c)) := by
    exact contDiffOn_univ.mp (hk.comp
      ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun _ _ ↦ ⟨⟨hc, mem_univ _⟩, mem_univ _⟩))
  exact (contDiff_parameterKernel hU hk hc v).add
    (ContDiff.sum fun j _ ↦ contDiff_sourceKernelDerivative ((hq j).mul hcK) j)

/-- Primitive common supports also support the constructed remainder. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem tsupport_transferRemainderKernel
    {U : Set P} (hU : IsOpen U) {X Y : Set E} (hX : IsClosed X) (hY : IsClosed Y)
    {k : P → E × E → E → ℂ} {δ : E}
    (hs : ∀ a ∈ U, tsupport (fun z ↦ k a z δ) ⊆ X ×ˢ Y)
    (q : Fin d → E × E → E → ℂ) {c : P} (hc : c ∈ U) (v : P) :
    tsupport (fun z ↦ transferRemainderKernel k q c v z δ) ⊆ X ×ˢ Y := by
  apply (tsupport_add _ _).trans
  apply union_subset (tsupport_parameterKernel hU hX hY hs hc v)
  apply closure_minimal _ (hX.prod hY)
  intro z hz
  by_contra hn
  apply hz
  change (∑ j, sourceKernelDerivative (fun w η ↦ q j w η * k c w η) j z δ) = 0
  apply Finset.sum_eq_zero
  intro j _
  apply image_eq_zero_of_notMem_tsupport (f := fun z ↦
    sourceKernelDerivative (fun w η ↦ q j w η * k c w η) j z δ)
  intro hz
  exact hn (hs c hc ((tsupport_mul_subset_right (f := fun z ↦ q j z δ) (g := fun z ↦ k c z δ))
    (tsupport_sourceKernelDerivative _ j δ hz)))

/-- The parameter transfer on L² from primitive smooth selected-kernel jets
and smooth coefficient jets. Smoothness and support of the modified kernels
are derived. `hr` is a pointwise kernel identity supplied by the proved signed
phase calculation; it contains neither an operator derivative nor any datum.
The parent must instantiate that identity with the literal amplitudes in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem hasLineDerivAt_frequency_transfer_of_coefficients
    {U : Set P} (hU : IsOpen U) {X Y F : Set E}
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    {k : P → E × E → E → ℂ}
    (hk : ContDiffOn ℝ ∞ (fun z : (P × (E × E)) × E ↦ k z.1.1 z.1.2 z.2)
      ((U ×ˢ univ) ×ˢ univ))
    (hs : ∀ a ∈ U, ∀ δ ∈ F, tsupport (fun z ↦ k a z δ) ⊆ X ×ˢ Y)
    {c : P} (hc : c ∈ U) (v : P)
    (q : Fin d → E × E → E → ℂ)
    (hq : ∀ j, ContDiff ℝ ∞ (Function.uncurry (q j)))
    (r : E × E → E → ℂ)
    (hr : ∀ x y δ, δ ∈ F → fderiv ℝ (fun a ↦ k a (x, y) δ) c v =
      r (x, y) δ - ∑ j, fderiv ℝ (fun z ↦ q j (x, z) δ * k c (x, z) δ) y
        (EuclideanSpace.single j 1))
    (T : P → Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (R : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (B : Fin d → Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (hT : ∀ a ∈ U, ∀ g : SchwartzMap E ℂ, T a (g.toLp 2 volume) =ᵐ[volume]
      fun x ↦ ∫ y, frequencyKernel F (k a) (x, y) * g y)
    (hR : ∀ g : SchwartzMap E ℂ, R (g.toLp 2 volume) =ᵐ[volume]
      fun x ↦ ∫ y, frequencyKernel F r (x, y) * g y)
    (hB : ∀ j, ∀ g : SchwartzMap E ℂ, B j (g.toLp 2 volume) =ᵐ[volume]
      fun x ↦ ∫ y, frequencyKernel F (fun z δ ↦ q j z δ * k c z δ) (x, y) * g y)
    {f : P → Lp ℂ 2 (volume : Measure E)}
    {df : Fin d → Lp ℂ 2 (volume : Measure E)} {pf : Lp ℂ 2 (volume : Measure E)}
    (hdf : ∀ j, Pseudodifferential.HasEuclideanL2CoordinateDerivative j (f c) (df j))
    (hpf : HasLineDerivAt ℝ f pf c v) :
    HasLineDerivAt ℝ (fun a ↦ T a (f a))
      (R (f c) + ∑ j, B j (df j) + T c pf) c v := by
  have hcK : ContDiff ℝ ∞ (Function.uncurry (k c)) :=
    contDiffOn_univ.mp (hk.comp
      ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun _ _ ↦ ⟨⟨hc, mem_univ _⟩, mem_univ _⟩))
  have hb (j : Fin d) : ContDiff ℝ ∞
      (fun z : (E × E) × E ↦ q j z.1 z.2 * k c z.1 z.2) := (hq j).mul hcK
  have hbs (j : Fin d) (δ : E) (hδ : δ ∈ F) :
      tsupport (fun z ↦ q j z δ * k c z δ) ⊆ X ×ˢ Y :=
    tsupport_mul_subset_right.trans (hs c hc δ hδ)
  have hd (j : Fin d) (z : E × E) (δ : E) :
      sourceKernelDerivative (fun w η ↦ q j w η * k c w η) j z δ =
        fderiv ℝ (fun y ↦ q j (z.1, y) δ * k c (z.1, y) δ) z.2
          (EuclideanSpace.single j 1) :=
    sourceKernelDerivative_eq
      (((hb j).comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) z) j
  have hreq (z : E × E) (δ : E) (hδ : δ ∈ F) :
      transferRemainderKernel k q c v z δ = r z δ := by
    simp only [transferRemainderKernel, hd, hr z.1 z.2 δ hδ, Prod.mk.eta,
      sub_add_cancel]
  have hReq : frequencyKernel F (transferRemainderKernel k q c v) = frequencyKernel F r := by
    funext z
    exact setIntegral_congr_fun hF.measurableSet (fun δ hδ ↦ hreq z δ hδ)
  apply hasLineDerivAt_frequency_kernel_transfer hU hX hY hF hk hs T hT hc v
    (transferRemainderKernel k q c v) (fun j z δ ↦ q j z δ * k c z δ)
    (contDiff_transferRemainderKernel hU hk hc v hq)
    (fun δ hδ ↦ tsupport_transferRemainderKernel hU hX.isClosed hY.isClosed
      (fun a ha ↦ hs a ha δ hδ) q hc v)
    hb hbs R B _ hB _ hdf hpf
  · simpa only [hReq] using hR
  · intro x y δ _
    simp only [transferRemainderKernel, hd, add_sub_cancel_right]

end JanetCartan.ResponseTransfer.NearCarrierParameter
