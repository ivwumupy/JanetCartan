module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Construction
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The mixed derivative on a Hamilton projection chart

For `app:lem:common-hamilton-phase`, differentiate the two inverse identities
at fixed canonical parameter, then use symmetry of the phase Hessian. The
canonical space retains its product norm throughout.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The canonical pairing as a continuous bilinear map, using the product norm
(`app:lem:common-hamilton-phase`). -/
def canonicalCovectorLinear : (ℝ × U) →L[ℝ] (ℝ × U) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ U).smulRight (ContinuousLinearMap.fst ℝ ℝ U) +
    ((ContinuousLinearMap.compL ℝ (ℝ × U) U ℝ).flip
      (ContinuousLinearMap.snd ℝ ℝ U)).comp
        ((show U →L[ℝ] U →L[ℝ] ℝ from innerSL ℝ).comp (ContinuousLinearMap.snd ℝ ℝ U))

/-- Evaluation recovers the split canonical covector
(`app:lem:common-hamilton-phase`). -/
@[simp] theorem canonicalCovectorLinear_apply (q : ℝ × U) :
    canonicalCovectorLinear q = canonicalCovector q := rfl

/-- The phase differential depends continuously and linearly on momentum and
inverse coordinates (`app:lem:common-hamilton-phase`). -/
def phaseDifferentialLinear : (E × (ℝ × U)) →L[ℝ] (E × (ℝ × U)) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (E × (ℝ × U)) E ℝ).flip
      (ContinuousLinearMap.fst ℝ E (ℝ × U))).comp
    ((show E →L[ℝ] E →L[ℝ] ℝ from innerSL ℝ).comp
      (ContinuousLinearMap.fst ℝ E (ℝ × U))) +
  ((ContinuousLinearMap.compL ℝ (E × (ℝ × U)) (ℝ × U) ℝ).flip
      (ContinuousLinearMap.snd ℝ E (ℝ × U))).comp
    (canonicalCovectorLinear.comp (ContinuousLinearMap.snd ℝ E (ℝ × U)))

/-- Evaluation recovers the Hamilton phase differential
(`app:lem:common-hamilton-phase`). -/
@[simp] theorem phaseDifferentialLinear_apply (p : E) (q : ℝ × U) :
    phaseDifferentialLinear (p, q) = phaseDifferential p q := rfl

namespace ProjectionChart

variable {H : HomogeneousSymbol E} {Φ : HamiltonFlow H U} (C : ProjectionChart Φ)

/-- The physical derivative of inverse time and section coordinates
(`app:lem:common-hamilton-phase`). -/
def coordinatePositionDerivative (z : E × (ℝ × U)) : E →L[ℝ] ℝ × U :=
  (C.derivative z).comp (ContinuousLinearMap.inl ℝ E (ℝ × U))

/-- The physical partial derivative is the restriction of the full chart
 derivative (`app:lem:common-hamilton-phase`). -/
theorem hasFDerivAt_coordinates_position {z : E × (ℝ × U)} (hz : z ∈ C.target) :
    HasFDerivAt (fun x ↦ C.coordinates (x, z.2)) (C.coordinatePositionDerivative z) z.1 :=
  (C.hasFDerivAt_coordinates z hz).comp z.1
    ((hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1))

/-- Both inverse identities, differentiated with the canonical parameter fixed,
make the physical chart derivative an equivalence (`app:lem:common-hamilton-phase`). -/
theorem exists_coordinatePositionEquiv {z : E × (ℝ × U)} (hz : z ∈ C.target) :
    ∃ A : E ≃L[ℝ] (ℝ × U), (A : E →L[ℝ] ℝ × U) = C.coordinatePositionDerivative z := by
  let g : E → ℝ × U := fun x ↦ C.coordinates (x, z.2)
  let f : ℝ × U → E := fun q ↦ Φ.position (q.1, (q.2, z.2))
  have hg := C.hasFDerivAt_coordinates_position hz
  have ha := C.source_admissible _ (C.maps_to_source z hz)
  have hf := (Φ.position_derivative _ ha.1 _ ha.2).comp (C.coordinates z)
    ((ContinuousLinearMap.fst ℝ ℝ U).hasFDerivAt.prodMk
      ((ContinuousLinearMap.snd ℝ ℝ U).hasFDerivAt.prodMk (hasFDerivAt_const z.2 _)))
  let B := fderiv ℝ f (C.coordinates z)
  have hfB : HasFDerivAt f B (g z.1) := hf.differentiableAt.hasFDerivAt
  have hfg : f (g z.1) = z.1 := C.right_inverse z hz
  have hfgN : (fun x ↦ f (g x)) =ᶠ[𝓝 z.1] id := by
    have hn := (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
      (C.isOpen_target.mem_nhds hz)
    filter_upwards [hn] with x hx using C.right_inverse (x, z.2) hx
  have hgfN : (fun q ↦ g (f q)) =ᶠ[𝓝 (g z.1)] id := by
    have hn := (continuousAt_fst.prodMk (continuousAt_snd.prodMk continuousAt_const)).preimage_mem_nhds
      (C.isOpen_source.mem_nhds (C.maps_to_source z hz))
    filter_upwards [hn] with q hq using C.left_inverse (q.1, (q.2, z.2)) hq
  have hBA := ((hfB.comp z.1 hg).congr_of_eventuallyEq hfgN.symm).unique (hasFDerivAt_id z.1)
  have hg' : HasFDerivAt g (C.coordinatePositionDerivative z) (f (g z.1)) := by
    rw [hfg]; exact hg
  have hAB := ((hg'.comp (g z.1) hfB).congr_of_eventuallyEq hgfN.symm).unique
    (hasFDerivAt_id (g z.1))
  refine ⟨ContinuousLinearEquiv.equivOfInverse (C.coordinatePositionDerivative z) B ?_ ?_, rfl⟩
  · intro x
    exact congrArg (fun L : E →L[ℝ] E ↦ L x) hBA
  · intro q
    exact congrArg (fun L : (ℝ × U) →L[ℝ] (ℝ × U) ↦ L q) hAB

/-- Transported momentum expressed on the actual inverse chart
(`app:lem:common-hamilton-phase`). -/
def chartMomentum (z : E × (ℝ × U)) : E := Φ.momentum (chartLift C.coordinates z)

/-- The phase gradient equals transported momentum on the target
(`app:ch_regular_base:eq:actual-eikonal`). -/
theorem gradient_phase_eq_chartMomentum [CompleteSpace E]
    {z : E × (ℝ × U)} (hz : z ∈ C.target) :
    gradient (fun x ↦ phase C.coordinates (x, z.2)) z.1 = C.chartMomentum z := by
  have ha := C.source_admissible _ (C.maps_to_source z hz)
  exact (show HasGradientAt (fun x ↦ phase C.coordinates (x, z.2)) (C.chartMomentum z) z.1 from
    Φ.hasFDerivAt_phase_position (C.hasFDerivAt_coordinates z hz) ha.1 ha.2
      (eventuallyEq_of_mem (C.isOpen_target.mem_nhds hz) (fun w hw ↦ C.right_inverse w hw))).gradient

/-- Smooth momentum and inverse coordinates give smooth transported momentum
(`app:lem:common-hamilton-phase`). -/
theorem contDiffOn_chartMomentum
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target) :
    ContDiffOn ℝ ∞ C.chartMomentum C.target := by
  exact hp.comp (hC.fst.prodMk (hC.snd.prodMk contDiff_snd.contDiffOn))
    (fun z hz ↦ C.source_admissible _ (C.maps_to_source z hz))

/-- The actual mixed phase derivative `D_η (gradient_x S)`
(`app:lem:common-hamilton-phase`). -/
def mixedMomentumDerivative [CompleteSpace E] (z : E × (ℝ × U)) : (ℝ × U) →L[ℝ] E :=
  fderiv ℝ (fun η ↦ gradient (fun x ↦ phase C.coordinates (x, η)) z.1) z.2

/-- The actual mixed derivative is computed by differentiating transported
momentum, with physical position fixed (`app:lem:common-hamilton-phase`). -/
theorem mixedMomentumDerivative_eq [CompleteSpace E]
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {z : E × (ℝ × U)} (hz : z ∈ C.target) :
    C.mixedMomentumDerivative z =
      (fderiv ℝ C.chartMomentum z).comp (ContinuousLinearMap.inr ℝ E (ℝ × U)) := by
  have hd := ((C.contDiffOn_chartMomentum hp hC).contDiffAt
    (C.isOpen_target.mem_nhds hz)).differentiableAt (by simp)
  have he : (fun η ↦ gradient (fun x ↦ phase C.coordinates (x, η)) z.1) =ᶠ[𝓝 z.2]
      (fun η ↦ C.chartMomentum (z.1, η)) := by
    have hn := (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
      (C.isOpen_target.mem_nhds hz)
    filter_upwards [hn] with η hη using C.gradient_phase_eq_chartMomentum hη
  exact ((hd.hasFDerivAt.comp (g := C.chartMomentum) (f := fun η ↦ (z.1, η)) z.2
    ((hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2))).congr_of_eventuallyEq he).fderiv

/-- Symmetry of the second phase derivative identifies the mixed momentum
map with the transpose of the physical inverse-chart derivative. The pairing
uses `canonicalCovector`, so no product inner-product instance is needed
(`app:lem:common-hamilton-phase`). -/
theorem mixedMomentumDerivative_pairing [CompleteSpace E]
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {z : E × (ℝ × U)} (hz : z ∈ C.target) (v : E) (η : ℝ × U) :
    ⟪C.mixedMomentumDerivative z η, v⟫_ℝ =
      canonicalCovector (C.coordinatePositionDerivative z v) η := by
  have hP := ((C.contDiffOn_chartMomentum hp hC).contDiffAt
    (C.isOpen_target.mem_nhds hz)).differentiableAt (by simp)
  have hD := (phaseDifferentialLinear (E := E) (U := U)).hasFDerivAt.comp
    (g := phaseDifferentialLinear) (f := fun w ↦ (C.chartMomentum w, C.coordinates w)) z
    (hP.hasFDerivAt.prodMk (C.hasFDerivAt_coordinates z hz))
  have he : ∀ᶠ w in 𝓝 z, HasFDerivAt (phase C.coordinates)
      (phaseDifferentialLinear (C.chartMomentum w, C.coordinates w)) w := by
    filter_upwards [C.isOpen_target.mem_nhds hz] with w hw
    exact C.hasFDerivAt_phase hw
  have hs := second_derivative_symmetric_of_eventually he hD (0, η) (v, 0)
  simpa [C.mixedMomentumDerivative_eq hp hC hz, coordinatePositionDerivative,
    phaseDifferentialLinear_apply, phaseDifferential_apply, canonicalCovector_apply] using hs

/-- Nondegeneracy of the canonical pairing transfers the chart derivative's
invertibility to the mixed derivative's injectivity
(`app:lem:common-hamilton-phase`). -/
theorem mixedMomentumDerivative_injective [CompleteSpace E]
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {z : E × (ℝ × U)} (hz : z ∈ C.target) :
    Function.Injective (C.mixedMomentumDerivative z) := by
  obtain ⟨A, hA⟩ := C.exists_coordinatePositionEquiv hz
  apply (injective_iff_map_eq_zero (C.mixedMomentumDerivative z)).mpr
  intro η hη
  have he := C.mixedMomentumDerivative_pairing hp hC hz (A.symm η) η
  rw [hη, inner_zero_left, ← hA] at he
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    canonicalCovector_apply] at he
  have h₁ : η.1 = 0 := by nlinarith [real_inner_self_nonneg (x := η.2)]
  have h₂ : η.2 = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp (by simpa [h₁] using he.symm)
  exact Prod.ext h₁ h₂

/-- In finite dimensions the actual mixed phase derivative is a continuous
linear equivalence; no mixed-Hessian gap is assumed
(`app:lem:common-hamilton-phase`). -/
theorem exists_mixedMomentumEquiv [CompleteSpace E]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {z : E × (ℝ × U)} (hz : z ∈ C.target) :
    ∃ A : (ℝ × U) ≃L[ℝ] E, (A : (ℝ × U) →L[ℝ] E) = C.mixedMomentumDerivative z := by
  obtain ⟨B, _⟩ := C.exists_coordinatePositionEquiv hz
  have hi := C.mixedMomentumDerivative_injective hp hC hz
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    B.toLinearEquiv.finrank_eq.symm (f := (C.mixedMomentumDerivative z).toLinearMap)).mp hi
  exact ⟨(LinearEquiv.ofBijective (C.mixedMomentumDerivative z).toLinearMap
    ⟨hi, hs⟩).toContinuousLinearEquiv, rfl⟩

/-- Joint continuity of the actual mixed derivative on the inverse chart
(`app:lem:common-hamilton-phase`). -/
theorem continuousOn_mixedMomentumDerivative [CompleteSpace E]
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target) :
    ContinuousOn C.mixedMomentumDerivative C.target := by
  have hd := (C.contDiffOn_chartMomentum hp hC).continuousOn_fderiv_of_isOpen
    C.isOpen_target (by simp)
  exact (hd.clm_comp continuousOn_const).congr (fun z hz ↦ C.mixedMomentumDerivative_eq hp hC hz)

/-- Each target point has an open neighborhood on which the actual mixed
phase derivative, normalized by its central equivalence, differs from identity
by at most `1/4` (`app:lem:common-hamilton-phase`). This is a local gap for one
symbol; common symbol-family neighborhoods are a separate assertion. -/
theorem exists_mixedMomentumDerivative_neighborhood [CompleteSpace E]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {z : E × (ℝ × U)} (hz : z ∈ C.target) :
    ∃ (A : (ℝ × U) ≃L[ℝ] E) (V : Set (E × (ℝ × U))),
      (A : (ℝ × U) →L[ℝ] E) = C.mixedMomentumDerivative z ∧
      IsOpen V ∧ z ∈ V ∧ V ⊆ C.target ∧
      ∀ w ∈ V, ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (C.mixedMomentumDerivative w) -
        ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ (1 / 4 : ℝ) := by
  obtain ⟨A, hA⟩ := C.exists_mixedMomentumEquiv hp hC hz
  have hc := (C.continuousOn_mixedMomentumDerivative hp hC).continuousAt
    (C.isOpen_target.mem_nhds hz)
  have hn : ContinuousAt (fun w ↦
      ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (C.mixedMomentumDerivative w) -
        ContinuousLinearMap.id ℝ (ℝ × U)‖) z :=
    ((continuousAt_const.clm_comp hc).sub continuousAt_const).norm
  have hzero : (A.symm : E →L[ℝ] (ℝ × U)).comp (C.mixedMomentumDerivative z) =
      ContinuousLinearMap.id ℝ (ℝ × U) := by
    rw [← hA]
    apply ContinuousLinearMap.ext
    intro η
    exact A.symm_apply_apply η
  have hsmall := hn.eventually (gt_mem_nhds (show
      ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (C.mixedMomentumDerivative z) -
        ContinuousLinearMap.id ℝ (ℝ × U)‖ < (1 / 4 : ℝ) by
      rw [hzero, sub_self]
      change ‖(0 : (ℝ × U) →L[ℝ] (ℝ × U))‖ < (1 / 4 : ℝ)
      rw [norm_zero (E := ((ℝ × U) →L[ℝ] (ℝ × U)))]
      norm_num))
  have ht : ∀ᶠ w in 𝓝 z, w ∈ C.target := C.isOpen_target.mem_nhds hz
  obtain ⟨V, hVsub, hV, hzV⟩ := eventually_nhds_iff.mp (ht.and hsmall)
  exact ⟨A, V, hA, hV, hzV, fun w hw ↦ (hVsub w hw).1,
    fun w hw ↦ (hVsub w hw).2.le⟩

end ProjectionChart
end JanetCartan.HamiltonPhase
