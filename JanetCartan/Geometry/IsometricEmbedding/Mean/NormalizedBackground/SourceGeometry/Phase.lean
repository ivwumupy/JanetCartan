module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.QuotientSmoothness
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Phase

/-!
# The source-rescaled phase and its extension

The phase formulas in `app:ch_background:eq:bg-Nsigma`. These deductions take
an unscaled phase as input. The Hamilton construction must identify that phase
with its inverse projection chart; no existence of such a chart is asserted here.
The canonical labels are unchanged. In particular, their derivative has a factor
`ρ⁻¹`, unlike the physical derivative. All extensions use the existing integral
`phaseShiftQuotient`, applied to the physical variable.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff InnerProductSpace

namespace JanetCartan.NormalizedBackground.SourceGeometry

variable {E Z : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The positive-scale phase in `app:ch_background:eq:bg-Nsigma`.
Its value at zero scale is not the smooth extension. -/
def sourcePhase (S : E × Z → ℝ) (ρ : ℝ) (q : E × Z) : ℝ :=
  ρ⁻¹ * S (ρ • q.1, q.2)

/-- The full differential of the source-scaled phase, retaining the unchanged
canonical labels (`app:ch_background:eq:bg-Nsigma`). -/
theorem hasFDerivAt_sourcePhase {S : E × Z → ℝ} {ρ : ℝ} {q : E × Z}
    {L : E × Z →L[ℝ] ℝ} (hS : HasFDerivAt S L (ρ • q.1, q.2)) :
    HasFDerivAt (sourcePhase S ρ)
      (ρ⁻¹ • L.comp ((ρ • ContinuousLinearMap.fst ℝ E Z).prod
        (ContinuousLinearMap.snd ℝ E Z))) q := by
  exact (hS.comp q (((ContinuousLinearMap.fst ℝ E Z).hasFDerivAt.const_smul ρ).prodMk
    (ContinuousLinearMap.snd ℝ E Z).hasFDerivAt)).const_mul ρ⁻¹

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- The scale cancels in the physical derivative
(`app:ch_background:eq:bg-Nsigma`). -/
theorem hasFDerivAt_sourcePhase_position {S : E × Z → ℝ} {ρ : ℝ}
    {x : E} {z : Z} {L : E →L[ℝ] ℝ} (hρ : ρ ≠ 0)
    (hS : HasFDerivAt (fun y ↦ S (y, z)) L (ρ • x)) :
    HasFDerivAt (fun y ↦ sourcePhase S ρ (y, z)) L x := by
  have hd := (hS.comp x ((hasFDerivAt_id x).const_smul ρ)).const_mul ρ⁻¹
  have heq : ρ⁻¹ • L.comp (ρ • ContinuousLinearMap.id ℝ E) = L := by
    ext v
    simp [hρ]
  rw [heq] at hd
  exact hd

/-- The canonical derivative is `ρ⁻¹` times the seed footpoint, with no
rescaling of the canonical label (`app:ch_background:eq:bg-Nsigma`). -/
theorem hasFDerivAt_sourcePhase_parameter {S : E × Z → ℝ} {ρ : ℝ}
    {x : E} {z : Z} {L : Z →L[ℝ] ℝ}
    (hS : HasFDerivAt (fun w ↦ S (ρ • x, w)) L z) :
    HasFDerivAt (fun w ↦ sourcePhase S ρ (x, w)) (ρ⁻¹ • L) z :=
  hS.const_mul ρ⁻¹

variable [CompleteSpace E]

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- The actual physical covector of the source phase is the seed covector at
`ρx` (`app:ch_background:eq:bg-Nsigma`). -/
theorem gradient_sourcePhase_position {S : E × Z → ℝ} {ρ : ℝ}
    {x : E} {z : Z} (hρ : ρ ≠ 0)
    (hS : DifferentiableAt ℝ (fun y ↦ S (y, z)) (ρ • x)) :
    gradient (fun y ↦ sourcePhase S ρ (y, z)) x =
      gradient (fun y ↦ S (y, z)) (ρ • x) := by
  unfold gradient
  rw [(hasFDerivAt_sourcePhase_position hρ hS.hasFDerivAt).fderiv]

/-- Integral extension of this same phase through zero, from
`app:ch_background:prop:bg-normalized`. The base point is physical zero. -/
def sourcePhaseExtension (S : E × Z → ℝ) (q : ℝ × (E × Z)) : ℝ :=
  phaseShiftQuotient (fun z x ↦ S (x, z)) q.2.2 0 q.2.1 q.1

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- The zero slice of the divided phase is linear in the physical variable
(`app:ch_background:prop:bg-normalized`). -/
@[simp] theorem sourcePhaseExtension_zero (S : E × Z → ℝ) (x : E) (z : Z) :
    sourcePhaseExtension S (0, (x, z)) =
      inner ℝ (gradient (fun y ↦ S (y, z)) 0) x := by
  simp [sourcePhaseExtension]

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Identification with the positive-scale phase uses the actual seed Cauchy
value at zero (`app:ch_background:eq:bg-Nsigma`). -/
theorem sourcePhase_eq_extension {S : E × Z → ℝ} {U : Set E}
    (hU : IsOpen U) (hc : Convex ℝ U) {ρ : ℝ} {x : E} {z : Z}
    (hS : ContDiffOn ℝ 1 (fun y ↦ S (y, z)) U)
    (hzero : S (0, z) = 0) (h0 : (0 : E) ∈ U) (hx : ρ • x ∈ U) (hρ : ρ ≠ 0) :
    sourcePhase S ρ (x, z) = sourcePhaseExtension S (ρ, (x, z)) := by
  simpa [sourcePhase, sourcePhaseExtension, hzero, div_eq_mul_inv, mul_comm] using
    (phase_div_eq_phaseShiftQuotient (S := fun z x ↦ S (x, z))
      hU hc hS h0 (by simpa using hx) hρ)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z]

/-- One open domain for every mixed derivative, including the zero slice,
with an explicit open enlargement of the integration interval
(`app:ch_background:prop:bg-normalized`). The parameter `Z` may include carrier
and canonical covector variables together. -/
theorem contDiffOn_sourcePhaseExtension {S : E × Z → ℝ}
    {U : Set E} {V : Set Z} {D : Set (ℝ × (E × Z))} {W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hD : IsOpen D) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    (hmem : ∀ q ∈ D, ∀ t ∈ W, ((t * q.1) • q.2.1, q.2.2) ∈ U ×ˢ V) :
    ContDiffOn ℝ ∞ (sourcePhaseExtension S) D := by
  have hs : ContDiffOn ℝ ∞ (Function.uncurry (fun z x ↦ S (x, z))) (V ×ˢ U) :=
    hS.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ h ↦ ⟨h.2, h.1⟩)
  unfold sourcePhaseExtension
  apply FullPhaseCharts.contDiffOn_phaseShiftQuotient_comp hV hU hD hW hIW hs
    contDiffOn_snd.snd contDiffOn_const contDiffOn_snd.fst contDiffOn_fst
  intro q hq t ht
  simpa using ⟨(hmem q hq t ht).2, (hmem q hq t ht).1⟩

set_option maxHeartbeats 600000 in
/-- Joint smoothness of the canonical footpoint differential of the extended
phase, including zero (`app:ch_background:prop:bg-normalized`). It is the
canonical derivative of the divided phase, not the undivided seed footpoint. -/
theorem contDiffOn_sourcePhaseExtension_parameterFDeriv {S : E × Z → ℝ}
    {U B : Set E} {V : Set Z} {I W : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hB : IsOpen B) (hI : IsOpen I)
    (hW : IsOpen W) (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hS : ContDiffOn ℝ ∞ S (U ×ˢ V))
    (hmem : ∀ q ∈ I ×ˢ B ×ˢ V, ∀ t ∈ W,
      ((t * q.1) • q.2.1, q.2.2) ∈ U ×ˢ V) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (E × Z) ↦
      fderiv ℝ (fun z ↦ sourcePhaseExtension S (q.1, (q.2.1, z))) q.2.2)
      (I ×ˢ B ×ˢ V) := by
  have hs := contDiffOn_sourcePhaseExtension hU hV (hI.prod (hB.prod hV)) hW hIW hS hmem
  have hs' : ContDiffOn ℝ ∞
      (fun q : Z × (ℝ × E) ↦ sourcePhaseExtension S (q.2.1, (q.2.2, q.1)))
      (V ×ˢ I ×ˢ B) := hs.comp
    (contDiffOn_snd.fst.prodMk (contDiffOn_snd.snd.prodMk contDiffOn_fst))
    (fun _ h ↦ ⟨h.2.1, h.2.2, h.1⟩)
  exact (contDiffOn_parameterFDeriv hV (hI.prod hB) hs').comp
    (contDiffOn_snd.snd.prodMk (contDiffOn_fst.prodMk contDiffOn_snd.fst))
    (fun _ h ↦ ⟨h.2.2, h.1, h.2.1⟩)

section Chart

variable {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Inverse physical time and section coordinates divide by the source scale;
canonical covectors are unchanged (`app:ch_background:eq:bg-Nsigma`). -/
def sourceCoordinates (C : E × (ℝ × Y) → ℝ × Y) (ρ : ℝ)
    (q : E × (ℝ × Y)) : ℝ × Y := ρ⁻¹ • C (ρ • q.1, q.2)

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace E]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z] in
/-- The literal Hamilton chart formula gives exactly the divided source phase
(`app:ch_background:eq:bg-Nsigma`). This names the compatible chart choice;
it does not identify independently selected existential inverses. -/
theorem phase_sourceCoordinates (C : E × (ℝ × Y) → ℝ × Y) (ρ : ℝ)
    (q : E × (ℝ × Y)) :
    HamiltonPhase.phase (sourceCoordinates C ρ) q =
      sourcePhase (HamiltonPhase.phase C) ρ q := by
  simp only [HamiltonPhase.phase, sourceCoordinates, sourcePhase, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, real_inner_smul_left]
  ring

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace E]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z] in
/-- The same linear Cauchy section has value `u · η'` after rescaling
(`app:ch_background:eq:bg-Nsigma`). The sole Cauchy input is the seed inverse
chart at the scaled section point. -/
theorem phase_sourceCoordinates_on_section
    {C : E × (ℝ × Y) → ℝ × Y} (j : Y →L[ℝ] E)
    {ρ : ℝ} (hρ : ρ ≠ 0) {u : Y} {η : ℝ × Y}
    (hC : C (j (ρ • u), η) = (0, ρ • u)) :
    HamiltonPhase.phase (sourceCoordinates C ρ) (j u, η) = inner ℝ u η.2 := by
  apply HamiltonPhase.phase_on_section
  rw [j.map_smul] at hC
  simp [sourceCoordinates, hC, smul_smul, hρ]

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z] in
/-- Eikonal identity of the named source phase from a genuine seed chart,
before identifying the source-dilated symbol (`app:ch_background:eq:bg-Nsigma`). -/
theorem sourcePhase_eikonal {H : HamiltonPhase.HomogeneousSymbol E}
    {Φ : HamiltonPhase.HamiltonFlow H Y} (C : HamiltonPhase.ProjectionChart Φ)
    {ρ : ℝ} (hρ : ρ ≠ 0) {x : E} {η : ℝ × Y} (hz : (ρ • x, η) ∈ C.target) :
    H.h (ρ • x, gradient (fun y ↦ sourcePhase (HamiltonPhase.phase C.coordinates) ρ (y, η)) x) =
      η.1 := by
  have hi : DifferentiableAt ℝ (fun y : E ↦ (y, η)) (ρ • x) :=
    differentiableAt_id.prodMk (differentiableAt_const η)
  have hd : DifferentiableAt ℝ (fun y ↦ HamiltonPhase.phase C.coordinates (y, η)) (ρ • x) :=
    by simpa only [Function.comp_def] using
      (HamiltonPhase.ProjectionChart.hasFDerivAt_phase C hz).differentiableAt.comp (ρ • x) hi
  rw [gradient_sourcePhase_position hρ hd]
  exact C.eikonal hz

end Chart

end JanetCartan.NormalizedBackground.SourceGeometry
