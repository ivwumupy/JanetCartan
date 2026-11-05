module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionRelation.Suspension
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.Eikonal

/-!
# Primary eikonal graphs for the direct root evolution

The graph-preservation step of `paper-v2.tex`,
`app:ch_response:lem:energy-carrier-jets`, for the literal Hamiltonian `τ-h`.
We reuse the Hessian symmetry and whole-segment uniqueness proofs in
`ProtectedFlow`. Smoothness supplies the defect Lipschitz constant on the
retained compact buffers; neither tangency nor graph preservation is assumed.

The inputs are a smooth root, the primary phase's equation for that SAME root,
and containment of the entire trajectory and phase graph in common buffers.
`PencilRoot` constructs the root; identification of its branch with the selected
primary chart and finite common buffers remain actual-construction obligations.
The conclusions apply to either sign and either time orientation, without any
carrier frequency, atom, sample or accuracy parameter.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff InnerProductSpace Topology NNReal

namespace JanetCartan.CompatibleResponse
open ArbitraryAccuracy RegularSector.Characteristic
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ}

private theorem contDiff_spacetimeRootState :
    ContDiff ℝ ∞ (spacetimeRootState (d := d)) :=
  ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.comp contDiff_fst).prodMk
    ((spatialPartCLM.contDiff.comp contDiff_fst).prodMk
      (spatialPartCLM.contDiff.comp contDiff_snd))

private theorem contDiffOn_primary_gradient {Ω : Set (Euclidean (d + 1))}
    {φ : Euclidean (d + 1) → ℝ} (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ φ Ω) :
    ContDiffOn ℝ ∞ (gradient φ) Ω :=
  (InnerProductSpace.toDual ℝ (Euclidean (d + 1))).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (hφ.fderiv_of_isOpen hΩ (by simp))

private theorem contDiffOn_suspensionField
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D) :
    ContDiffOn ℝ ∞ (rootSuspensionField h) (spacetimeRootState ⁻¹' D) := by
  have hopen := hD.preimage contDiff_spacetimeRootState.continuous
  have hs : ContDiffOn ℝ ∞ (rootSuspension h) (spacetimeRootState ⁻¹' D) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.comp_contDiffOn
      contDiffOn_snd).sub
        (hh.comp contDiff_spacetimeRootState.contDiffOn (fun _ hz ↦ hz))
  apply (HamiltonPhase.hamiltonFieldOfDifferential.contDiff.comp_contDiffOn
    (hs.fderiv_of_isOpen hopen (by simp))).congr
  intro z hz
  exact rootSuspensionField_eq_differential
    ((hh.contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp))

/-- The original root eikonal equation makes the full differential graph
tangent to the actual suspended field. This is the differential step of
`app:ch_response:lem:energy-carrier-jets`; Hessian symmetry is reused from
`ProtectedFlow`, and no flow or phase matching is assumed. -/
theorem rootSuspension_tangent_of_eikonal
    {h : RootState (Euclidean d) → ℝ} {φ : Euclidean (d + 1) → ℝ}
    {x : Euclidean (d + 1)} {dg : Euclidean (d + 1) →L[ℝ] Euclidean (d + 1)}
    (hφ : ContDiffAt ℝ 2 φ x) (hg : HasFDerivAt (gradient φ) dg x)
    (hh : DifferentiableAt ℝ h (spacetimeRootState (x, gradient φ x)))
    (he : (fun y ↦ rootSuspension h (y, gradient φ y)) =ᶠ[𝓝 x] (fun _ ↦ 0)) :
    (rootSuspensionField h (x, gradient φ x)).2 =
      dg (rootSuspensionField h (x, gradient φ x)).1 := by
  have hd := (hasFDerivAt_rootSuspension hh).comp x ((hasFDerivAt_id x).prodMk hg)
  have hz := (hd.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_const (0 : ℝ) x)
  apply ext_inner_right ℝ
  intro v
  have hv := congrArg (fun L : Euclidean (d + 1) →L[ℝ] ℝ ↦ L v) hz
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, HamiltonPhase.hamiltonDifferential_apply,
    zero_apply, inner_neg_left] at hv
  rw [ProtectedFlow.gradient_derivative_symmetric hφ hg]
  have hc := real_inner_comm (dg v) (rootSuspensionField h (x, gradient φ x)).1
  linarith

/-- Smoothness of the actual root and primary phase supplies one uniform
defect Lipschitz constant on compact physical/covector buffers. Consumer:
`root_characteristic_preserves_primary`, not an assumed invariance interface
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem exists_root_primary_defect_lipschitz
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    {Ω Y P : Set (Euclidean (d + 1))} {φ : Euclidean (d + 1) → ℝ}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ φ Ω)
    (hY : IsCompact Y) (hP : IsCompact P) (hYΩ : Y ⊆ Ω)
    (hprod : MapsTo spacetimeRootState (Y ×ˢ P) D) :
    ∃ L : ℝ≥0, ∀ x ∈ Y, LipschitzOnWith L
      (fun p ↦ (rootSuspensionField h (x, p)).2 -
        fderiv ℝ (gradient φ) x (rootSuspensionField h (x, p)).1) P := by
  let S := (Ω ×ˢ univ) ∩ spacetimeRootState ⁻¹' D
  have hS : IsOpen S := (hΩ.prod isOpen_univ).inter
    (hD.preimage contDiff_spacetimeRootState.continuous)
  have hK : Y ×ˢ P ⊆ S := fun z hz ↦ ⟨⟨hYΩ hz.1, mem_univ _⟩, hprod hz⟩
  have hv := (contDiffOn_suspensionField hD hh).mono (inter_subset_right (s := Ω ×ˢ univ))
  have hg := ((contDiffOn_primary_gradient hΩ hφ).fderiv_of_isOpen hΩ
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).comp contDiffOn_fst
      (fun z (hz : z ∈ S) ↦ hz.1.1)
  have hf := (hv.snd.sub (hg.clm_apply hv.fst)).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hloc : LocallyLipschitzOn (Y ×ˢ P)
      (fun z ↦ (rootSuspensionField h z).2 -
        fderiv ℝ (gradient φ) z.1 (rootSuspensionField h z).1) := by
    intro z hz
    obtain ⟨L, V, hV, hL⟩ := (hf.contDiffAt (hS.mem_nhds (hK hz))).exists_lipschitzOnWith
    exact ⟨L, V, mem_nhdsWithin_of_mem_nhds hV, hL⟩
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hY.prod hP) hloc
  refine ⟨L, fun x hx p hp q hq ↦ ?_⟩
  simpa only [edist_dist, dist_prod_same_left] using
    hL (show (x, p) ∈ Y ×ˢ P from ⟨hx, hp⟩) (show (x, q) ∈ Y ×ˢ P from ⟨hx, hq⟩)

/-- A complete direct root trajectory starting on the primary differential
graph stays on that graph. The same scalar root occurs in the eikonal equation
and the actual ODE. All intermediate physical and covector containment is
retained, and the initial time may be either endpoint or an interior point.
The defect estimate is constructed above from smooth primitive data
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem root_characteristic_preserves_primary
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    {Ω W Y P : Set (Euclidean (d + 1))} {φ : Euclidean (d + 1) → ℝ}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ φ Ω) (hW : IsOpen W)
    (hY : IsCompact Y) (hP : IsCompact P) (hWY : W ⊆ Y) (hYΩ : Y ⊆ Ω)
    (hprod : MapsTo spacetimeRootState (Y ×ˢ P) D)
    (hgP : MapsTo (gradient φ) W P)
    (he : ∀ x ∈ W, rootSuspension h (x, gradient φ x) = 0)
    {Z : ℝ → RootState (Euclidean d)} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hZ : ∀ t ∈ Icc a b, HasDerivAt Z (rootHamiltonField h (Z t)) t)
    (hZW : ∀ t ∈ Icc a b, (rootSuspensionState h 0 (Z t)).1 ∈ W)
    (hZP : ∀ t ∈ Icc a b, (rootSuspensionState h 0 (Z t)).2 ∈ P)
    (hi : (rootSuspensionState h 0 (Z t₀)).2 =
      gradient φ (rootSuspensionState h 0 (Z t₀)).1) :
    ∀ t ∈ Icc a b, (rootSuspensionState h 0 (Z t)).2 =
      gradient φ (rootSuspensionState h 0 (Z t)).1 := by
  have hg := contDiffOn_primary_gradient hΩ hφ
  have hder x (hx : x ∈ W) :=
    ((hg.contDiffAt (hΩ.mem_nhds (hYΩ (hWY hx)))).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨L, hL⟩ := exists_root_primary_defect_lipschitz hD hh hΩ hφ hY hP hYΩ hprod
  have hZdom t (ht : t ∈ Icc a b) : Z t ∈ D := by
    simpa only [spacetimeRootState_rootSuspensionState] using
      hprod ⟨hWY (hZW t ht), hZP t ht⟩
  have hlift t (ht : t ∈ Icc a b) := hasDerivAt_rootSuspensionState 0
    ((hh.contDiffAt (hD.mem_nhds (hZdom t ht))).differentiableAt (by simp)) (hZ t ht)
  apply ProtectedFlow.characteristic_stays_on_graph
    (A := fun x p ↦ (rootSuspensionField h (x, p)).1)
    (B := fun x p ↦ (rootSuspensionField h (x, p)).2)
    ht₀ hder ?_ (fun x hx ↦ hL x (hWY hx))
    (fun t ht ↦ (hlift t ht).fst) (fun t ht ↦ (hlift t ht).snd) hZW hZP hgP hi
  intro x hx
  exact rootSuspension_tangent_of_eikonal
    ((hφ.contDiffAt (hΩ.mem_nhds (hYΩ (hWY hx)))).of_le (by simp)) (hder x hx)
    ((hh.contDiffAt (hD.mem_nhds (hprod ⟨hWY hx, hgP hx⟩))).differentiableAt (by simp))
    (eventuallyEq_of_mem (hW.mem_nhds hx) (fun y hy ↦ he y hy))

/-- On the preserved zero-energy graph, Euler's identity for the actual root
makes the primary phase constant along the characteristic. The graph equality
is supplied by `root_characteristic_preserves_primary`; the local homogeneity
is an output of `PencilRoot.exists_pencilRoot_domain`
(`app:ch_response:lem:energy-carrier-jets`, zero critical value). -/
theorem hasDerivAt_primary_along_root_eq_zero
    {h : RootState (Euclidean d) → ℝ} {φ : Euclidean (d + 1) → ℝ}
    {Z : ℝ → RootState (Euclidean d)} {t : ℝ}
    (hh : DifferentiableAt ℝ h (Z t))
    (hhom : ∀ᶠ c : ℝ in 𝓝 1, h ((Z t).1, ((Z t).2.1, c • (Z t).2.2)) = c * h (Z t))
    (hφ : DifferentiableAt ℝ φ (rootSuspensionState h 0 (Z t)).1)
    (hZ : HasDerivAt Z (rootHamiltonField h (Z t)) t)
    (hg : (rootSuspensionState h 0 (Z t)).2 =
      gradient φ (rootSuspensionState h 0 (Z t)).1) :
    HasDerivAt (fun u ↦ φ (rootSuspensionState h 0 (Z u)).1) 0 t := by
  have hd := hφ.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_rootSuspensionState 0 hh hZ).fst
  convert! hd using 1
  rw [← inner_gradient_left, ← hg]
  simp only [rootSuspensionField, spacetimeRootState_rootSuspensionState]
  simp only [rootSuspensionState, inner_eq_time_add_spatial,
    timeSpacePoint_time, spatialPart_timeSpacePoint, zero_add, mul_one,
    inner_neg_right, root_euler hh hhom, add_neg_cancel]

/-- Both the differential graph and the value of the SAME primary phase are
preserved on the whole direct root segment. All bounds precede times and no
frequency enters the statement. This supplies the zero critical value in
`app:ch_response:lem:energy-carrier-jets`; the original eikonal and common
buffer premises still have to be instantiated for the finite selected family. -/
theorem root_characteristic_preserves_primary_phase
    {h : RootState (Euclidean d) → ℝ} {D : Set (RootState (Euclidean d))}
    {Ω W Y P : Set (Euclidean (d + 1))} {φ : Euclidean (d + 1) → ℝ}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hhom : ∀ z ∈ D, ∀ᶠ c : ℝ in 𝓝 1, h (z.1, (z.2.1, c • z.2.2)) = c * h z)
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ ∞ φ Ω) (hW : IsOpen W)
    (hY : IsCompact Y) (hP : IsCompact P) (hWY : W ⊆ Y) (hYΩ : Y ⊆ Ω)
    (hprod : MapsTo spacetimeRootState (Y ×ˢ P) D)
    (hgP : MapsTo (gradient φ) W P)
    (he : ∀ x ∈ W, rootSuspension h (x, gradient φ x) = 0)
    {Z : ℝ → RootState (Euclidean d)} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (hZ : ∀ t ∈ Icc a b, HasDerivAt Z (rootHamiltonField h (Z t)) t)
    (hZW : ∀ t ∈ Icc a b, (rootSuspensionState h 0 (Z t)).1 ∈ W)
    (hZP : ∀ t ∈ Icc a b, (rootSuspensionState h 0 (Z t)).2 ∈ P)
    (hi : (rootSuspensionState h 0 (Z t₀)).2 =
      gradient φ (rootSuspensionState h 0 (Z t₀)).1) :
    ∀ t ∈ Icc a b,
      (rootSuspensionState h 0 (Z t)).2 = gradient φ (rootSuspensionState h 0 (Z t)).1 ∧
      φ (rootSuspensionState h 0 (Z t)).1 = φ (rootSuspensionState h 0 (Z t₀)).1 := by
  have hg := root_characteristic_preserves_primary hD hh hΩ hφ hW hY hP hWY hYΩ
    hprod hgP he ht₀ hZ hZW hZP hi
  have hd t (ht : t ∈ Icc a b) :
      HasDerivAt (fun u ↦ φ (rootSuspensionState h 0 (Z u)).1) 0 t := by
    have hz : Z t ∈ D := by
      simpa only [spacetimeRootState_rootSuspensionState] using
        hprod ⟨hWY (hZW t ht), hZP t ht⟩
    exact hasDerivAt_primary_along_root_eq_zero
      ((hh.contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp)) (hhom _ hz)
      ((hφ.contDiffAt (hΩ.mem_nhds (hYΩ (hWY (hZW t ht))))).differentiableAt (by simp))
      (hZ t ht) (hg t ht)
  intro t ht
  refine ⟨hg t ht, ?_⟩
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu ↦ (hd u hu).hasDerivWithinAt) (fun _ _ ↦ norm_zero.le)
    (convex_Icc a b) ht₀ ht
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hb

end JanetCartan.CompatibleResponse
