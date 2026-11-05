module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.TwoTimePhase
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RowTransport

/-!
# Signed transport on the constructed two-time Hamilton chart

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, use the
same inverse projection as `twoTimePhase` to transport signed row data. The
potential is pulled back along that actual projection. The inverse equations,
unchanged initial covector, diagonal data and physical velocity are proved
from the chart and Hamilton IVP, rather than supplied as transport hypotheses.

The final local constructor chooses a product neighborhood inside the chart
before the potential and signed datum. Its consumer is the row `a` in
`W₀ = k a`. The concrete potential `lᵀPk`, datum `lᵀσ`, common coefficient
buffers and quantitative symbol estimates remain construction obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace JanetCartan.RegularSector.Characteristic

variable {E ι : Type*} [NormedAddCommGroup E]

/-- The transported position and unchanged initial covector, with the two
times retained by `twoTimeProjection`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def twoTimeSpatialProjection (Φ : RootState E × ℝ → RootState E)
    (q : TwoTimePoint E) : E × E :=
  ((twoTimeState Φ q).2.1, q.2.2.2)

/-- The actual initial spatial label and covector from the phase chart
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def twoTimeInitialLabel (C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E))
    (q : TwoTimePoint E) : E × E := (C.symm q).2.2

/-- The signed row with a physical potential, using the same chart as the
phase. In the characteristic-kernel construction `c = lᵀPk` and `a₀ = lᵀσ`.
No positivity is imposed on `a₀`. -/
def twoTimeRowTransport (C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E))
    (c : TwoTimePoint E → ℝ) (a₀ : RootState E → ι → ℝ) : TwoTimePoint E → ι → ℝ :=
  physicalRowTransport (c ∘ C) a₀ (twoTimeInitialLabel C)

/-- The actual chart proves the inverse-flow premise needed by the signed
transport construction (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem twoTimeInitialLabel_projection
    {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hC : (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ)
    {q : TwoTimePoint E} (hq : q ∈ C.source) :
    twoTimeInitialLabel C (q.1, (q.2.1, twoTimeSpatialProjection Φ q)) = q.2.2 := by
  change (C.symm (twoTimeProjection Φ q)).2.2 = q.2.2
  rw [← hC, C.left_inv hq]

/-- On the chart target, the row is the literal exponential solution evaluated
at the actual inverse point (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem twoTimeRowTransport_eq_pullback
    {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hC : (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ)
    (c : TwoTimePoint E → ℝ) (a₀ : RootState E → ι → ℝ)
    {q : TwoTimePoint E} (hq : q ∈ C.target) :
    twoTimeRowTransport C c a₀ q = rowTransport (c ∘ C) a₀ (C.symm q) := by
  obtain ⟨ht, hs, _, _⟩ := twoTimeChart_inverse_coordinates hC hq
  simp only [twoTimeRowTransport, physicalRowTransport, twoTimeInitialLabel]
  rw [← ht, ← hs]

/-- Exact diagonal data on the same phase chart
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem twoTimeRowTransport_diagonal
    {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hC : (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ)
    (c : TwoTimePoint E → ℝ) (a₀ : RootState E → ι → ℝ)
    {w : RootState E} (hi : Φ (w, 0) = w) (hw : (w.1, w) ∈ C.source) :
    twoTimeRowTransport C c a₀ (w.1, w) = a₀ w := by
  have hp : twoTimeProjection Φ (w.1, w) = (w.1, w) := by
    simp [twoTimeProjection, twoTimeState, hi]
  have he : C.symm (w.1, w) = (w.1, w) := by
    simpa only [hC, hp] using C.left_inv hw
  simp only [twoTimeRowTransport, physicalRowTransport, twoTimeInitialLabel, he]
  exact rowTransport_diagonal _ _ _ _

/-- The source row's zero set is retained exactly, including its physical and
angular source cutoff (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem twoTimeRowTransport_eq_zero_iff
    {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hC : (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ)
    (c : TwoTimePoint E → ℝ) (a₀ : RootState E → ι → ℝ)
    {q : TwoTimePoint E} (hq : q ∈ C.target) :
    twoTimeRowTransport C c a₀ q = 0 ↔ a₀ (C.symm q).2 = 0 := by
  rw [twoTimeRowTransport_eq_pullback hC c a₀ hq, rowTransport_eq_zero_iff]

variable [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] [Fintype ι]

omit [FiniteDimensional ℝ E] in
/-- The spatial projection's physical velocity is derived from the actual
Hamilton ODE; the initial covector has zero velocity
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasDerivAt_twoTimeSpatialProjection
    {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    {q : TwoTimePoint E}
    (hd : HasDerivAt (fun u ↦ Φ (q.2, u))
      (rootHamiltonField h (twoTimeState Φ q)) (q.1 - q.2.1)) :
    HasDerivAt (fun t ↦ twoTimeSpatialProjection Φ (t, q.2))
      (-rootMomentumGradient h (twoTimeState Φ q), 0) q.1 := by
  have hs := hd.scomp q.1 ((hasDerivAt_id q.1).sub_const q.2.1)
  have hy := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt q.1
    ((ContinuousLinearMap.snd ℝ ℝ (E × E)).hasFDerivAt.comp_hasDerivAt q.1 hs)
  simpa [twoTimeSpatialProjection, twoTimeState, rootHamiltonField, Function.comp_def] using
    hy.prodMk (hasDerivAt_const q.1 q.2.2.2)

/-- Instantiate signed row transport on a product subchart of the actual
Hamilton projection. All inverse compatibility and velocity premises of
`fderiv_physicalRowTransport_along_flow` are discharged here. The potential
and row are primitive data, not a supplied transport solution
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem twoTimeRowTransport_spec
    {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E}
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    (hC : (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ)
    (hCf : ContDiffOn ℝ ∞ C C.source) (hCs : ContDiffOn ℝ ∞ C.symm C.target)
    {I : Set ℝ} {U : Set (E × E)}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U)
    (hB : I ×ˢ (I ×ˢ U) ⊆ C.source)
    (hd : ∀ q ∈ I ×ˢ (I ×ˢ U), HasDerivAt (fun u ↦ Φ (q.2, u))
      (rootHamiltonField h (twoTimeState Φ q)) (q.1 - q.2.1))
    {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    {c : TwoTimePoint E → ℝ} {a₀ : RootState E → ι → ℝ}
    (hc : ContDiffOn ℝ ∞ c C.target) (ha₀ : ContDiffOn ℝ ∞ a₀ (I ×ˢ U)) :
    let D := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
    ContDiffOn ℝ ∞ (twoTimeRowTransport C c a₀) D ∧
      ∀ q ∈ D,
        fderiv ℝ (twoTimeRowTransport C c a₀) q
          (1, (0, (-rootMomentumGradient h (twoTimeState Φ (C.symm q)), 0))) =
            -c q • twoTimeRowTransport C c a₀ q := by
  dsimp only
  let D := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
  have hD : IsOpen D := hCs.continuousOn.isOpen_inter_preimage
    C.open_target (hI.prod (hI.prod hU))
  have hcf : ContDiffOn ℝ ∞ (c ∘ C) (I ×ˢ (I ×ˢ U)) :=
    hc.comp (hCf.mono hB) (fun _ hq ↦ C.map_source (hB hq))
  have hY : ContDiffOn ℝ ∞ (twoTimeInitialLabel C) D :=
    (hCs.mono inter_subset_left).snd.snd
  have hmap : MapsTo (fun q ↦ (q.1, (q.2.1, twoTimeInitialLabel C q)))
      D (I ×ˢ (I ×ˢ U)) := by
    intro q hq
    obtain ⟨ht, hs, _, _⟩ := twoTimeChart_inverse_coordinates hC hq.1
    have hq' : (C.symm q).1 ∈ I ∧ (C.symm q).2.1 ∈ I ∧ (C.symm q).2.2 ∈ U := hq.2
    exact ⟨ht ▸ hq'.1, hs ▸ hq'.2.1, hq'.2.2⟩
  refine ⟨contDiffOn_physicalRowTransport hI hIc hU hcf ha₀ ht₀ hY hmap, ?_⟩
  intro q hq
  let w := C.symm q
  have hw : w ∈ I ×ˢ (I ×ˢ U) := hq.2
  have he : (w.1, (w.2.1, twoTimeSpatialProjection Φ w)) = q := by
    change twoTimeProjection Φ w = q
    rw [← hC]
    exact C.right_inv hq.1
  have hYΦ : ∀ u ∈ I,
      twoTimeInitialLabel C (u, (w.2.1, twoTimeSpatialProjection Φ (u, w.2))) = w.2.2 :=
    fun u hu ↦ twoTimeInitialLabel_projection hC (q := (u, w.2)) (hB ⟨hu, hw.2⟩)
  have ha := fderiv_physicalRowTransport_along_flow hI hIc hU hD hcf ha₀
    hw.2.1 hw.1 hw.2.2 hY hmap hYΦ (he.symm ▸ hq)
      (hasDerivAt_twoTimeSpatialProjection (hd w hw))
  change fderiv ℝ (twoTimeRowTransport C c a₀)
      (w.1, (w.2.1, twoTimeSpatialProjection Φ w)) _ =
    -(c (C w)) • twoTimeRowTransport C c a₀
      (w.1, (w.2.1, twoTimeSpatialProjection Φ w)) at ha
  rw [he, C.right_inv hq.1] at ha
  exact ha

omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Choose an actual product neighborhood inside the constructed chart, before
the signed data or potential. This supplies the full time segments required
by the exponential integral; openness at each isolated time would not suffice
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_twoTime_transport_box
    {C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E)}
    {z : RootState E} (hz : (z.1, z) ∈ C.source) :
    ∃ δ > (0 : ℝ),
      ball z.1 δ ×ˢ (ball z.1 δ ×ˢ ball z.2 δ) ⊆ C.source := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp C.open_source (z.1, z) hz
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  apply hsub
  simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Set.mem_prod] using hq

/-- Construct the phase chart and signed transport together from the scalar
root. The product box is chosen before the potential or initial row. Both
time eikonal identities follow from the retained phase differential, while
the physical row equation is proved on the image of that very box. No flow,
inverse or transport solution is assumed
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_localTwoTimePhase_transport
    {h : RootState E → ℝ} {D : Set (RootState E)}
    (hD : IsOpen D) (hh : ContDiffOn ℝ ∞ h D)
    (hhom : ∀ z ∈ D, ∀ᶠ a : ℝ in 𝓝 1, h (z.1, (z.2.1, a • z.2.2)) = a * h z)
    {z : RootState E} (hz : z ∈ D) :
    ∃ Φ : RootState E × ℝ → RootState E,
      ∃ C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E), ∃ δ > (0 : ℝ),
        let I := ball z.1 δ
        let U := ball z.2 δ
        let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
        IsOpen V ∧ (z.1, z) ∈ V ∧
        (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ ∧
        (∀ q ∈ C.target, twoTimeState Φ (C.symm q) ∈ D ∧
          (twoTimeState Φ (C.symm q)).1 = q.1) ∧
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target ∧
        (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) ∧
        (∀ w ∈ I ×ˢ U, (w.1, w) ∈ V ∧ twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ) ∧
        ∀ (c : TwoTimePoint E → ℝ) (a₀ : RootState E → ι → ℝ),
          ContDiffOn ℝ ∞ c C.target → ContDiffOn ℝ ∞ a₀ (I ×ˢ U) →
          ContDiffOn ℝ ∞ (twoTimeRowTransport C c a₀) V ∧
          (∀ w ∈ I ×ˢ U, twoTimeRowTransport C c a₀ (w.1, w) = a₀ w) ∧
          (∀ q ∈ V, fderiv ℝ (twoTimeRowTransport C c a₀) q
            (1, (0, (-rootMomentumGradient h (twoTimeState Φ (C.symm q)), 0))) =
              -c q • twoTimeRowTransport C c a₀ q) := by
  obtain ⟨r, _, ε, _, Φ, C, _, hi, hd, hm, _, hclock, hC, hsource, hzC, _, hCf, hCs,
    hphase, hdiff, hdiag⟩ := exists_localTwoTimeHamiltonPhase hD hh hhom hz
  obtain ⟨δ, hδ, hbox⟩ := exists_twoTime_transport_box hzC
  let I := ball z.1 δ
  let U := ball z.2 δ
  let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
  have hV : IsOpen V := hCs.continuousOn.isOpen_inter_preimage
    C.open_target (isOpen_ball.prod (isOpen_ball.prod isOpen_ball))
  have hinit (w : RootState E) (hw : w ∈ I ×ˢ U) :
      Φ (w, 0) = w ∧ (w.1, w) ∈ C.source := by
    have hs := hbox (show (w.1, w) ∈ I ×ˢ (I ×ˢ U) from ⟨hw.1, hw⟩)
    exact ⟨hi w (hsource hs).1, hs⟩
  have hdiagV (w : RootState E) (hw : w ∈ I ×ˢ U) : (w.1, w) ∈ V := by
    obtain ⟨hwi, hws⟩ := hinit w hw
    have hp : C (w.1, w) = (w.1, w) := by
      simp [hC, twoTimeProjection, twoTimeState, hwi]
    have hinv : C.symm (w.1, w) = (w.1, w) := by
      simpa only [hp] using C.left_inv hws
    refine ⟨hp ▸ C.map_source hws, ?_⟩
    change C.symm (w.1, w) ∈ I ×ˢ (I ×ˢ U)
    rw [hinv]
    exact ⟨hw.1, hw⟩
  refine ⟨Φ, C, δ, hδ, hV, hdiagV z ⟨mem_ball_self hδ, mem_ball_self hδ⟩,
    hC, ?_, hphase, hdiff, ?_, ?_⟩
  · intro q hq
    have hs := hsource (C.map_target hq)
    exact ⟨hm _ hs.1 _ hs.2,
      (hclock _ hs).trans (twoTimeChart_inverse_coordinates hC hq).1⟩
  · intro w hw
    exact ⟨hdiagV w hw, hdiag w (hsource (hinit w hw).2).1 (hinit w hw).2⟩
  · intro c a₀ hc ha₀
    have hder (q : TwoTimePoint E) (hq : q ∈ I ×ˢ (I ×ˢ U)) :=
      hd q.2 (hsource (hbox hq)).1 (q.1 - q.2.1) (hsource (hbox hq)).2
    have hspec := twoTimeRowTransport_spec hC hCf hCs isOpen_ball
      (convex_ball z.1 δ).ordConnected isOpen_ball hbox hder (mem_ball_self hδ) hc ha₀
    refine ⟨hspec.1, ?_, hspec.2⟩
    intro w hw
    exact twoTimeRowTransport_diagonal hC c a₀ (hinit w hw).1 (hinit w hw).2

end JanetCartan.RegularSector.Characteristic
