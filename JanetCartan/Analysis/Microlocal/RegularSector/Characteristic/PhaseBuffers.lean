module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.TwoTimePhase
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.Basic
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.PhaseLocality

/-!
# Buffered mixed geometry of the constructed two-time phase

The diagonal data of the actual phase imply that its spatial mixed matrix is
exactly the identity at equal times. Joint smoothness then supplies an actual
closed buffer on which that matrix stays within one half of the identity.
These are the primitive spatial inputs of the elapsed-time graph geometry in
`paper-v2.tex`, `app:ch_regular_base:lem:retarded-kernel`.

The buffers here belong to one constructed coefficient array. Uniformity over
a coefficient neighborhood and conic extension remain separate obligations;
no symbol bound or operator estimate is inferred from local smoothness.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic
open FourierIntegral
variable {d : ℕ}

/-- The constructed phase in the four-argument convention of the elapsed-time
kernel. Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
def curriedTwoTimePhase
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))) :
    EvolutionIntegral.TwoTimePhase d :=
  fun t s y η ↦ twoTimePhase C (t, (s, (y, η)))

/-- The literal spatial mixed matrix of the constructed phase, with both times
retained. Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
def twoTimePhaseMixed
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (q : TwoTimePoint (Euclidean d)) : Matrix (Fin d) (Fin d) ℝ :=
  mixedPhaseMatrix (curriedTwoTimePhase C q.1 q.2.1) q.2.2.1 q.2.2.2

private theorem mixedPhaseMatrix_inner :
    mixedPhaseMatrix (fun y η : Euclidean d ↦ ⟪y, η⟫_ℝ) = fun _ _ ↦ 1 := by
  funext y η
  ext i j
  simp only [mixedPhaseMatrix, partialDeriv]
  have hx (ζ : Euclidean d) : fderiv ℝ (fun y : Euclidean d ↦ ⟪y, ζ⟫_ℝ) y = innerSL ℝ ζ := by
    simpa only [coe_innerSL_apply, real_inner_comm] using (innerSL ℝ ζ).fderiv (x := y)
  simp_rw [hx]
  have he : (fun ζ : Euclidean d ↦ (innerSL ℝ ζ) (EuclideanSpace.single i 1)) =
      innerSL ℝ (EuclideanSpace.single i 1) := by
    funext ζ
    simp only [innerSL_apply_apply, real_inner_comm]
  rw [he, (innerSL ℝ (EuclideanSpace.single i 1)).fderiv]
  simp [innerSL_apply_apply, EuclideanSpace.inner_single_left, EuclideanSpace.single,
    Matrix.one_apply]

/-- Smoothness in both times and spatial variables of the actual mixed matrix.
The proof differentiates the original phase, not a separately chosen matrix.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem contDiffAt_twoTimePhaseMixed
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (p : TwoTimePoint (Euclidean d)) (hF : ContDiffAt ℝ ∞ (twoTimePhase C) p) :
    ContDiffAt ℝ ∞ (twoTimePhaseMixed C) p := by
  let pack : (Fin d → Fin d → ℝ) →L[ℝ] Matrix (Fin d) (Fin d) ℝ :=
    { LinearMap.id with cont := continuous_id }
  apply pack.contDiff.contDiffAt.comp p
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hx : ContDiffAt ℝ ∞ (fun q : TwoTimePoint (Euclidean d) ↦
      partialDeriv (fun y ↦ twoTimePhase C (q.1, (q.2.1, (y, q.2.2.2)))) q.2.2.1 i) p := by
    have h := hF.comp (p, p.2.2.1)
      (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.fst.prodMk
        (contDiffAt_snd.prodMk contDiffAt_fst.snd.snd.snd)))
    exact (h.fderiv contDiffAt_snd.snd.fst (by simp)).clm_apply contDiffAt_const
  have h := hx.comp (p, p.2.2.2)
    (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.fst.prodMk
      (contDiffAt_fst.snd.snd.fst.prodMk contDiffAt_snd)))
  exact (h.fderiv contDiffAt_snd.snd.snd (by simp)).clm_apply contDiffAt_const

/-- The exact diagonal phase data give the identity mixed matrix. The data are
supplied by `exists_physical_pencil_kernel` for its same chart.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem twoTimePhaseMixed_diagonal
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (t : ℝ) {U : Set (Euclidean d × Euclidean d)} (hU : IsOpen U)
    (hdiag : ∀ p ∈ U, twoTimePhase C (t, (t, p)) = ⟪p.1, p.2⟫_ℝ)
    {p : Euclidean d × Euclidean d} (hp : p ∈ U) :
    twoTimePhaseMixed C (t, (t, p)) = 1 := by
  have he : Function.uncurry (curriedTwoTimePhase C t t) =ᶠ[𝓝 p]
      Function.uncurry (fun y η : Euclidean d ↦ ⟪y, η⟫_ℝ) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hp) hdiag
  change mixedPhaseMatrix (curriedTwoTimePhase C t t) p.1 p.2 = 1
  rw [SupportedSobolev.mixedPhaseMatrix_eq_of_eventuallyEq he, mixedPhaseMatrix_inner]

/-- Choose a positive closed margin and the spatial half-gap from the actual
phase's smoothness and diagonal identity. The prescribed open set retains the
same transport chart, so the margin can be chosen before the source mask.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem exists_twoTimePhase_mixed_buffer
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {z : RootState (Euclidean d)} {V : Set (TwoTimePoint (Euclidean d))}
    (hV : IsOpen V) (hz : (z.1, z) ∈ V) (hVC : V ⊆ C.target)
    (hphase : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    {U : Set (Euclidean d × Euclidean d)} (hU : IsOpen U) (hzU : z.2 ∈ U)
    (hdiag : ∀ p ∈ U, twoTimePhase C (z.1, (z.1, p)) = ⟪p.1, p.2⟫_ℝ) :
    ∃ ε > (0 : ℝ), closedBall (z.1, z) (2 * ε) ⊆ V ∧
      ∀ q ∈ closedBall (z.1, z) (2 * ε), ‖twoTimePhaseMixed C q - 1‖ ≤ 1 / 2 := by
  have hs := contDiffAt_twoTimePhaseMixed C (z.1, z)
    (hphase.contDiffAt (C.open_target.mem_nhds (hVC hz)))
  have hid := twoTimePhaseMixed_diagonal C z.1 hU hdiag hzU
  have hn : ∀ᶠ q in 𝓝 (z.1, z), ‖twoTimePhaseMixed C q - 1‖ < (1 / 2 : ℝ) :=
    (hs.continuousAt.sub continuousAt_const).norm.eventually_lt_const (by change ‖twoTimePhaseMixed C (z.1, z) - 1‖ < (1 / 2 : ℝ); rw [hid]; norm_num)
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hV.mem_nhds hz) hn)
  refine ⟨a / 4, by positivity, ?_, ?_⟩
  · intro q hq
    exact (hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hq) (show 2 * (a / 4) < a by linarith))).1
  · intro q hq
    exact (hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hq) (show 2 * (a / 4) < a by linarith))).2.le

end JanetCartan.RegularSector.Characteristic
