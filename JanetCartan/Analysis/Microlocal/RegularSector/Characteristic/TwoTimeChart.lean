module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.TwoTimeFlow
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# The inverse projection of the two-time characteristic flow

For `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`, retain
both times and the initial covector in the spatial projection. Its diagonal
differential is an explicit invertible shear. The inverse function theorem
therefore constructs a smooth chart on the same actual flow from
`exists_twoTimeHamiltonFlow`; no projection gap or inverse is assumed.

This is local geometry for the subsequent phase and signed row transport.
Uniform buffers over the coefficient class, the phase differential, and
symbol estimates are further obligations of the sector construction.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.RegularSector.Characteristic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Spatial projection retaining output time, source time and initial
covector (`app:ch_regular_base:lem:characteristic-kernel`). -/
def twoTimeProjection (Φ : RootState E × ℝ → RootState E) (q : TwoTimePoint E) :
    TwoTimePoint E := (q.1, (q.2.1, ((twoTimeState Φ q).2.1, q.2.2.2)))

/-- The diagonal projection shear `(δt,δs,δy,δη) ↦
(δt,δs,δy+(δt-δs)v,δη)`
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def twoTimeProjectionLinear (v : E) : TwoTimePoint E →L[ℝ] TwoTimePoint E :=
  let t := ContinuousLinearMap.fst ℝ ℝ (RootState E)
  let s := (ContinuousLinearMap.fst ℝ ℝ (E × E)).comp
    (ContinuousLinearMap.snd ℝ ℝ (RootState E))
  let yp := (ContinuousLinearMap.snd ℝ ℝ (E × E)).comp
    (ContinuousLinearMap.snd ℝ ℝ (RootState E))
  t.prod (s.prod (((ContinuousLinearMap.fst ℝ E E).comp yp +
    (t - s).smulRight v).prod ((ContinuousLinearMap.snd ℝ E E).comp yp)))

omit [CompleteSpace E] in
/-- Explicit evaluation of the projection shear
(`app:ch_regular_base:lem:characteristic-kernel`). -/
@[simp] theorem twoTimeProjectionLinear_apply (v : E) (w : TwoTimePoint E) :
    twoTimeProjectionLinear v w =
      (w.1, (w.2.1, (w.2.2.1 + (w.1 - w.2.1) • v, w.2.2.2))) := rfl

/-- The inverse shear subtracts `(δt-δs)v`; in particular no determinant
gap is assumed at the time diagonal
(`app:ch_regular_base:lem:characteristic-kernel`). -/
def twoTimeProjectionEquiv (v : E) : TwoTimePoint E ≃L[ℝ] TwoTimePoint E where
  toLinearEquiv := {
    toLinearMap := (twoTimeProjectionLinear v).toLinearMap
    invFun := twoTimeProjectionLinear (-v)
    left_inv := by intro w; simp [twoTimeProjectionLinear_apply]
    right_inv := by intro w; simp [twoTimeProjectionLinear_apply] }
  continuous_toFun := (twoTimeProjectionLinear v).continuous
  continuous_invFun := (twoTimeProjectionLinear (-v)).continuous

/-- The actual projection derivative is the invertible shear with velocity
`-h_η`, derived from the Hamilton IVP
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem hasFDerivAt_twoTimeProjection_diagonal
    {h : RootState E → ℝ} {Φ : RootState E × ℝ → RootState E} {z : RootState E}
    (hΦ : DifferentiableAt ℝ Φ (z, 0))
    (hd : HasDerivAt (fun u ↦ Φ (z, u)) (rootHamiltonField h z) 0)
    (hJ : ODE.flowInitialDerivative Φ z 0 = ContinuousLinearMap.id ℝ _) :
    HasFDerivAt (twoTimeProjection Φ)
      (twoTimeProjectionEquiv (-rootMomentumGradient h z)).toContinuousLinearMap (z.1, z) := by
  have hs := hasFDerivAt_twoTimeState_diagonal hΦ hd hJ
  have ht := (ContinuousLinearMap.fst ℝ ℝ (RootState E)).hasFDerivAt (x := (z.1, z))
  have hi := (ContinuousLinearMap.snd ℝ ℝ (RootState E)).hasFDerivAt (x := (z.1, z))
  convert! ht.prodMk (hi.fst.prodMk (hs.snd.fst.prodMk hi.snd.snd)) using 1

/-- Construct a smooth inverse chart for the actual two-time flow near its
time diagonal. The source is contained in the same ODE domain. The hypotheses
are the initial-data, smoothness and ODE conclusions of
`exists_twoTimeHamiltonFlow`, not assumed inverse-chart data
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_twoTimeProjectionChart {h : RootState E → ℝ}
    {Φ : RootState E × ℝ → RootState E} {z : RootState E} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε)
    (hΦ : ContDiffOn ℝ ∞ Φ (ball z r ×ˢ Ioo (-ε) ε))
    (hi : Φ (z, 0) = z)
    (hd : HasDerivAt (fun u ↦ Φ (z, u)) (rootHamiltonField h z) 0)
    (hJ : ODE.flowInitialDerivative Φ z 0 = ContinuousLinearMap.id ℝ _) :
    ∃ C : OpenPartialHomeomorph (TwoTimePoint E) (TwoTimePoint E),
      (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ ∧
      C.source ⊆ twoTimeDomain z r ε ∧ (z.1, z) ∈ C.source ∧ (z.1, z) ∈ C.target ∧
      ContDiffOn ℝ ∞ C C.source ∧ ContDiffOn ℝ ∞ C.symm C.target := by
  let D := twoTimeDomain z r ε
  have hD : IsOpen D := isOpen_twoTimeDomain z r ε
  have hz : (z.1, z) ∈ D := diagonal_mem_twoTimeDomain hε (mem_ball_self hr)
  have hstate : ContDiffOn ℝ ∞ (twoTimeState Φ) D :=
    hΦ.comp (contDiffOn_snd.prodMk (contDiffOn_fst.sub contDiffOn_snd.fst))
      (fun _ hq ↦ hq)
  have hp : ContDiffOn ℝ ∞ (twoTimeProjection Φ) D :=
    contDiffOn_fst.prodMk (contDiffOn_snd.fst.prodMk
      (hstate.snd.fst.prodMk contDiffOn_snd.snd.snd))
  have hbase : twoTimeProjection Φ (z.1, z) = (z.1, z) := by
    simp [twoTimeProjection, twoTimeState, hi]
  have hΦ₀ : DifferentiableAt ℝ Φ (z, 0) :=
    (hΦ.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds
      ⟨mem_ball_self hr, by constructor <;> linarith⟩)).differentiableAt (by simp)
  let A := twoTimeProjectionEquiv (-rootMomentumGradient h z)
  have hA : HasFDerivAt (twoTimeProjection Φ) A.toContinuousLinearMap (z.1, z) :=
    hasFDerivAt_twoTimeProjection_diagonal hΦ₀ hd hJ
  have hp₀ := hp.contDiffAt (hD.mem_nhds hz)
  let e := hp₀.toOpenPartialHomeomorph (twoTimeProjection Φ) hA (by simp)
  have he : (e : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ := rfl
  have hinv : ∀ᶠ w in 𝓝 (z.1, z), ∃ B : TwoTimePoint E ≃L[ℝ] TwoTimePoint E,
      B.toContinuousLinearMap = fderiv ℝ (twoTimeProjection Φ) w := by
    have hN := A.nhds
    rw [← hA.fderiv] at hN
    exact (hp₀.continuousAt_fderiv (by simp)).tendsto.eventually hN
  obtain ⟨V, hVsub, hV, hzV⟩ := _root_.eventually_nhds_iff.mp (hinv.and (hD.mem_nhds hz))
  let C := e.restrOpen V hV
  have hC : (C : TwoTimePoint E → TwoTimePoint E) = twoTimeProjection Φ := rfl
  have hsub : C.source ⊆ D := fun _ hw ↦ (hVsub _ hw.2).2
  have hzC : (z.1, z) ∈ C.source :=
    ⟨hp₀.mem_toOpenPartialHomeomorph_source hA (by simp), hzV⟩
  refine ⟨C, hC, hsub, hzC, ?_, ?_, ?_⟩
  · simpa only [hC, hbase] using C.map_source hzC
  · exact hp.mono hsub
  · intro w hw
    have hx := C.map_target hw
    obtain ⟨B, hB⟩ := (hVsub _ hx.2).1
    have hf := hp.contDiffAt (hD.mem_nhds (hsub hx))
    apply ContDiffAt.contDiffWithinAt (C.contDiffAt_symm hw (f₀' := B) ?_ hf)
    rw [hC, hB]
    exact (hf.differentiableAt (by simp)).hasFDerivAt

end JanetCartan.RegularSector.Characteristic
