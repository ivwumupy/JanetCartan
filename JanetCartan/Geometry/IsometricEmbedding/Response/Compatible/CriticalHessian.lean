module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.CriticalPoint
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.Basic

/-!
# The literal carrier Hessian and the stationary Jacobian

Connect the ordinary-product stationary equations to the Hilbert-product
variables used by `ResponseTransfer.DirectEvolution`. The gradient and Hessian
are those of its literal `elapsedCarrierPhase`. This is the geometric input
to the averaged-Hessian calculation in `app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.CompatibleResponse
open ArbitraryAccuracy RegularSector.Characteristic
open ResponseTransfer.DirectEvolution
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

variable {d : ℕ}

/-- The actual Hilbert gradient is the two stationary equations, with the
source and covector coordinates unchanged. In particular there is no implicit
identification of the maximum product norm and the Hilbert product norm
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem gradient_elapsedCarrierPhase
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {φ : Euclidean (d + 1) → Euclidean 3 → ℝ}
    {r : ℝ} {x : Euclidean (d + 1)} {c : Euclidean 3} {w : CarrierVariables (d + 1)}
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint r x w.snd))
        (elapsedChartPoint r x w.snd))
    (hφ : DifferentiableAt ℝ (fun z ↦ φ z c) w.fst) :
    gradient (elapsedCarrierPhase (chartPhase C) r φ (x, c)) w =
      WithLp.toLp 2 (elapsedStationarySystem C φ ((r, (x, c)), w.ofLp)) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ (Euclidean (d + 1)) (Euclidean (d + 1))
  have hd := (hasFDerivAt_elapsedModulatedPhase hphase hφ).comp w e.hasFDerivAt
  have hg : HasGradientAt (elapsedCarrierPhase (chartPhase C) r φ (x, c))
      (WithLp.toLp 2 (elapsedStationarySystem C φ ((r, (x, c)), w.ofLp))) w := by
    convert! hd using 1
  exact hg.gradient

/-- Differentiate the same Hilbert gradient: its Hessian is the stationary
Jacobian conjugated by the explicit product equivalence. The full two-time
phase differential and actual primary-gradient smoothness are the inputs
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem fderiv_gradient_elapsedCarrierPhase
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hphase : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hs : ContDiffOn ℝ ∞ C.symm C.target)
    {φ : Euclidean (d + 1) → Euclidean 3 → ℝ}
    {Ω : Set (Euclidean (d + 1) × Euclidean 3)} (hΩ : IsOpen Ω)
    (hφ : ContDiffOn ℝ ∞ (fun q ↦ φ q.1 q.2) Ω)
    (hg : ContDiffOn ℝ ∞ (fun q : Euclidean (d + 1) × Euclidean 3 ↦
      gradient (fun z ↦ φ z q.2) q.1) Ω)
    {r : ℝ} {x : Euclidean (d + 1)} {c : Euclidean 3} {w : CarrierVariables (d + 1)}
    (hw : (w.fst, c) ∈ Ω) (hq : elapsedChartPoint r x w.snd ∈ C.target) :
    let e := WithLp.prodContinuousLinearEquiv 2 ℝ (Euclidean (d + 1)) (Euclidean (d + 1))
    fderiv ℝ (gradient (elapsedCarrierPhase (chartPhase C) r φ (x, c))) w =
      e.symm.toContinuousLinearMap ∘L
        (fderiv ℝ (elapsedStationarySystem C φ) ((r, (x, c)), w.ofLp) ∘L
          ContinuousLinearMap.inr ℝ (ℝ × (Euclidean (d + 1) × Euclidean 3))
            (Euclidean (d + 1) × Euclidean (d + 1))) ∘L e.toContinuousLinearMap := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ (Euclidean (d + 1)) (Euclidean (d + 1))
  have hf := (contDiffAt_elapsedStationarySystem
    (hs.contDiffAt (C.open_target.mem_nhds hq))
    (hg.contDiffAt (hΩ.mem_nhds hw))).differentiableAt (by simp)
  have hd := e.symm.hasFDerivAt.comp w (hf.hasFDerivAt.comp w
    ((hasFDerivAt_const (𝕜 := ℝ) (r, (x, c)) w).prodMk e.hasFDerivAt))
  have he : gradient (elapsedCarrierPhase (chartPhase C) r φ (x, c)) =ᶠ[𝓝 w]
      (fun v ↦ e.symm (elapsedStationarySystem C φ ((r, (x, c)), e v))) := by
    have hp : ContinuousAt (fun v : CarrierVariables (d + 1) ↦ (v.fst, c)) w := by fun_prop
    have hc : ContinuousAt (fun v : CarrierVariables (d + 1) ↦
        elapsedChartPoint r x v.snd) w := by
      exact continuousAt_const.prodMk (continuousAt_const.prodMk
        (continuousAt_const.prodMk (spatialPartCLM.continuous.continuousAt.comp
          (WithLp.continuous_snd 2 (Euclidean (d + 1)) (Euclidean (d + 1))).continuousAt)))
    filter_upwards [hp.preimage_mem_nhds (hΩ.mem_nhds hw),
      hc.preimage_mem_nhds (C.open_target.mem_nhds hq)] with v hv hcv
    exact gradient_elapsedCarrierPhase (hphase _ hcv)
      (((hφ.contDiffAt (hΩ.mem_nhds hv)).comp v.fst
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
  have heq := (hd.congr_of_eventuallyEq he).fderiv
  convert! heq using 1

/-- The invertibility constructed from the diagonal stationary system is
invertibility of the literal Hilbert Hessian used by the envelope consumer.
The parent instantiates the displayed Jacobian premise with
`exists_elapsedStationary_branch` (`app:ch_response:lem:energy-carrier-jets`). -/
theorem isUnit_fderiv_gradient_elapsedCarrierPhase
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hphase : ∀ q ∈ C.target,
      HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q)
    (hs : ContDiffOn ℝ ∞ C.symm C.target)
    {φ : Euclidean (d + 1) → Euclidean 3 → ℝ}
    {Ω : Set (Euclidean (d + 1) × Euclidean 3)} (hΩ : IsOpen Ω)
    (hφ : ContDiffOn ℝ ∞ (fun q ↦ φ q.1 q.2) Ω)
    (hg : ContDiffOn ℝ ∞ (fun q : Euclidean (d + 1) × Euclidean 3 ↦
      gradient (fun z ↦ φ z q.2) q.1) Ω)
    {r : ℝ} {x : Euclidean (d + 1)} {c : Euclidean 3} {w : CarrierVariables (d + 1)}
    (hw : (w.fst, c) ∈ Ω) (hq : elapsedChartPoint r x w.snd ∈ C.target)
    (hJ : (fderiv ℝ (elapsedStationarySystem C φ) ((r, (x, c)), w.ofLp) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × (Euclidean (d + 1) × Euclidean 3))
        (Euclidean (d + 1) × Euclidean (d + 1))).IsInvertible) :
    IsUnit (fderiv ℝ (gradient (elapsedCarrierPhase (chartPhase C) r φ (x, c))) w) := by
  rw [fderiv_gradient_elapsedCarrierPhase hphase hs hΩ hφ hg hw hq]
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ (Euclidean (d + 1)) (Euclidean (d + 1))
  obtain ⟨A, hA⟩ := hJ
  rw [← hA]
  exact ((e.trans A).trans e.symm).toUnit.isUnit

/-- Joint smoothness of the literal phase, including elapsed time and all
primary parameters, from the SAME smooth two-time chart and primary phase.
This supplies the continuity input for the local averaged-Hessian gap
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem contDiffAt_joint_elapsedCarrierPhase
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    {φ : Euclidean (d + 1) → Euclidean 3 → ℝ}
    {r : ℝ} {x : Euclidean (d + 1)} {c : Euclidean 3} {w : CarrierVariables (d + 1)}
    (hC : ContDiffAt ℝ ∞ (twoTimePhase C) (elapsedChartPoint r x w.snd))
    (hsrc : ContDiffAt ℝ ∞ (fun q : Euclidean (d + 1) × Euclidean 3 ↦ φ q.1 q.2) (w.fst, c))
    (hout : ContDiffAt ℝ ∞ (fun q : Euclidean (d + 1) × Euclidean 3 ↦ φ q.1 q.2) (x, c)) :
    ContDiffAt ℝ ∞
      (fun v : (ℝ × (Euclidean (d + 1) × Euclidean 3)) × CarrierVariables (d + 1) ↦
        elapsedCarrierPhase (chartPhase C) v.1.1 φ v.1.2 v.2) ((r, (x, c)), w) := by
  let v := ((r, (x, c)), w)
  have hz : ContDiffAt ℝ ∞ (fun v : (ℝ × (Euclidean (d + 1) × Euclidean 3)) ×
      CarrierVariables (d + 1) ↦ v.2.fst) v :=
    (WithLp.fstL 2 ℝ (Euclidean (d + 1)) (Euclidean (d + 1))).contDiff.contDiffAt.comp v contDiffAt_snd
  have hθ : ContDiffAt ℝ ∞ (fun v : (ℝ × (Euclidean (d + 1) × Euclidean 3)) ×
      CarrierVariables (d + 1) ↦ v.2.snd) v :=
    (WithLp.sndL 2 ℝ (Euclidean (d + 1)) (Euclidean (d + 1))).contDiff.contDiffAt.comp v contDiffAt_snd
  have ht := ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff (n := ∞)).contDiffAt.comp
    v contDiffAt_fst.snd.fst
  have hτ := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).contDiff.contDiffAt.comp v hθ
  have hc := hC.comp v (ht.prodMk ((ht.sub contDiffAt_fst.fst).prodMk
    ((spatialPartCLM.contDiff.contDiffAt.comp v contDiffAt_fst.snd.fst).prodMk
      (spatialPartCLM.contDiff.contDiffAt.comp v hθ))))
  exact ((((ht.sub contDiffAt_fst.fst).mul hτ).add hc).sub (hz.inner ℝ hθ)).add
    (hsrc.comp v (hz.prodMk contDiffAt_fst.snd.snd)) |>.sub
      (hout.comp v contDiffAt_fst.snd)

end JanetCartan.CompatibleResponse
