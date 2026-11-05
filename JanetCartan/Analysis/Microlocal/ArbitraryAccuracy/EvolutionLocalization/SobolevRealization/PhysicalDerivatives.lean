module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization.CompletedDerivatives
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization.Coordinates
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.IntegerDerivatives

/-!
# Completed jets are actual distributional derivatives

For the Fourier comparison in `app:ch_regular:eq:chain-tail`, the derivatives
constructed from classical jets are identified in tempered distributions.
The dense test calculation is the ordinary chain rule for the fixed map `J`.
-/

@[expose] public noncomputable section

open MeasureTheory Set LineDeriv
open scoped ContDiff ENNReal SchwartzMap LineDeriv

namespace JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization

open RetardedSobolev.Spaces FourierIntegral FiniteChain.Graph.KernelLimits Pseudodifferential

variable {d : ℕ}
variable (J : (ℝ × (Fin d → ℝ)) ≃L[ℝ] Euclidean (d + 1))

/-- The actual physical scalar test field as a Schwartz map, for the
Fourier comparison in `app:ch_regular:eq:chain-tail`. -/
def physicalSchwartzTest (f : Test d) : 𝓢(Euclidean (d + 1), ℂ) :=
  (f.property.2.comp_homeomorph J.symm.toHomeomorph).toSchwartzMap
    (f.property.1.comp J.symm.contDiff)

/-- Differentiating the physical test field is the usual chain rule, with
exactly the fixed coordinates used in `app:ch_regular:eq:chain-tail`. -/
theorem physicalSchwartzTest_directionalTest (v : ℝ × (Fin d → ℝ)) (f : Test d) :
    physicalSchwartzTest J (directionalTest v f) = ∂_{J v} (physicalSchwartzTest J f) := by
  ext y
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ f.val (J.symm y) v = fderiv ℝ (f.val ∘ J.symm) y (J v)
  rw [J.symm.comp_right_fderiv, ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

variable (hJ : MeasurePreserving (graphInputCoordinates J) volume volume)

/-- The zeroth-jet test action is precisely the L² class of the physical
Schwartz test (`app:ch_regular:eq:chain-tail`). -/
theorem physicalZeroJet_ofTest_eq_schwartz (m : ℕ) (f : Test d) :
    physicalZeroJet J hJ m (ofTest m volume f) = (physicalSchwartzTest J f).toLp 2 volume := by
  apply Lp.ext
  exact (physicalZeroJet_ofTest_ae J hJ m f).trans
    ((physicalSchwartzTest J f).coeFn_toLp 2 volume).symm

/-- Budget lowering does not change the physical function represented by the
completed jets (`app:ch_regular:eq:chain-tail`). -/
theorem physicalZeroJet_lowerOrder (m : ℕ)
    (u : Sobolev (m + 1) (volume : Measure ((Fin d → ℝ) × ℝ))) :
    physicalZeroJet J hJ m (lowerOrder m u) = physicalZeroJet J hJ (m + 1) u := by
  have he : (fun u => physicalZeroJet J hJ m (lowerOrder m u)) =
      fun u => physicalZeroJet J hJ (m + 1) u := by
    apply (denseRange_ofTest (m + 1) volume).equalizer
      ((physicalZeroJet J hJ m).continuous.comp (lowerOrder m).continuous)
      (physicalZeroJet J hJ (m + 1)).continuous
    funext f
    simp only [Function.comp_apply, lowerOrder_ofTest]
    exact (physicalZeroJet_ofTest_eq_schwartz J hJ m f).trans
      (physicalZeroJet_ofTest_eq_schwartz J hJ (m + 1) f).symm
  exact congrFun he u

/-- Every completed directional derivative is the actual distributional
derivative of the physical zeroth jet. No derivative identity is assumed
(`app:ch_regular:eq:chain-tail`). -/
theorem physicalZeroJet_completedDirectionalDerivative (m : ℕ)
    (v : ℝ × (Fin d → ℝ))
    (u : Sobolev (m + 1) (volume : Measure ((Fin d → ℝ) × ℝ))) :
    ∂_{J v} (physicalZeroJet J hJ (m + 1) u : 𝓢'(Euclidean (d + 1), ℂ)) =
      (physicalZeroJet J hJ m (completedDirectionalDerivative m v u) :
        𝓢'(Euclidean (d + 1), ℂ)) := by
  let F := (lineDerivOpCLM ℂ 𝓢'(Euclidean (d + 1), ℂ) (J v)).comp
    ((Lp.toTemperedDistributionCLM ℂ volume 2).comp (physicalZeroJet J hJ (m + 1)))
  let G := (Lp.toTemperedDistributionCLM ℂ volume 2).comp
    ((physicalZeroJet J hJ m).comp (completedDirectionalDerivative m v))
  have he : (F : _ → 𝓢'(Euclidean (d + 1), ℂ)) = G := by
    apply (denseRange_ofTest (m + 1) volume).equalizer F.continuous G.continuous
    funext f
    change ∂_{J v} (physicalZeroJet J hJ (m + 1) (ofTest (m + 1) volume f) :
        𝓢'(Euclidean (d + 1), ℂ)) =
      (physicalZeroJet J hJ m
        (completedDirectionalDerivative m v (ofTest (m + 1) volume f)) :
        𝓢'(Euclidean (d + 1), ℂ))
    rw [completedDirectionalDerivative_ofTest, physicalZeroJet_ofTest_eq_schwartz,
      physicalZeroJet_ofTest_eq_schwartz, Lp.toTemperedDistribution_toLp_eq,
      Lp.toTemperedDistribution_toLp_eq, physicalSchwartzTest_directionalTest,
      TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq]
  exact congrFun he u

/-- Euclidean coordinate derivatives are supplied by the concrete completed
jet construction, ready for the existing Fourier gain-one theorem
(`app:ch_regular:eq:chain-tail`). -/
theorem physicalZeroJet_hasCoordinateDerivative (m : ℕ) (i : Fin (d + 1))
    (u : Sobolev (m + 1) (volume : Measure ((Fin d → ℝ) × ℝ))) :
    HasEuclideanL2CoordinateDerivative i (physicalZeroJet J hJ (m + 1) u)
      (physicalZeroJet J hJ m (completedDirectionalDerivative m
        (J.symm (EuclideanSpace.basisFun (Fin (d + 1)) ℝ i)) u)) := by
  simpa only [HasEuclideanL2CoordinateDerivative, euclideanCoordinateDerivative,
    ContinuousLinearEquiv.apply_symm_apply] using
    physicalZeroJet_completedDirectionalDerivative J hJ m
      (J.symm (EuclideanSpace.basisFun (Fin (d + 1)) ℝ i)) u

end JanetCartan.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization
