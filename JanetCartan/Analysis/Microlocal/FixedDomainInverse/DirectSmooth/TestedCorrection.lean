module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.DirectOperators
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.RealCompression
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.SectorEquations

/-!
# The tested physical equation for the actual corrected source

The distributional form of `app:ch_regular:eq:exact-physical`, before smooth
realization. The original finite solver's tested equation and the fixed
Neumann inverse's local residual equation concern the same source. Their
combination retains the entire paired angular source minus the identity.

The inputs are produced by `exists_finite_direct_fixed_inverse`: its real
physical tested equation and its supported corrected-source equation. This
relative deduction does not construct those operators or their estimates.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set MeasureTheory Filter
open scoped ContDiff JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse

open LocalSobolev SmallSupport RegularSector.Realization
open RegularSector.FiniteAssembly
open CharacteristicTransport.CompleteResidual
open ArbitraryAccuracy.ResidualLocalization

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "CF" => EuclideanSpace ℂ (Fin q)
local notation "RF" => EuclideanSpace ℝ (Fin q)
local notation "H" => Lp CF 2 (volume : Measure E)
local notation "RH" => Lp RF 2 (volume : Measure E)

/-- The right side of the original physical equation equals the exact
corrected source on the fixed core, for the same L² class
(`app:ch_regular:eq:exact-physical`). The primitive input is the local residual
equation returned by `exists_finite_direct_fixed_inverse`. This a.e. identity
is also used to identify the smooth right-side representative without testing. -/
theorem realPair_correctedSource_right_ae
    {W U V : Set E} (hW : MeasurableSet W) (hV : MeasurableSet V)
    (hVU : V ⊆ U) (hVW : V ⊆ W)
    (source residual : H →L[ℂ] H) (h z : LocalL2 W RF)
    (heq : ∀ᵐ y ∂volume.restrict V,
      z y + localRealCompression hW U
        (physicalPairedSectorSum {()} (fun _ : Unit ↦ residual)) z y = h y) :
    realCompression (physicalPairedSectorSum {()}
      (fun _ : Unit ↦ source + residual)) (zeroExtend hW z) =ᵐ[volume.restrict V]
      (zeroExtend hW h +
        realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦ source))
          (zeroExtend hW z) - zeroExtend hW z : RH) := by
  let z₀ : RH := zeroExtend hW z
  let h₀ : RH := zeroExtend hW h
  let src : RH := realCompression
    (physicalPairedSectorSum {()} (fun _ : Unit ↦ source)) z₀
  let res : RH := realCompression
    (physicalPairedSectorSum {()} (fun _ : Unit ↦ residual)) z₀
  have hsum : realCompression (physicalPairedSectorSum {()}
      (fun _ : Unit ↦ source + residual)) z₀ = src + res := by
    rw [physicalPairedSectorSum_add]
    change (l2RealPart volume)
      (physicalPairedSectorSum {()} (fun _ : Unit ↦ source)
        (l2ComplexInclusion volume z₀) +
       physicalPairedSectorSum {()} (fun _ : Unit ↦ residual)
        (l2ComplexInclusion volume z₀)) = _
    exact map_add (l2RealPart volume) _ _
  rw [hsum]
  filter_upwards [heq,
    ae_restrict_of_ae_restrict_of_subset hVU
      (localRealCompression_coeFn hW U
        (physicalPairedSectorSum {()} (fun _ : Unit ↦ residual)) z),
    ae_restrict_of_ae (zeroExtend_coeFn hW z),
    ae_restrict_of_ae (zeroExtend_coeFn hW h),
    ae_restrict_of_ae (Lp.coeFn_add src res),
    ae_restrict_of_ae (Lp.coeFn_sub (h₀ + src) z₀),
    ae_restrict_of_ae (Lp.coeFn_add h₀ src),
    ae_restrict_mem hV] with y hy hres hz hh hadd hsub hadd' hyV
  simp only [Pi.add_apply, Pi.sub_apply] at hadd hsub hadd'
  change z₀ y = _ at hz
  change h₀ y = _ at hh
  rw [hadd, hsub, hadd', hz, hh]
  simp only [indicator_of_mem (hVW hyV)]
  change _ + res y = _
  rw [← hres, ← hy]
  abel

/-- The original tested physical equation and the same corrected source's
residual equation imply the tested exact correction, with the full angular
discrepancy `AΓ z - z` (`app:ch_regular:eq:exact-physical`). The finite direct
constructor supplies `htest`; its fixed Neumann inverse supplies `heq`. The
core is allowed to be smaller than the original measurement domain. -/
theorem realPair_correctedSource_test
    {W U V : Set E} (hW : MeasurableSet W) (hV : MeasurableSet V)
    (hVU : V ⊆ U) (hVW : V ⊆ W)
    (A : E → Fin (d + 1) → Matrix (Fin q) (Fin q) ℝ)
    (B : E → Matrix (Fin q) (Fin q) ℝ)
    (S source residual : H →L[ℂ] H)
    (htest : ∀ (u : RH) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∀ j,
      physicalTestAction A B
        (fun y ↦ (l2ComplexInclusion volume
          (realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦ S)) u) y).ofLp)
        φ j = ∫ y, φ y • l2ComplexInclusion volume
          (realCompression (physicalPairedSectorSum {()}
            (fun _ : Unit ↦ source + residual)) u) y j)
    (h z : LocalL2 W RF)
    (heq : ∀ᵐ y ∂volume.restrict V,
      z y + localRealCompression hW U
        (physicalPairedSectorSum {()} (fun _ : Unit ↦ residual)) z y = h y) :
    ∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V → ∀ j,
      physicalTestAction A B
        (fun y ↦ (l2ComplexInclusion volume
          (realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦ S))
            (zeroExtend hW z)) y).ofLp) φ j =
      ∫ y, φ y • l2ComplexInclusion volume
        (zeroExtend hW h +
          realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦ source))
            (zeroExtend hW z) - zeroExtend hW z) y j := by
  let z₀ : RH := zeroExtend hW z
  let h₀ : RH := zeroExtend hW h
  let src : RH := realCompression
    (physicalPairedSectorSum {()} (fun _ : Unit ↦ source)) z₀
  have hreal := realPair_correctedSource_right_ae hW hV hVU hVW source residual h z heq
  have hcomplex : l2ComplexInclusion volume
      (realCompression (physicalPairedSectorSum {()}
        (fun _ : Unit ↦ source + residual)) z₀) =ᵐ[volume.restrict V]
      l2ComplexInclusion volume (h₀ + src - z₀) := by
    filter_upwards [hreal,
      ae_restrict_of_ae (euclideanComplexInclusion.coeFn_compLpL
        (realCompression (physicalPairedSectorSum {()}
          (fun _ : Unit ↦ source + residual)) z₀)),
      ae_restrict_of_ae (euclideanComplexInclusion.coeFn_compLpL (h₀ + src - z₀))]
      with y he hl hr
    exact hl.trans ((congrArg euclideanComplexInclusion he).trans hr.symm)
  intro φ hφ hc hs j
  rw [htest z₀ φ hφ hc (hs.trans hVU) j]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hV).mp hcomplex] with y hy
  by_cases hφy : φ y = 0
  · simp only [hφy, zero_smul]
  · exact congrArg (fun v : CF ↦ φ y • v j)
      (hy (hs (subset_tsupport φ hφy)))

section Selected

open RegularSector.FiniteMasks.ActualFamily RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic FourierIntegral.LowBounds

local notation "H₀" => SpacetimeL2 d (d + 1)
local notation "R₀" => Lp (Euclidean (d + 1)) 2 (volume : Measure E)

/-- Apply the tested correction to the literal finite selected solver, source
PDO and three-term analytic residual, without identifying separate selections
(`app:ch_regular:eq:exact-physical`, `energy-complete-residual`). The two
premises are exactly the tested physical equation and corrected-source equation
retained by `exists_finite_direct_fixed_inverse`; its original `2*L` source
threshold, common output multiplier and angular defect all remain intact. -/
theorem selectedFinite_correctedSource_test
    {Ω : Set E} {x : E} {RQ M : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set E}
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d + 1) → MetricTensor (d + 1)) (B : E → MetricTensor (d + 1))
    (W₁ : f.centers → TwoTimeAmplitude d (d + 1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (retarded : Fin 2 → H₀ →L[ℂ] H₀)
    {W U V : Set E} (hW : MeasurableSet W) (hV : MeasurableSet V)
    (hVU : V ⊆ U) (hVW : V ⊆ W)
    (htest : ∀ (u : R₀) (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∀ j,
      physicalTestAction
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (l2ComplexInclusion volume
          (realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦
            selectedFiniteDirectSolver f L Q B output ho hob (retarded 0))) u) y).ofLp)
        φ j = ∫ y, φ y • l2ComplexInclusion volume
          (realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦
            1 + selectedFiniteCompleteError f L Q B W₁ output ho hob (retarded 1))) u) y j)
    (h z : LocalL2 W (Euclidean (d + 1)))
    (heq : ∀ᵐ y ∂volume.restrict V,
      z y + localRealCompression hW U (physicalPairedSectorSum {()} (fun _ : Unit ↦
        selectedFiniteDirectResidual f L Q B W₁ output ho hob (retarded 1))) z y = h y) :
    ∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V → ∀ j,
      physicalTestAction
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
        (fun y ↦ (l2ComplexInclusion volume
          (realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦
            selectedFiniteDirectSolver f L Q B output ho hob (retarded 0)))
            (zeroExtend hW z)) y).ofLp) φ j =
      ∫ y, φ y • l2ComplexInclusion volume
        (zeroExtend hW h + realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦
          (sourceCutMultiplier output ho hob).comp (selectedFiniteSourcePDO f L)))
            (zeroExtend hW z) - zeroExtend hW z) y j := by
  refine realPair_correctedSource_test hW hV hVU hVW
    (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1)) B
    (selectedFiniteDirectSolver f L Q B output ho hob (retarded 0))
    ((sourceCutMultiplier output ho hob).comp (selectedFiniteSourcePDO f L))
    (selectedFiniteDirectResidual f L Q B W₁ output ho hob (retarded 1)) ?_ h z heq
  intro u φ hφ hc hs j
  rw [selectedFiniteCompleteError_identity]
  exact htest u φ hφ hc hs j

end Selected

end JanetCartan.FixedDomainInverse
