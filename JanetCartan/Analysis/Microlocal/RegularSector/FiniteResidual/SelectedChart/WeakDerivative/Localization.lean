module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Masks
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.Multiplier
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier.Projection
public import JanetCartan.Analysis.Sobolev.Local.Fourier.VectorFirstDerivative

/-!
# Weak differentiation of the same localized solver

The positive order-one retarded estimate is applied only to compact smooth
inputs. The algebraic input below is precisely the order-zero forward gain
exported by `FiniteAlgebraic.SupportedBudgets.IntegerBounds`, with the same
physical masks. The parent leaf instantiates that producer on the selected
chart. The resulting derivative acts on the literal L² representative used
by `CompleteResidual.physicalWeakApply` in `energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.SelectedChart
open Characteristic Characteristic.UniformEvolution Characteristic.EvolutionIntegral
open FourierIntegral FourierIntegral.LowBounds Pseudodifferential LocalSobolev
open JanetCartan.CharacteristicTransport.CompleteResidual
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => SpacetimeL2 d q

private theorem exists_sum_coordinate_weakDerivative
    (v w : H) (hv : MemVectorFourierSobolev 1 v)
    (hw : MemVectorFourierSobolev 1 w) :
    ∃ D : E → E →L[ℝ] (Fin q → ℂ),
      Mollification.HasWeakFDerivOn volume
        (fun x ↦ ((v + (1 / Complex.I) • w) x).ofLp) D univ ∧ MemLp D 2 volume := by
  obtain ⟨Dv, hvD, hvm, _⟩ := exists_vector_firstWeakDerivative v hv
  obtain ⟨Dw, hwD, hwm, _⟩ := exists_vector_firstWeakDerivative w hw
  let L : F →L[ℝ] F := (1 / Complex.I) • ContinuousLinearMap.id ℝ F
  let P : F →L[ℝ] (Fin q → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin q ↦ ℂ)).toContinuousLinearMap
  have hd := (hvD.add_univ (hwD.comp_clm_univ L)).comp_clm_univ P
  refine ⟨fun x ↦ P.comp (Dv x + L.comp (Dw x)), ?_, ?_⟩
  · apply hd.congr_ae _ Filter.EventuallyEq.rfl
    rw [Measure.restrict_univ]
    filter_upwards [Lp.coeFn_add v ((1 / Complex.I) • w),
      Lp.coeFn_smul (1 / Complex.I) w] with x hx hs
    change (v x + (1 / Complex.I) • w x).ofLp = _
    simp only [hx, Pi.add_apply, hs, Pi.smul_apply]
  · exact ((ContinuousLinearMap.compL ℝ E F (Fin q → ℂ)) P).comp_memLp'
      (hvm.add (((ContinuousLinearMap.compL ℝ E F F) L).comp_memLp' hwm))

/-- Construct a genuine whole-space derivative of the actual sum of the
localized order-zero retarded solver and its algebraic correction. `hOp` is
the solver output of `SelectedChartEvolutionAt`; `hP` is the positive `n=0`
forward clause of `exists_selected_algebraicSymbols_integer_gain_constants`.
No regularity of the solver on arbitrary L² inputs is used. Consumer: the
same-output a.e. equation in `app:ch_regular_base:eq:energy-complete-residual`.
-/
theorem exists_localized_retarded_algebraic_weakDerivative
    (KQ : Set E) (Q : E → Fin (d + 1) → MetricTensor (d + 1))
    (B : E → MetricTensor (d + 1)) (Δ a : ℝ)
    (Ψ : TwoTimePhase d) (W : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
    (A₀ : ℝ) (A : ℕ → ℝ) (Op : H →L[ℂ] H)
    (hOp : RetainedSignedRetardedBounds KQ Q B Δ a Ψ W χout χsource β hs 0 A₀ A Op)
    (ψout ψsource : E → ℝ) (ho : ContDiff ℝ ∞ ψout)
    (hoc : HasCompactSupport ψout) (hsource : ContDiff ℝ ∞ ψsource)
    (hob : ∀ x, ‖ψout x‖ ≤ 1) (hsb : ∀ x, ‖ψsource x‖ ≤ 1)
    (b : E → E → Matrix (Fin q) (Fin q) ℂ) (C high : ℝ)
    (hP : ∀ v : H, MemVectorFourierSobolev 0 v →
      MemVectorFourierSobolev 1
          (maskedPhysicalPDO (fun x ↦ (ψout x : ℂ)) (fun x ↦ (ψsource x : ℂ)) b v) ∧
        vectorFourierSobolevNorm 1
          (maskedPhysicalPDO (fun x ↦ (ψout x : ℂ)) (fun x ↦ (ψsource x : ℂ)) b v) ≤
            C * (vectorFourierSobolevNorm 0 v + high * ‖v‖)) :
    let S := (sourceCutMultiplier ψout ho.continuous hob).comp
        (Op.comp (sourceCutMultiplier ψsource hsource.continuous hsb)) +
      (1 / Complex.I) • maskedPhysicalPDO
        (fun x ↦ (ψout x : ℂ)) (fun x ↦ (ψsource x : ℂ)) b
    ∀ u : graphTestSpace (d + 1) q, ∃ D : E → E →L[ℝ] (Fin q → ℂ),
      Mollification.HasWeakFDerivOn volume (fun x ↦ (S (graphTestToLp u) x).ofLp) D univ ∧
        MemLp D 2 volume := by
  intro S u
  have hret : MemVectorFourierSobolev 1
      (Op (sourceCutMultiplier ψsource hsource.continuous hsb (graphTestToLp u))) := by
    rw [sourceCutMultiplier_graphTestToLp ψsource hsource hsb u]
    simpa only [Nat.cast_one] using (hOp.2.2.2.1 1 Op (Or.inl rfl) _
      (graphTest_memVectorFourierSobolev _ (sourceCutTest ψsource hsource u))).1
  obtain ⟨_, _, hmul⟩ := exists_sourceCutMultiplier_fourierSobolev_bound
    (r := q) ψout ho hoc hob 1
  simp only [Nat.cast_one] at hmul
  exact exists_sum_coordinate_weakDerivative _ _ (hmul _ hret).1
    (hP _ (graphTest_memVectorFourierSobolev 0 u)).1

end JanetCartan.RegularSector.FiniteResidual.SelectedChart
