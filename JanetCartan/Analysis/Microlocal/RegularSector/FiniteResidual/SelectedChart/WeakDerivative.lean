module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.WeakDerivative.Localization
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.SelectedChart.Collars
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAlgebraic.SupportedBudgets.IntegerBounds

/-!
# The selected solver has a weak derivative on compact smooth inputs

Instantiate the algebraic integer-gain producer with the literal common
physical masks from `PhysicalConstruction`. The inverse-domain and inverse
estimates are the outputs of `exists_finite_physical_evolution_and_algebraic_inverse`
on the same selected chart. The retarded input is its actual order-zero
`RetainedSignedRetardedBounds` output, exported by `SelectedChartEvolutionAt`.
The two spatial collars are matched by `SelectedChart.Collars`.

The resulting derivative is for the SAME L² representative used by
`CompleteResidual.physicalWeakApply`. This supplies the regularity input for
the parent's tested-to-a.e. implication; it does not assert the tested equation
or construct a new solver. Sources: `app:ch_regular_base:eq:energy-complete-residual`
in `paper-v2.tex` and `app:ch_regular_base:eq:sector-theorem-identity` in `paper.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.SelectedChart
open ActualCarriers Characteristic Characteristic.AlgebraicChart Characteristic.RootFamily
open Characteristic.ResidualCoordinates Characteristic.AlgebraicSymbols Characteristic.AmplitudeBounds
open Characteristic.UniformEvolution Characteristic.EvolutionIntegral
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic FiniteEvolution
open FourierIntegral FourierIntegral.LowBounds Pseudodifferential
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "H" => SpacetimeL2 d (d + 1)
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {Aref : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}

/-- The compact smooth selected input gives an actual whole-space weak
Fréchet derivative of the same localized retarded-plus-algebraic solver.
The common output and input masks are literally those of `PhysicalConstruction`.
`hc`, `hsource`, the complement-domain inclusion and `hinverse` come from
`exists_finite_physical_evolution_and_algebraic_inverse`; the proof instantiates
`exists_selected_algebraicSymbols_integer_gain_constants` with these masks.
`hOp` is the solver clause of `SelectedChartEvolutionAt`, at the same enlarged
threshold. Only its positive `s=1` bound is used, on the smooth masked input.
Consumer: the same-output a.e. equation in `energy-complete-residual`, hence
`sector-theorem-identity`. All original coefficient hypotheses are retained.
-/
theorem exists_selected_common_solver_weakDerivative
    (f : ActualMaskFamily Ω x RQ Aref K M) (p : f.centers)
    (hΩ : IsOpen Ω) (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (hc : RootBuffer (f.chart p).index (f.chart p).row (f.chart p).col Aref p.val.val
      (f.chart p).root (f.chart p).coefficientRadius (f.chart p).rootRadius
      (f.chart p).minorGap (f.chart p).transportGap)
    (hsource : MapsTo (rootPhysicalPosition (coordinateSplit (f.chart p).index))
      (tsupport (f.chart p).sourceMask) (closedBall x RQ))
    (inverseCost : ℕ → ℝ) (hcost : ∀ m, 0 < inverseCost m) (hM : 0 ≤ M)
    (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (hQrange : MapsTo Q Ω (closedBall Aref f.coefficientRadius))
    (hQlow : cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M)
    (hBlow : cNorm (closedBall x RQ) (sectorLowOrder d) B ≤ M)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (horange : ∀ y, output y ∈ Icc (0 : ℝ) 1) (hoc : HasCompactSupport output)
    (hosupport : tsupport output ⊆ ball x f.physicalRadius)
    {L : ℝ} (hL : 2 * f.radialThreshold ≤ L) (angular : Euclidean d → ℝ) :
    let c := f.chart p
    let e := physicalCoordinates c.index
    let h := fieldRoot (coordinateSplit c.index) Q c.root
    let β := fun ζ ↦ (dilatedConicMask (f.angularMask p) L (e ζ) : ℂ)
    (∀ ζ ∈ tsupport β, conicMask angular =ᶠ[𝓝 (spatialPart ζ)] fun _ ↦ (1 : ℝ)) →
    ((e ⁻¹' Ω) ×ˢ (normalizeCovector c.radialSection '' tsupport β) ⊆
      complementDomain c.index Q h c.row c.col (normalizedRootDomain c)) →
    (∀ ζ ∈ tsupport β,
      (∀ y ∈ closedBall (e.symm x) RQ, ContDiffAt ℝ ∞
        (fun y ↦ conicBminus c.radialSection c.index Q h c.row c.col y ζ) y) ∧
      ∀ m, (1 + ‖ζ‖) * cNorm (closedBall (e.symm x) RQ) m
        (fun y ↦ conicBminus c.radialSection c.index Q h c.row c.col y ζ) ≤
          inverseCost m * (1 + cNorm (closedBall x RQ) m Q)) →
    ∀ (Δ a : ℝ) (Ψ : TwoTimePhase d) (W : TwoTimeAmplitude d (d + 1))
      (χout χsource : E → ℂ) (hs : ContDiff ℝ ∞ χsource)
      (A₀ : ℝ) (A : ℕ → ℝ) (Op : H →L[ℂ] H),
      RetainedSignedRetardedBounds (closedBall x RQ) Q B Δ a Ψ W
        χout χsource β hs 0 A₀ A Op →
    let ψout := output ∘ e
    let ψsource := f.inputMask ∘ e
    ∃ (hψout : ContDiff ℝ ∞ ψout) (hψsource : ContDiff ℝ ∞ ψsource)
      (hob : ∀ y, ‖ψout y‖ ≤ 1) (hsb : ∀ y, ‖ψsource y‖ ≤ 1),
    let b := directAlgebraicSymbol (conicBminus c.radialSection c.index Q h c.row c.col)
      (conicSourceSymbol c.radialSection (conicMask angular) c.sourceMask) β
    let S := (sourceCutMultiplier ψout hψout.continuous hob).comp
        (Op.comp (sourceCutMultiplier ψsource hψsource.continuous hsb)) +
      (1 / Complex.I) • maskedPhysicalPDO
        (fun y ↦ (ψout y : ℂ)) (fun y ↦ (ψsource y : ℂ)) b
    ∀ u : graphTestSpace (d + 1) (d + 1), ∃ D : E → E →L[ℝ] (Fin (d + 1) → ℂ),
      Mollification.HasWeakFDerivOn volume (fun y ↦ (S (graphTestToLp u) y).ofLp) D univ ∧
        MemLp D 2 volume := by
  intro c e h β hangular hdom hinverse Δ a Ψ W χout χsource hs A₀ A Op hOp ψout ψsource
  have hψout : ContDiff ℝ ∞ ψout := ho.comp e.contDiff
  have hψsource : ContDiff ℝ ∞ ψsource := f.inputMask_smooth.comp e.contDiff
  have hob (y : E) : ‖ψout y‖ ≤ 1 := by
    simpa only [ψout, Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (horange (e y)).1] using (horange (e y)).2
  have hsb (y : E) : ‖ψsource y‖ ≤ 1 := by
    simpa only [ψsource, Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (f.inputMask_range (e y)).1] using (f.inputMask_range (e y)).2
  have hψoc : HasCompactSupport ψout := hoc.comp_homeomorph e.toHomeomorph
  have hψsc : HasCompactSupport ψsource := f.inputMask_compact.comp_homeomorph e.toHomeomorph
  have hcarrier : tsupport (fun y ↦ (ψout y : ℂ)) ⊆ closedBall (e.symm x) RQ := by
    intro y hy
    have hy' : e y ∈ tsupport output :=
      tsupport_comp_subset_preimage output e.continuous
        (tsupport_comp_subset Complex.ofReal_zero ψout hy)
    have hball := f.physicalBall_coefficientDomain
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall
        (by linarith [f.physicalRadius_pos] : f.physicalRadius ≤ 4 * f.physicalRadius)))
        (hosupport hy'))
    change dist y (e.symm x) ≤ RQ
    have he : dist (e y) x = dist y (e.symm x) := by
      conv_lhs => arg 2; rw [← e.apply_symm_apply x]
      rw [dist_eq_norm, ← map_sub, norm_physicalCoordinates, dist_eq_norm]
    simpa only [mem_closedBall, he] using hball
  obtain ⟨hρ, hsρ, hρrange⟩ := chartConicMask_properties f p
  obtain ⟨C, G, _, _, hgain⟩ :=
    exists_selected_algebraicSymbols_integer_gain_constants f p hΩ hRQ hKΩ hc hsource
      _ hρ hsρ hρrange (fun y ↦ (ψout y : ℂ)) (fun y ↦ (ψsource y : ℂ))
      (Complex.ofRealCLM.contDiff.comp hψout) (Complex.ofRealCLM.contDiff.comp hψsource)
      (hψoc.comp_left Complex.ofReal_zero) (hψsc.comp_left Complex.ofReal_zero)
      hcarrier M hM inverseCost hcost
  have horder : 2 * (d + 2) + 2 ≤ sectorLowOrder d := by
    have := (sectorLowOrder_bounds d).2.2
    omega
  have hg := hgain L Q B hQ hB hQrange
    ((cNorm_mono_order horder).trans hQlow) ((cNorm_mono_order horder).trans hBlow)
    hdom hinverse
  refine ⟨hψout, hψsource, hob, hsb, ?_⟩
  intro b S
  let bfamily := directAlgebraicSymbol
    (conicBminus c.radialSection c.index Q h c.row c.col)
    (conicSourceSymbol c.radialSection (conicMask (f.spatialMask p)) c.sourceMask) β
  have hb : b = bfamily := by
    exact congrFun (selected_directPDOSymbols_collar f p hL angular hangular
      (fun _ _ ↦ (0 : CMat)) (fun _ ↦ (0 : CMat)) 0
      (conicBminus c.radialSection c.index Q h c.row c.col)) 0
  apply exists_localized_retarded_algebraic_weakDerivative
    (closedBall x RQ) Q B Δ a Ψ W χout χsource β hs A₀ A Op hOp
    ψout ψsource hψout hψoc hψsource hob hsb b
    ((d + 1 : ℝ) * (d + 1) * G 0)
    (C (2 * (d + 2) + 1) *
      (1 + cNorm (closedBall x RQ) (2 * (d + 2) + 2) Q +
        cNorm (closedBall x RQ) (2 * (d + 2) + 2) B))
  intro v hv
  rw [hb]
  simpa only [Nat.cast_zero, zero_add] using
    (hg bfamily (by exact Or.inl rfl) 0 v (by simpa only [Nat.cast_zero] using hv)).1

end JanetCartan.RegularSector.FiniteResidual.SelectedChart
