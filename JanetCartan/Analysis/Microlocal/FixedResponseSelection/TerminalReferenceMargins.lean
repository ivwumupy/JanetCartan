module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.TerminalAdmission
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ReducedCoefficients
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.FiberBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.ScaledReference

/-!
# Original full-array margins for terminal protection and source histories

The common initializer takes arbitrary finite full and extended coefficient
margins. Project its SAME local reduced array onto the original principal rows,
then apply the existing retained-history admission at the selected coefficient
radius and all original phase tolerances. The requested margins precede the
reference, its scale, the target and every history. The family is supplied; the
separate pre-reference stationary selection must construct it in this order.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ProtectedFlow
open GeometricProfile ProjectedStressFrame FullPhaseCharts.InverseEstimates

/-- Principal-row projection of the original complete reduced array
(`app:ch_regular:eq:coefficient-extension`). -/
private def terminalPrincipalRowProjection {n : ℕ} (i : Fin n) :
    (ReducedCoefficientIndex n → ℝ) →L[ℝ] MetricTensor n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a j k ↦ a (.inl (j, i, k))
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

/-- The same full coefficient margin requested from the common initializer
admits both the original terminal protection at order `m` and the selected
family's history tolerance at order six. No reference is chosen here. The
parent supplies this margin at order `m` to the arbitrary finite-margin clause
of `exists_common_normalized_history_reference_with_chart_centers_and_carrier_data_and_comparison_radius_and_position_smoothness`,
on its SAME menu and source scale. Physical buffers remain unchanged
(`app:ch_seed:setup:seed-current`, `app:ch_regular:thm:no-return`). -/
theorem exists_full_coefficient_margin_for_terminal_reference_admission
    {n : ℕ} (m : ℕ) (hm : 6 ≤ m)
    {ηprotect ηhistory : ℝ} (hp : 0 < ηprotect) (hh : 0 < ηhistory) :
    ∃ μ > (0 : ℝ),
      ∀ {N : ℕ} (F : Euclidean n → Euclidean N), ContDiff ℝ ∞ F →
      ∀ {U : Set (Euclidean n)}, IsOpen U →
        IsImmersionOn F U → HasFullNormalRankOn F U →
      ∀ {b r : ℝ}, r ≤ b → closedBall (0 : Euclidean n) b ⊆ U →
        cNorm (closedBall (0 : Euclidean n) b) m
          (geometricReducedCoefficients F - reducedCoefficientBackground (fun _ _ ↦ 0)) < μ →
        (∀ i, cNorm (closedBall (0 : Euclidean n) b) m
          (fun y ↦ projectedStress F y i - cubeStress n i) < ηprotect) ∧
        (∀ i, cNorm (closedBall (0 : Euclidean n) r) 6
          (fun y ↦ projectedStress F y i - cubeStress n i) < ηhistory) := by
  let D : ℝ := 1 + ∑ i : Fin n, ‖terminalPrincipalRowProjection i‖
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have hDi (i : Fin n) : ‖terminalPrincipalRowProjection i‖ ≤ D := by
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) ↦ norm_nonneg (terminalPrincipalRowProjection j))
      (Finset.mem_univ i)
    dsimp only [D]
    linarith
  refine ⟨min ηprotect ηhistory / D, div_pos (lt_min hp hh) hD, ?_⟩
  intro N F hF U hU hi hrank b r hrb hKU hfull
  let K := closedBall (0 : Euclidean n) b
  let a := geometricReducedCoefficients F - reducedCoefficientBackground (fun _ _ ↦ 0)
  have ha : ∀ x ∈ K, ContDiffAt ℝ m a x := by
    intro x hx
    exact (((ContinuumRow.ImageGeometry.contDiffOn_geometricReducedCoefficients hF hU hi hrank).contDiffAt (hU.mem_nhds (hKU hx))).sub
        (contDiff_reducedCoefficientBackground contDiff_const).contDiffAt).of_le (by simp)
  have hrow (i : Fin n) : cNorm K m (fun y ↦ projectedStress F y i - cubeStress n i) <
      min ηprotect ηhistory := by
    have heq : cNorm K m (fun y ↦ projectedStress F y i - cubeStress n i) =
        cNorm K m (terminalPrincipalRowProjection i ∘ a) := by
      apply cNorm_eq_of_eventuallyEq
      intro x hx
      filter_upwards [hU.mem_nhds (hKU hx)] with y hy
      ext j k
      change projectedStress F y i j k - cubeStress n i j k =
        (StressFrame.geometricCubeStress F y i).val j k - cubeStress n i j k
      rw [ContinuumRow.ImageGeometry.geometricCubeStress_val_eq_projectedStress
          (hF.contDiffAt.of_le (by simp)) (hrank y hy) i]
    rw [heq]
    have hbudget := cNorm_postLinear_le_on (isCompact_closedBall _ _) m
      (terminalPrincipalRowProjection i) ha
    have hlt : D * cNorm K m a < min ηprotect ηhistory := by
      simpa only [mul_comm] using (lt_div_iff₀ hD).mp hfull
    exact (hbudget.trans (mul_le_mul_of_nonneg_right (hDi i) (cNorm_nonneg K m a))).trans_lt hlt
  refine ⟨fun i ↦ (hrow i).trans_le (min_le_left _ _), ?_⟩
  intro i
  have hsmooth : ∀ x ∈ K, ContDiffAt ℝ 6 (fun y ↦ projectedStress F y i - cubeStress n i) x := by
    intro x hx
    exact (((contDiffOn_projectedStress hU hF.contDiffOn hi hrank i).contDiffAt
      (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp)
  exact ((cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall hrb)
    (isCompact_closedBall _ _) hsmooth).trans (cNorm_mono_order hm)).trans_lt
      ((hrow i).trans_le (min_le_right _ _))

end JanetCartan.ProtectedFlow

namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.FiniteMasks.ActualFamily
open ActualCarriers.CurrentFullPhase ProjectedStressFrame ProtectedFlow GeometricProfile

/-- The actual finite margins for the SAME selected family are converted to
one full-array tolerance that the common initializer can request BEFORE its
reference scale. The conclusion retains no-return admission, coefficient range,
all original phase margins and a C6 cap at most one. This is a supplied-family
continuation, not a pre-reference construction of that family
(`app:ch_seed:setup:seed-current`, `app:ch_regular:thm:no-return`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_full_coefficient_margin_for_selected_history_admission
    {d : ℕ} {ι : Type*} [Finite ι]
    {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
    {K : Set (Euclidean (d+1))}
    (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) K M)
    (δphase : ι → ℝ) (hδphase : ∀ j, 0 < δphase j)
    (ext : BallExtension.Parameters (Euclidean (d+1))) (hext : ext.center = 0)
    (m : ℕ) (hm : 6 ≤ m) {ηprotect : ℝ} (hηprotect : 0 < ηprotect) :
    ∃ δ > (0 : ℝ), δ ≤ 1 ∧ (∀ j, δ ≤ δphase j) ∧
    ∃ μ > (0 : ℝ),
      ∀ Gref : FlatReference (d+1), ∀ b R : ℝ,
      ext.radius ≤ b → b < R → R < Gref.domain.chartRadius →
      cNorm (closedBall (0 : Euclidean (d+1)) b) m
        (geometricReducedCoefficients Gref.map -
          reducedCoefficientBackground (fun _ _ ↦ 0)) < μ →
      (∀ i, cNorm (closedBall (0 : Euclidean (d+1)) b) m
        (fun y ↦ projectedStress Gref.map y i - cubeStress (d+1) i) < ηprotect) ∧
      ∀ kMin : ℕ,
      displacementLoss (d+1) + bandExponent * (8 + ((d+1 : ℕ) : ℝ) / 2) + 2 < kMin →
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → Torus (d+1) → Euclidean (embeddingDimension (d+1)))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let Q := extendedProjectedStress ext (finiteHistoryMap Gref.map u)
      ContDiff ℝ ∞ Q ∧ MapsTo Q univ (closedBall (cubeStress (d+1)) f.coefficientRadius) ∧
      (∀ A : Set (Euclidean (d+1)), cNorm A 6 (Q - fun _ ↦ cubeStress (d+1)) < δ) ∧
      ∀ j, ∀ A : Set (Euclidean (d+1)), cNorm A 6 (Q - fun _ ↦ cubeStress (d+1)) < δphase j := by
  let δall : Option ι → ℝ := fun j ↦ j.elim 1 δphase
  have hδall : ∀ j, 0 < δall j := by
    intro j
    cases j with
    | none => exact zero_lt_one
    | some j => exact hδphase j
  obtain ⟨δ, hδ, hδle, η, hη, _, hadmit⟩ :=
    exists_reference_tolerance_for_selected_full_source_margins
      f δall hδall ext hext hηprotect
  obtain ⟨μ, hμ, hfull⟩ := exists_full_coefficient_margin_for_terminal_reference_admission
    (n := d+1) m hm hηprotect hη
  refine ⟨δ, hδ, hδle none, (fun j ↦ hδle (some j)), μ, hμ, ?_⟩
  intro Gref b R heb hbR hR href
  have himm : IsImmersionOn Gref.map (Gref.domain.chart (d+1)) :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one)
      (fun y _ ↦ Gref.inducedMetric_eq_one y)
  obtain ⟨hprotect, hhistory⟩ := hfull Gref.map Gref.contDiff
    (show IsOpen (Gref.domain.chart (d+1)) from isOpen_ball) himm Gref.fullNormalRank
    heb (closedBall_subset_ball (hbR.trans hR)) href
  refine ⟨hprotect, ?_⟩
  intro kMin horder
  obtain ⟨S, hS, hproduce⟩ := hadmit Gref R (heb.trans_lt hbR) hR hhistory kMin horder
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ s u ell hu
  obtain ⟨hQ, hrange, hlow, hphases⟩ := hproduce R₀ hR₀ s u ell hu
  exact ⟨hQ, hrange, hlow, fun j ↦ hphases (some j)⟩

/-- The selected-family full-array tolerance is used on the SAME initialized
source dilation, with the original analytic source's outer chart. The working
reference may have a smaller domain: its proved map equality identifies every
literal history field with the deterministic wide-domain source dilation.
No independent reference is chosen (`main:eq:normalized`,
`app:ch_regular:thm:no-return`, `app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_full_coefficient_margin_for_selected_history_on_source_dilation
    {d : ℕ} {ι : Type*} [Finite ι]
    {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
    {K : Set (Euclidean (d+1))}
    (f : ActualMaskFamily Ω x RQ (cubeStress (d+1)) K M)
    (δphase : ι → ℝ) (hδphase : ∀ j, 0 < δphase j)
    (ext : BallExtension.Parameters (Euclidean (d+1))) (hext : ext.center = 0)
    (m : ℕ) (hm : 6 ≤ m) {ηprotect : ℝ} (hηprotect : 0 < ηprotect) :
    ∃ δ > (0 : ℝ), δ ≤ 1 ∧ (∀ j, δ ≤ δphase j) ∧
    ∃ μ > (0 : ℝ),
      ∀ G₀ Gref : FlatReference (d+1), ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      Gref.map = sourceDilation G₀.map ρ → ∀ b R : ℝ,
      ext.radius ≤ b → b < R → R < G₀.domain.chartRadius →
      cNorm (closedBall (0 : Euclidean (d+1)) b) m
        (geometricReducedCoefficients Gref.map -
          reducedCoefficientBackground (fun _ _ ↦ 0)) < μ →
      (∀ i, cNorm (closedBall (0 : Euclidean (d+1)) b) m
        (fun y ↦ projectedStress Gref.map y i - cubeStress (d+1) i) < ηprotect) ∧
      ∀ kMin : ℕ,
      displacementLoss (d+1) + bandExponent * (8 + ((d+1 : ℕ) : ℝ) / 2) + 2 < kMin →
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → Torus (d+1) → Euclidean (embeddingDimension (d+1)))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let Q := extendedProjectedStress ext (finiteHistoryMap Gref.map u)
      ContDiff ℝ ∞ Q ∧ MapsTo Q univ (closedBall (cubeStress (d+1)) f.coefficientRadius) ∧
      (∀ A : Set (Euclidean (d+1)), cNorm A 6 (Q - fun _ ↦ cubeStress (d+1)) < δ) ∧
      ∀ j, ∀ A : Set (Euclidean (d+1)), cNorm A 6 (Q - fun _ ↦ cubeStress (d+1)) < δphase j := by
  obtain ⟨δ, hδ, hδone, hδphase', μ, hμ, hadmit⟩ :=
    exists_full_coefficient_margin_for_selected_history_admission
      f δphase hδphase ext hext m hm hηprotect
  refine ⟨δ, hδ, hδone, hδphase', μ, hμ, ?_⟩
  intro G₀ Gref ρ hρ hρone hmap b R heb hbR hR href
  let Gwide := sourceDilationReference G₀ hρ hρone
  have hsame : Gref.map = Gwide.map := hmap
  have h := hadmit Gwide b R heb hbR hR
    (by simpa only [← hsame] using href)
  simpa only [← hsame] using h

end JanetCartan.ResponseTransfer.RetainedFactors
