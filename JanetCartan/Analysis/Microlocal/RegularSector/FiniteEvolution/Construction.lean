module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.LocalOperators

/-!
# Construct the retarded factors on the actual finite family

Select the finite family with retained retarded radii, then apply its SAME
coefficient-family producer to construct the literal solver and residual
evolutions on every selected patch. All physical source plateaux are chosen
around the original common input support, in the actual selected coordinates.

This closes the primitive retarded instantiation. The complete sector still
requires the algebraic/endpoint PDO instantiation, physical radial-cutoff
identification, common output localization and finite residual sum.
Sources: `app:ch_regular_base:thm:sector` and
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteEvolution
open ActualCarriers Characteristic Characteristic.ResidualCoordinates
open FiniteMasks.ActualFamily
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)

/-- The original common input support lies in the coefficient domain in
EVERY selected coordinate system. No new source mask or source domain is
substituted for it (`energy-complete-residual`). -/
theorem selected_input_carrier_subset_domain
    {Ω : Set E} {x : E} {RQ M : ℝ}
    {A₀ : Fin (d+1) → Mat} {K : Set E}
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) :
    (physicalCoordinates (f.chart p).index).symm '' tsupport f.inputMask ⊆
      (physicalCoordinates (f.chart p).index) ⁻¹' Ω := by
  rintro _ ⟨y, hy, rfl⟩
  change physicalCoordinates (f.chart p).index
    ((physicalCoordinates (f.chart p).index).symm y) ∈ Ω
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply f.physicalBall_subset
  exact ball_subset_closedBall ((ball_subset_ball (by
    have := f.physicalRadius_pos
    linarith : 3 * f.physicalRadius ≤ 4 * f.physicalRadius)) (f.inputMask_support hy))

/-- From a frozen regular pencil construct one finite family with actual
signed solver and `PW₁` evolutions on each selected chart. Their constants,
low coefficient order, masks and chart data precede varying `Q,B`, history,
Sobolev order and accuracy. Every phase and amplitude premise of the local
operator constructor is discharged by the original coefficient producer.
The source plateau contains the SAME common input support. This proves the
retarded factors, not the full sector residual (`thm:sector`,
`energy-complete-residual`). -/
theorem exists_actual_finite_signed_evolution
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Fin (d+1) → Mat) {K : Set E} (hK : IsCompact K)
    (hKzero : (0 : E) ∉ K)
    (hregular : ∀ ξ ∈ K, determinant A₀ ξ = 0 → fderiv ℝ (determinant A₀) ξ ≠ 0)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ f : ActualMaskFamily Ω x RQ A₀ K M,
      (∀ p : f.centers, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
        (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4) ∧
      ∀ p : f.centers, SelectedChartEvolution (f.chart p) (f.angularMask p)
        ((physicalCoordinates (f.chart p).index).symm '' tsupport f.inputMask)
        ((physicalCoordinates (f.chart p).index) ⁻¹' Ω) := by
  obtain ⟨f, hradii⟩ := exists_actualMaskFamily_with_retarded_radii
    hΩ x hRQ hKΩ A₀ hK hKzero hregular hM
  refine ⟨f, hradii, ?_⟩
  intro p
  exact exists_selected_chart_signed_operators (f.chart p) (hradii p).1 (hradii p).2 hM
    (f.angularMask p) (f.angularMask_smooth p) (f.angularMask_support p)
    (f.inputMask_compact.image (physicalCoordinates (f.chart p).index).symm.continuous)
    (hΩ.preimage (physicalCoordinates (f.chart p).index).continuous)
    (selected_input_carrier_subset_domain f p)

end JanetCartan.RegularSector.FiniteEvolution
