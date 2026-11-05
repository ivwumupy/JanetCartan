module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalRegular
public import Mathlib.MeasureTheory.Measure.OpenPos
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSolverSupportTemplate

/-!
# The unchanged compact output of the original normalized solver

Every ambient complex or real L2 input is sent to a class which vanishes
outside the SAME original output cutoff. The literal original38 retarded,
algebraic and elliptic branches, external half, physical pair and real
compression are retained. The static original23 support is compact, contains
both existing inverse-source bumps, and lies in the original wide geometry.
No new output cutoff, support/gain premise, source restriction, inverse or
normal-carrier selection is introduced. Consumers: the uncut solver's smooth
representative and the full ambient response (`main:prop:current-waves`,
`app:ch_response:eq:response-graded-reduced`).
-/

set_option Elab.async false
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

@[expose] public noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff
namespace JanetCartan.PhysicalPrimary.OriginalSolverSupport
open RegularSector NormalizedSolver FiniteAssembly Realization
open FourierIntegral LowBounds CharacteristicTransport.CompleteResidual
open RegularSector.Characteristic.EvolutionIntegral

variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)
local notation "RH" => Lp (Euclidean (d+1)) 2 (volume : Measure E)

/-- The original physical output multiplier forces zero outside its original
support on every ambient L2 input (`app:ch_regular_base:eq:energy-complete-residual`). -/
private theorem cut_zero (output : E → ℝ) (ho : Continuous output)
    (hob : ∀ x, ‖output x‖ ≤ 1) (u : H) :
    ∀ᵐ x ∂volume, x ∉ tsupport output → sourceCutMultiplier output ho hob u x = 0 := by
  filter_upwards [sourceCutMultiplier_coeFn output ho hob u] with x hx
  intro hout
  rw [hx, image_eq_zero_of_notMem_tsupport hout]
  simp

/-- All three genuine direct-solver branches have the SAME original output
multiplier. The external half, physical conjugate and real compression retain
that exact support, on ALL ambient L2 inputs (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem factored_solver_outputs (output : E → ℝ) (ho : Continuous output)
    (hob : ∀ x, ‖output x‖ ≤ 1) (R A El : H →L[ℂ] H) :
    let Mout : H →L[ℂ] H := sourceCutMultiplier output ho hob
    let half : H →L[ℂ] H := (1/2 : ℂ) •
      (Mout.comp R + (-Complex.I) • Mout.comp A + Mout.comp El)
    let paired := physicalPairedSectorSum {()} (fun _ : Unit ↦ half)
    (∀ u : H, ∀ᵐ x ∂volume, x ∉ tsupport output → half u x = 0) ∧
    (∀ u : H, ∀ᵐ x ∂volume, x ∉ tsupport output → paired u x = 0) ∧
    (∀ u : RH, ∀ᵐ x ∂volume, x ∉ tsupport output → realCompression paired u x = 0) := by
  intro Mout half paired
  have raw (u : H) : ∀ᵐ x ∂volume, x ∉ tsupport output →
      (Mout (R u) + (-Complex.I) • Mout (A u) + Mout (El u)) x = 0 := by
    filter_upwards [cut_zero output ho hob (R u), cut_zero output ho hob (A u),
      cut_zero output ho hob (El u), Lp.coeFn_smul (-Complex.I) (Mout (A u)),
      Lp.coeFn_add (Mout (R u)) ((-Complex.I) • Mout (A u)),
      Lp.coeFn_add (Mout (R u) + (-Complex.I) • Mout (A u)) (Mout (El u))]
      with x hR hA hEl hs ha hb
    intro hx
    rw [hb, Pi.add_apply, ha, Pi.add_apply, hs, Pi.smul_apply, hR hx, hA hx, hEl hx]
    simp
  have hh (u : H) : ∀ᵐ x ∂volume, x ∉ tsupport output → half u x = 0 := by
    change ∀ᵐ x ∂volume, x ∉ tsupport output →
      ((1/2 : ℂ) • (Mout (R u) + (-Complex.I) • Mout (A u) + Mout (El u))) x = 0
    filter_upwards [raw u, Lp.coeFn_smul (1/2 : ℂ)
      (Mout (R u) + (-Complex.I) • Mout (A u) + Mout (El u))] with x hx hs
    intro hout
    rw [hs, Pi.smul_apply, hx hout, smul_zero]
  have hp (u : H) : ∀ᵐ x ∂volume, x ∉ tsupport output → paired u x = 0 := by
    dsimp only [paired, physicalPairedSectorSum]
    simp only [Finset.sum_singleton]
    change ∀ᵐ x ∂volume, x ∉ tsupport output → (half u + star (half (star u))) x = 0
    filter_upwards [hh u, hh (star u), Lp.coeFn_star (half (star u)),
      Lp.coeFn_add (half u) (star (half (star u)))] with x hu hv hs ha
    intro hx
    rw [ha, Pi.add_apply, hu hx, hs, Pi.star_apply, hv hx, star_zero, add_zero]
  refine ⟨hh, hp, ?_⟩
  intro u
  change ∀ᵐ x ∂volume, x ∉ tsupport output →
    l2RealPart volume (paired (l2ComplexInclusion volume u)) x = 0
  filter_upwards [hp (l2ComplexInclusion volume u),
    euclideanRealPart.coeFn_compLpL (paired (l2ComplexInclusion volume u))] with x hx hr
  intro hout
  change l2RealPart volume (paired (l2ComplexInclusion volume u)) x =
    euclideanRealPart (paired (l2ComplexInclusion volume u) x) at hr
  rw [hr, hx hout, map_zero]

/-- The original physical output fits into the SAME native geometry domain,
using the existing mask family's four-radius inclusion (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem output_support_geometry {Ω : Set E} {x : E} {RQ M : ℝ}
    {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set E}
    (f : FiniteMasks.ActualFamily.ActualMaskFamily Ω x RQ A₀ K M)
    {output : E → ℝ} (hs : tsupport output ⊆ ball x f.physicalRadius) :
    tsupport output ⊆ Ω := by
  have hr : f.physicalRadius ≤ 4 * f.physicalRadius := by
    linarith only [f.physicalRadius_pos]
  exact hs.trans (ball_subset_closedBall.trans
    ((closedBall_subset_closedBall hr).trans f.physicalBall_subset))

/-- A continuous representative of the SAME supported L2 class retains its
closed output support; no extra multiplier is introduced (`main:prop:current-waves`). -/
theorem continuous_tsupport_of_ae_zero {n : ℕ} {K : Set (Euclidean n)} (hK : IsClosed K)
    (u : Lp (Euclidean n) 2 (volume : Measure (Euclidean n)))
    (g : Euclidean n → Euclidean n) (hg : Continuous g) (heq : g =ᵐ[volume] u)
    (hz : ∀ᵐ x ∂volume, x ∉ K → u x = 0) : tsupport g ⊆ K := by
  have he : g =ᵐ[volume.restrict Kᶜ] fun _ ↦ 0 := by
    apply (ae_restrict_iff' hK.measurableSet.compl).mpr
    filter_upwards [heq, hz] with x hx hx0
    exact fun hout ↦ hx.trans (hx0 hout)
  have hall := Measure.eqOn_open_of_ae_eq he hK.isOpen_compl
    hg.continuousOn continuous_const.continuousOn
  apply closure_minimal _ hK
  intro x hx
  by_contra hout
  exact hx (hall hout)

/-- The existing output plateau contains either original inverse-source bump;
no new source or output cutoff is selected (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem source_support_original_output {n : ℕ} {x : Euclidean n} {r a : ℝ}
    {output χ : Euclidean n → ℝ}
    (hp : closedBall x r ⊆ interior {y | output y = 1})
    (hχ : tsupport χ ⊆ ball x (min r a)) : tsupport χ ⊆ tsupport output := by
  intro y hy
  have hball : y ∈ closedBall x r :=
    ball_subset_closedBall ((ball_subset_ball (min_le_left r a)) (hχ hy))
  have hy' : y ∈ {z : Euclidean n | output z = 1} := interior_subset (hp hball)
  have hone : output y = 1 := hy'
  apply subset_tsupport output
  change output y ≠ 0
  rw [hone]
  exact one_ne_zero

/-- The same compact output stays inside the original wide immersion/rank
chart, before the source contraction and current history (`main:prop:current-waves`). -/
theorem output_support_wide {d : ℕ} (hn : 5 ≤ d+1) {RQ M : ℝ}
    {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
    (f : FiniteMasks.ActualFamily.ActualMaskFamily
      (ball 0 (PhysicalSeed.OriginalBoundary.b hn)) 0 RQ A₀ K M)
    {output : Euclidean (d+1) → ℝ}
    (hs : tsupport output ⊆ ball 0 f.physicalRadius) :
    tsupport output ⊆ ball 0 (PhysicalSeed.OriginalBoundary.R hn) :=
  (output_support_geometry f hs).trans
    (ball_subset_ball (PhysicalSeed.OriginalBoundary.b_lt_R hn).le)

end JanetCartan.PhysicalPrimary.OriginalSolverSupport
open scoped ContDiff Matrix.Norms.Frobenius
set_option maxRecDepth 16000
construct_original_solver_support

end
