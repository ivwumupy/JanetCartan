module

public import JanetCartan.Iteration.PhysicalAdjointGeometry.PrimitiveProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.CoordinateTransfer.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.PhaseJets

/-!
# Full physical realization of the same joint trade family

The original adapted spacetime isometry transfers all derivatives, including
time, to physical Euclidean coordinates. Restricting to the physical variables
only decreases the derivative norm. Neither operation spends a reserve or
introduces an input-frequency power. The exact original full Hamilton phase
is retained, not replaced by a homogeneous model.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalAdjointGeometry

variable {X Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] {m : ℕ}

/-- The same physical coordinate isometry, with the original carrier and
literal displacement left unchanged (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
def jointCoordinateEquiv (e : X ≃ₗᵢ[ℝ] Z) : Point X m ≃ₗᵢ[ℝ] Point Z m where
  toLinearEquiv := e.toLinearEquiv.prodCongr (LinearEquiv.refl ℝ (Euclidean m × Euclidean m))
  norm_map' q := by
    change max ‖e q.1‖ ‖q.2‖ = max ‖q.1‖ ‖q.2‖
    rw [e.norm_map]

/-- Full physical realization of the original averaged phase coefficient. -/
def physicalCovector (e : X ≃ₗᵢ[ℝ] Z) (Y : Point X m → Euclidean m) : Point Z m → Euclidean m :=
  Y ∘ jointCoordinateEquiv e.symm

/-- Full physical realization of the same joint inverse-transpose family. -/
def physicalTrade (e : X ≃ₗᵢ[ℝ] Z) (L : Point X m → Euclidean m →L[ℝ] X)
    (q : Point Z m) : Euclidean m →L[ℝ] Z :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.comp (L (jointCoordinateEquiv e.symm q))

/-- The physical covector realization remains globally jointly smooth. -/
theorem contDiff_physicalCovector (e : X ≃ₗᵢ[ℝ] Z)
    {Y : Point X m → Euclidean m} (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (physicalCovector e Y) :=
  hY.comp (jointCoordinateEquiv e.symm).toContinuousLinearEquiv.contDiff

/-- The physical direction realization remains globally jointly smooth. -/
theorem contDiff_physicalTrade (e : X ≃ₗᵢ[ℝ] Z)
    {L : Point X m → Euclidean m →L[ℝ] X} (hL : ContDiff ℝ ∞ L) :
    ContDiff ℝ ∞ (physicalTrade e L) :=
  contDiff_const.clm_comp (hL.comp (jointCoordinateEquiv e.symm).toContinuousLinearEquiv.contDiff)

/-- Every joint covector derivative norm is preserved, including all physical
time derivatives (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_jet_physicalCovector (e : X ≃ₗᵢ[ℝ] Z) (Y : Point X m → Euclidean m)
    (q : Point Z m) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (physicalCovector e Y) q‖ =
      ‖iteratedFDeriv ℝ k Y (jointCoordinateEquiv e.symm q)‖ :=
  (jointCoordinateEquiv e.symm).norm_iteratedFDeriv_comp_right Y q k

/-- Every joint physical direction derivative is bounded with norm factor
one. In particular its reserve and original frequency independence survive
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem norm_jet_physicalTrade_le (e : X ≃ₗᵢ[ℝ] Z)
    {L : Point X m → Euclidean m →L[ℝ] X} (hL : ContDiff ℝ ∞ L)
    (q : Point Z m) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (physicalTrade e L) q‖ ≤
      ‖iteratedFDeriv ℝ k L (jointCoordinateEquiv e.symm q)‖ := by
  let P : (Euclidean m →L[ℝ] X) →L[ℝ] (Euclidean m →L[ℝ] Z) :=
    ContinuousLinearMap.compL ℝ (Euclidean m) X Z e.toContinuousLinearEquiv.toContinuousLinearMap
  have heop : ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖e x‖ ≤ 1 * ‖x‖
    simp
  have hP : ‖P‖ ≤ 1 := by
    apply P.opNorm_le_bound zero_le_one
    intro A
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa using (mul_le_mul_of_nonneg_right heop (norm_nonneg A)))
  have hs := hL.comp (jointCoordinateEquiv e.symm).toContinuousLinearEquiv.contDiff
  have hb := P.norm_iteratedFDeriv_comp_left (x := q) hs.contDiffAt (by simp : (k : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDeriv ℝ k (physicalTrade e L) q‖ ≤ _ at hb
  apply (hb.trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))).trans
  simpa only [one_mul, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
    ((jointCoordinateEquiv e.symm).norm_iteratedFDeriv_comp_right L q k).le

/-- The exact derivative-trade identity transfers through the full physical
isometry, with all directions evaluated at the same carrier and shift
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem fderiv_phase_physicalTrade (e : X ≃ₗᵢ[ℝ] Z)
    {Y : Point X m → Euclidean m} (hY : ContDiff ℝ ∞ Y)
    (L : Point X m → Euclidean m →L[ℝ] X) (q : Point Z m)
    (h η : Euclidean m)
    (hid : fderiv ℝ (fun x ↦ inner ℝ (Y (x, q.2)) η) (e.symm q.1)
      (L (jointCoordinateEquiv e.symm q) h) = inner ℝ h η) :
    fderiv ℝ (fun x ↦ inner ℝ (physicalCovector e Y (x, q.2)) η) q.1
      (physicalTrade e L q h) = inner ℝ h η := by
  have hs : ContDiff ℝ ∞ (fun x ↦ inner ℝ (Y (x, q.2)) η) :=
    (hY.comp (contDiff_id.prodMk contDiff_const)).inner ℝ contDiff_const
  have hd := (hs.differentiable (by simp) (e.symm q.1)).hasFDerivAt.comp q.1
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  change HasFDerivAt (fun x ↦ inner ℝ (physicalCovector e Y (x, q.2)) η) _ q.1 at hd
  rw [hd.fderiv]
  change fderiv ℝ (fun x ↦ inner ℝ (Y (x, q.2)) η) (e.symm q.1)
    (e.symm (e (L (jointCoordinateEquiv e.symm q) h))) = _
  rw [e.symm_apply_apply]
  exact hid

variable {n : ℕ}

/-- One joint frequency/physical measurable direction family; it is not a
choice of unrelated measurable extensions at each frequency
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem measurable_sampled_physicalTrade (e : X ≃ₗᵢ[ℝ] Euclidean n)
    {L : Point X m → Euclidean m →L[ℝ] X} (hL : ContDiff ℝ ∞ L)
    (ζ : Euclidean m) (τ : ℝ) :
    Measurable (fun q : Euclidean m × Euclidean n ↦ physicalTrade e L (q.2, ζ, τ • q.1)) :=
  (contDiff_sampled_trade_family (contDiff_physicalTrade e hL) ζ τ).continuous.measurable

open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualPhase
open LeadingWave.FullModulation RawPrimary.SliceBounds

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The physical primitive is exactly the retained full Hamilton phase,
through the original adapted isometry (`app:ch_waves:eq:WKB-W`). -/
theorem fullPhase_eq_current_pullback (Q : _) (x : Euclidean n) (ζ : Euclidean (n - 1)) :
    phase T Q x ζ = current T Q ((adaptedSpacetimeEquiv T.data.adapted).symm x, ζ) := by
  have he : FullPhaseCharts.adaptedSpacetime T.data.adapted
      ((adaptedSpacetimeEquiv T.data.adapted).symm x) = x :=
    (adaptedSpacetimeEquiv T.data.adapted).apply_symm_apply x
  simpa only [he] using phase_in_adapted_coordinates T Q
    ((adaptedSpacetimeEquiv T.data.adapted).symm x, ζ)

/-- The exact unchanged raw full phase is the localized physical linear
pairing on the original support. The primitive phase, carrier, inverse
frequency and literal shift are all retained
(`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem literal_rawPhase_eq_inner_physicalCovector (Q : _)
    {Y : Point (Spacetime (n - 1)) (n - 1) → Euclidean (n - 1)}
    {x : Euclidean n} {ζ η : Euclidean (n - 1)} {τ : ℝ} (hτ : τ ≠ 0)
    (hq : ((adaptedSpacetimeEquiv T.data.adapted).symm x, ζ, τ • η) ∈
      shiftDomain (covectorCenter T) T.family.radius)
    (heY : Y =ᶠ[𝓝 ((adaptedSpacetimeEquiv T.data.adapted).symm x, ζ, τ • η)]
      averagedCovector (current T Q)) :
    (phase T Q x (ζ + τ • η) - phase T Q x ζ) / τ =
      inner ℝ (physicalCovector (adaptedSpacetimeEquiv T.data.adapted) Y (x, ζ, τ • η)) η := by
  rw [fullPhase_eq_current_pullback, fullPhase_eq_current_pullback]
  change _ = inner ℝ (Y ((adaptedSpacetimeEquiv T.data.adapted).symm x, ζ, τ • η)) η
  rw [heY.eq_of_nhds]
  have hs : ContDiffOn ℝ ∞ (current T Q)
      (Metric.ball (0 : Spacetime (n - 1)) T.family.radius ×ˢ
        Metric.ball (covectorCenter T) T.family.radius) := by
    rw [ball_prod_same]
    exact (current_smooth T Q).mono (Metric.ball_subset_ball (by linarith [T.family.radius_pos]))
  have hζ : ζ ∈ Metric.ball (covectorCenter T) T.family.radius :=
    lt_of_le_of_lt (le_add_of_nonneg_right (norm_nonneg _)) hq.2
  have hshift : ζ + τ • η ∈ Metric.ball (covectorCenter T) T.family.radius := by
    have hb := segment_mem_phaseBall hq (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    rw [Metric.mem_ball, segment_apply, Prod.dist_eq, max_lt_iff, one_smul] at hb
    exact hb.2
  exact rawPhase_eq_inner_averagedCovector Metric.isOpen_ball Metric.isOpen_ball
    (convex_ball _ _) hs (by simpa using hq.1) hζ hshift hτ

end JanetCartan.PhysicalAdjointGeometry
