module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.Measurement
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.LiteralSupport
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.FullNormalGeometry.PhaseJets.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.PullbackGrades

/-!
# The literal normalized pullback of the retained measured polynomial

The substitution retains the incidence variable, spectators, physical point
and shifted covector. Its fixed geometric jets are uniform in the reciprocal
dyadic scale. The original buffered carrier refinement gives a concrete
plateau on which the supported polynomial is exactly the raw polynomial.
These close the pullback and cutoff-agreement obligations for the nonzero
amplitude in `app:ch_waves:eq:sampling-operator-bounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open FullPhaseCharts.ActualPhase FullPhaseCharts.ActualComparison
open RawKernel FullNormalGeometry FullNormalGeometry.PhaseJets
open MeanNormalBound.NormalizedFullPhase ContinuumRow ContinuumRow.CanonicalConic
open RawPrimary.MaskProfiles RawPrimary.SliceBounds FourierIntegral.NormalOneHigh

variable {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The actual normalized WKB substitution. At band `j`, its first parameter
is `μ = (2^j)⁻¹`; the raw inverse frequency is `με`. No chart or measure is
changed (`app:ch_waves:eq:phase-quotient`). -/
def normalizedRetainedPoint (μ : ℝ)
    (q : ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) :
    ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) :=
  (μ * q.1, (q.2.2.1,
    (carrierParameters (q.2.1, (inputCoordinates T q.2.2.2).1),
      T.reference.spatialPatch
        (carrierParameters (q.2.1, (inputCoordinates T q.2.2.2).1)) +
          q.1 • (inputCoordinates T q.2.2.2).2)))

/-- The substitution is smooth on the original full-input extension,
including both sides of epsilon zero (`app:ch_waves:setup:oscillatory`). -/
theorem normalizedRetainedPoint_smooth {c C : ℝ} (hP : P.IsValid c C) (M : ℝ) :
    ContDiffOn ℝ ∞ (fun w : ℝ ×
      (ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) ↦
      normalizedRetainedPoint T w.1 w.2)
      (univ ×ˢ (univ ×ˢ tripleDomain T M)) := by
  have hz : ContDiffOn ℝ ∞
      (fun w : ℝ × (ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) ↦
        T.reference.spatialPatch
          (carrierParameters (w.2.2.1, (inputCoordinates T w.2.2.2.2).1)))
      (univ ×ˢ (univ ×ˢ tripleDomain T M)) := by
    apply (T.reference.spatialPatch_smooth hP).comp (by fun_prop)
    intro w hw
    exact (middle_parameter_buffers hP).2 (fun i ↦ (hw.2.2.2.1 i).le)
  unfold normalizedRetainedPoint
  exact ContDiffOn.prodMk (by fun_prop)
    (ContDiffOn.prodMk (by fun_prop)
      (ContDiffOn.prodMk (by fun_prop) (hz.add (by fun_prop))))

/-- Every substitution jet is bounded before the current immersion, raw
fields, scalar, band label and history scale. Incidence is differentiated;
this is not a fixed-carrier bound (`app:ch_waves:setup:oscillatory`). -/
theorem exists_normalizedRetainedPoint_jet_bounds {c C : ℝ} (hP : P.IsValid c C)
    (M e : ℝ)
    {H : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))}
    (hH : IsCompact H) (hHM : H ⊆ tripleDomain T M) :
    ∃ b : ℕ → ℝ, (∀ j, 0 ≤ b j) ∧
      ∀ μ ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (-e) e ×ˢ H, ∀ j,
        ‖iteratedFDeriv ℝ j (normalizedRetainedPoint T μ) q‖ ≤ b j := by
  have hb (j : ℕ) : ∃ b : ℝ, ∀ μ ∈ Icc (0 : ℝ) 1,
      ∀ q ∈ Icc (-e) e ×ˢ H,
        ‖iteratedFDeriv ℝ j (normalizedRetainedPoint T μ) q‖ ≤ b := by
    have hc : ContinuousOn (fun w : ℝ ×
        (ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))) ↦
        iteratedFDeriv ℝ j (normalizedRetainedPoint T w.1) w.2)
        (Icc (0 : ℝ) 1 ×ˢ (Icc (-e) e ×ˢ H)) := by
      intro w hw
      exact (NormalComparison.contDiffAt_segmentSpatialJet
        ((normalizedRetainedPoint_smooth T hP M).contDiffAt
          ((isOpen_univ.prod (isOpen_univ.prod (isOpen_tripleDomain T M))).mem_nhds
            ⟨mem_univ _, mem_univ _, hHM hw.2.2⟩)) j).continuousAt.continuousWithinAt
    obtain ⟨b, hb⟩ := (isCompact_Icc.prod (isCompact_Icc.prod hH)).exists_bound_of_continuousOn hc
    exact ⟨b, fun μ hμ q hq ↦ hb (μ, q) ⟨hμ, hq⟩⟩
  choose b hb using hb
  exact ⟨fun j ↦ max 0 (b j), fun j ↦ le_max_left _ _,
    fun μ hμ q hq j ↦ (hb j μ hμ q hq).trans (le_max_right _ _)⟩

/-- The full normalized pullback preserves the retained polynomial reserve.
The primitive `hf` and `hb` are exactly the supported conclusions of
`exists_retained_measuredPolynomial_budgets`; no normalized jet bound is
assumed. The compact set and constants precede the raw polynomial
(`app:ch_waves:setup:oscillatory`). -/
theorem exists_normalizedRetainedPoint_composition_budgets
    {c C : ℝ} (hP : P.IsValid c C) (M : ℝ) {e : ℝ} (he : e ≤ 1)
    {H : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))}
    (hH : IsCompact H) (hHM : H ⊆ tripleDomain T M)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (f : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
        EuclideanSpace ℂ (Fin (m + 1))), ContDiff ℝ ∞ f →
      ∀ (L : ℝ) (rpar : ℕ), 1 ≤ L →
      (∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w, ∀ j,
        ‖iteratedFDeriv ℝ j f (τ, w)‖ ≤ A j * L ^ (j - rpar)) →
      ∀ j, ∀ q ∈ Icc (-e) e ×ˢ H, ∀ k,
        ‖iteratedFDeriv ℝ k (f ∘ normalizedRetainedPoint T ((2 : ℝ) ^ j)⁻¹) q‖ ≤
          B k * L ^ (k - rpar) := by
  obtain ⟨b, hb, hsub⟩ := exists_normalizedRetainedPoint_jet_bounds T hP M e hH hHM
  refine ⟨compositionBudget A b, compositionBudget_nonneg hA hb, ?_⟩
  intro f hf L rpar hL hfjet j q hq k
  have hμ : ((2 : ℝ) ^ j)⁻¹ ∈ Icc (0 : ℝ) 1 := by
    exact ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))⟩
  have hτ : (normalizedRetainedPoint T ((2 : ℝ) ^ j)⁻¹ q).1 ∈ Icc (-1 : ℝ) 1 := by
    change ((2 : ℝ) ^ j)⁻¹ * q.1 ∈ Icc (-1 : ℝ) 1
    have hε : |q.1| ≤ 1 := (abs_le.mpr hq.1).trans he
    apply abs_le.mp
    rw [abs_mul, abs_of_nonneg hμ.1]
    exact (mul_le_mul hμ.2 hε (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hs : ContDiffOn ℝ ∞ (normalizedRetainedPoint T ((2 : ℝ) ^ j)⁻¹)
      (univ ×ˢ tripleDomain T M) :=
    (normalizedRetainedPoint_smooth T hP M).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun q hq ↦ ⟨mem_univ _, hq⟩)
  exact norm_iteratedFDeriv_comp_le_sliceGrade
    (hs.contDiffAt ((isOpen_univ.prod (isOpen_tripleDomain T M)).mem_nhds
      ⟨mem_univ _, hHM hq.2⟩)) hf.contDiffAt
    (fun i _ ↦ hA i) hL
    (fun i _ ↦ hfjet _ hτ _ i) (fun i _ _ ↦ hsub _ hμ q hq i)

/-- The actual carrier refinement has margin `ρ/4`. A covector displacement
of size at most `ρ/4` and the original physical cutoff therefore stay in the
`ρ/2` plateau. This also applies at epsilon zero
(`app:ch_waves:eq:individual-representation`). -/
theorem normalizedRetainedPoint_mem_plateau
    {a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))} {ρ : ℝ}
    {z : Euclidean 3} {x : Euclidean (m + 1)} {θ : Euclidean (m + 1 - 1)} {ε : ℝ}
    (hx : x ∈ closedBall a.1 (ρ / 2))
    (hz : (z, T.reference.spatialPatch z) ∈ closedBall a.2 (ρ / 4))
    (hθ : ‖θ‖ ≤ 2) (hε : |ε| ≤ ρ / 8) :
    (x, (z, T.reference.spatialPatch z + ε • θ)) ∈ closedBall a (ρ / 2) := by
  rw [← closedBall_prod_same] at hz ⊢
  refine ⟨hx, ?_⟩
  rw [← closedBall_prod_same]
  have hρ : 0 ≤ ρ := by linarith [abs_nonneg ε]
  refine ⟨closedBall_subset_closedBall (by linarith) hz.1, ?_⟩
  rw [mem_closedBall_iff_norm]
  have hzξ := mem_closedBall_iff_norm.mp hz.2
  calc
    ‖T.reference.spatialPatch z + ε • θ - a.2.2‖ =
        ‖(T.reference.spatialPatch z - a.2.2) + ε • θ‖ := by congr 1; abel
    _ ≤ ‖T.reference.spatialPatch z - a.2.2‖ + ‖ε • θ‖ := norm_add_le _ _
    _ ≤ ρ / 4 + (ρ / 8) * 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add hzξ (mul_le_mul hε hθ (norm_nonneg _) (by linarith))
    _ = ρ / 2 := by ring

end JanetCartan.Sampling.MeasuredAmplitude
