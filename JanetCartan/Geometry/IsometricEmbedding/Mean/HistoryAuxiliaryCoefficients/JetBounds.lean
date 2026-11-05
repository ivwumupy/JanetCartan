module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.FieldBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.JetFormula

/-!
# One-high bounds for the actual auxiliary coefficients

The coefficients in `app:ch_background:eq:bg-Vaux` and the full induced
connection in `app:ch_background:prop:bg-mixed-physical` are smooth functions
of the second jet. The compact jet range supplies their low bounds; the
closed-ball composition theorem gives the fixed reserve two. The consumers
are the periodic history construction and `auxiliary_rawBand_originalRow_Q0`.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.HistoryAuxiliaryCoefficients

open GeometricProfile ProjectedStressFrame AuxiliaryRawBand

variable {n N : ℕ}

/-- The literal half tangent lift as a jet formula
(`app:ch_background:eq:bg-Vaux`). -/
def secondJetHalfTangent (J : SecondJet (Euclidean n) (Euclidean N)) :
    Euclidean n →L[ℝ] Euclidean N :=
  (1 / 2 : ℝ) • ∑ i, ∑ j,
    ((firstJetMetric J.1)⁻¹ i j • PiLp.proj 2 (fun _ : Fin n ↦ ℝ) j).smulRight
      (J.1 (EuclideanSpace.single i 1))

/-- Identification uses precisely the coefficient in the auxiliary field,
without changing the physical map (`app:ch_background:eq:bg-Vaux`). -/
theorem secondJetHalfTangent_eq (F : Euclidean n → Euclidean N) (x : Euclidean n) :
    secondJetHalfTangent (secondJet F x) = halfTangentCoefficient F x := rfl

private def tensorEntry (i j : Fin n) : MetricTensor n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) j).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) i))

/-- Smoothness follows from the actual inverse-metric formula
(`app:ch_background:prop:bg-mixed-physical`). -/
theorem contDiffAt_secondJetHalfTangent
    {J : SecondJet (Euclidean n) (Euclidean N)} (hJ : IsUnit (firstJetMetric J.1)) :
    ContDiffAt ℝ ∞ (@secondJetHalfTangent n N) J := by
  apply contDiffWithinAt_clm_apply.mpr
  intro v
  have he : (fun K : SecondJet (Euclidean n) (Euclidean N) ↦ secondJetHalfTangent K v) =
      (fun K ↦ (1 / 2 : ℝ) • ∑ i, ∑ j,
        ((firstJetMetric K.1)⁻¹ i j * v j) • K.1 (EuclideanSpace.single i 1)) := by
    funext K
    simp [secondJetHalfTangent]
  rw [he]
  apply ContDiffAt.smul (contDiffAt_const (c := (1 / 2 : ℝ)))
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (((tensorEntry i j).contDiff.contDiffAt.comp J
    ((contDiffAt_firstJetMetric_inv hJ).comp J contDiffAt_fst)).mul
      contDiffAt_const).smul (contDiffAt_fst.clm_apply contDiffAt_const)

/-- Actual local smoothness of the half tangent coefficient
(`app:ch_background:eq:bg-Vaux`). -/
theorem contDiffOn_halfTangentCoefficient {F : Euclidean n → Euclidean N}
    (hF : ContDiff ℝ ∞ F) {U : Set (Euclidean n)} (hi : IsImmersionOn F U) :
    ContDiffOn ℝ ∞ (halfTangentCoefficient F) U := by
  intro x hx
  exact ((contDiffAt_secondJetHalfTangent
    (firstJetMetric_isUnit_of_injective (hi x hx))).comp x
      (contDiff_secondJet hF).contDiffAt).contDiffWithinAt

/-- Actual local smoothness of the full connection coefficient
(`app:ch_background:prop:bg-mixed-physical`). -/
theorem contDiffOn_christoffel {F : Euclidean n → Euclidean N}
    (hF : ContDiff ℝ ∞ F) {U : Set (Euclidean n)} (hi : IsImmersionOn F U)
    (i j k : Fin n) : ContDiffOn ℝ ∞ (fun x ↦ christoffel F x i j k) U := by
  have he : (fun J ↦ secondJetChristoffel J i j k) ∘ secondJet F =
      (fun x ↦ christoffel F x i j k) := by
    funext x
    exact secondJetChristoffel_eq hF x i j k
  rw [← he]
  intro x hx
  exact ((contDiffAt_secondJetChristoffel
    (firstJetMetric_isUnit_of_injective (hi x hx)) i j k).comp x
      (contDiff_secondJet hF).contDiffAt).contDiffWithinAt

/-- The exact auxiliary coefficient norm needed by the periodic construction
for `app:ch_background:prop:bg-mixed-physical`. -/
def physicalAuxiliaryCoefficientNorm (K : Set (Euclidean n)) (m : ℕ)
    (F : Euclidean n → Euclidean N) : ℝ :=
  cNorm K m (halfTangentCoefficient F) +
    ∑ i, ∑ j, ∑ k, cNorm K m (fun x ↦ christoffel F x i j k)

/-- One high map norm, with reserve exactly two, controls the half tangent
lift and every Christoffel coefficient (`app:ch_background:eq:bg-Vaux-tame`).
The range is supplied for actual histories by
`CurrentCoefficientProfiles.exists_admissible_history_jet_range`. -/
theorem exists_physicalAuxiliaryCoefficientNorm_le
    (a : Euclidean n) {r : ℝ} (hr : 0 < r)
    {L : Set (StressJet n N)} (hL : IsCompact L)
    (hu : ∀ J ∈ L, IsUnit (jetMetric J)) (m : ℕ) :
    ∃ C > 0, ∀ F : Euclidean n → Euclidean N, ContDiff ℝ ∞ F →
      Set.MapsTo (stressJet F) (Metric.closedBall a r) L →
      physicalAuxiliaryCoefficientNorm (Metric.closedBall a r) m F ≤
        C * (1 + cNorm (Metric.closedBall a r) (m + 2) F) := by
  have hinv (J) (hJ : J ∈ L) : IsUnit (firstJetMetric J.1) :=
    firstJetMetric_isUnit_of_injective (J.1.adjoint_comp_self_injective_iff.mp
      (ContinuousLinearMap.isUnit_iff_bijective.mp (hu J hJ)).1)
  obtain ⟨A, hA, hraise⟩ := exists_cNorm_secondJet_comp_le_closedBall a hr hL
    (fun J hJ ↦ (contDiffAt_secondJetHalfTangent (hinv J hJ)).of_le
      (by simp : (m : ℕ∞ω) ≤ ∞))
  choose B hB hconnection using fun i j k : Fin n ↦
    exists_cNorm_secondJet_comp_le_closedBall a hr hL
      (fun J hJ ↦ (contDiffAt_secondJetChristoffel (hinv J hJ) i j k).of_le
        (by simp : (m : ℕ∞ω) ≤ ∞))
  refine ⟨A + ∑ i, ∑ j, ∑ k, B i j k, add_pos_of_pos_of_nonneg hA
    (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      Finset.sum_nonneg fun k _ ↦ (hB i j k).le), ?_⟩
  intro F hF hFL
  have hc (i j k : Fin n) :
      cNorm (Metric.closedBall a r) m (fun x ↦ christoffel F x i j k) ≤
        B i j k * (1 + cNorm (Metric.closedBall a r) (m + 2) F) := by
    simpa only [Function.comp_def, secondJetChristoffel_eq hF] using
      hconnection i j k F hF hFL
  have hb := add_le_add (hraise F hF hFL)
    (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
      Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦
        Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) ↦ hc i j k)
  simpa only [physicalAuxiliaryCoefficientNorm, Function.comp_def, secondJetHalfTangent_eq,
    ← Finset.sum_mul, ← add_mul] using hb

end JanetCartan.HistoryAuxiliaryCoefficients
