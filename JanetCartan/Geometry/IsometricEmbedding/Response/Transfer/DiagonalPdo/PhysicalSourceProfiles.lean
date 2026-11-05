module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.HistoryPhaseProfiles

/-!
# Physical source phases with the same extended solver coefficients

The primary atom uses the physical projected stress, whereas the solver uses
its fixed affine extension. Equality of every jet on the original coefficient
ball, including its boundary, transfers the actual history bounds to the
physical source phase. No global equality of these two fields is asserted.

Consumer: the physical-source version of the diagonal elliptic envelope.
Sources: `app:ch_regular:eq:coefficient-extension`,
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DiagonalPdo
open GeometricProfile ProtectedFlow CurrentCoefficientProfiles RetainedFactors
open ActualCarriers FrozenMenu CurrentFullPhase CompatibleResponse
open LeadingWave.FullModulation

/-- The actual affine frame extension preserves every ambient jet on the
original closed coefficient ball, including the boundary. Its C-seminorm on
any subset of that ball is therefore unchanged. This supplies the physical
source-phase budget for the same extended solver
(`app:ch_regular:eq:coefficient-extension`). -/
theorem cNorm_affineFrameExtension_on_subset {n : ℕ}
    (ext : BallExtension.Parameters (Euclidean n))
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hball : closedBall ext.center ext.radius ⊆ U)
    (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U)
    {K : Set (Euclidean n)} (hK : K ⊆ closedBall ext.center ext.radius) (m : ℕ) :
    cNorm K m (affineFrameExtension ext Q) = cNorm K m Q := by
  have hext := contDiff_affineFrameExtension ext (hQ.mono hball)
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Set.image_congr
  intro y hy
  have he := (affineFrameExtension_eqOn ext Q).iteratedFDerivWithin (𝕜 := ℝ) j (hK hy)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv ext.uniqueDiffOn_closedBall
    (hext.contDiffAt.of_le (by simp)) (hK hy),
    iteratedFDerivWithin_eq_iteratedFDeriv ext.uniqueDiffOn_closedBall
      ((hQ.contDiffAt (hU.mem_nhds (hball (hK hy)))).of_le (by simp)) (hK hy)] at he
  exact congrArg norm he

variable {d : ℕ} {P : Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d

/-- Apply the SAME extended coefficient history profiles to the actual
physical source phase. Only containment of its original frame ball in the
extension ball is required; the two varying fields are never identified
globally. The original coefficient order `m+1` and reserve `Rstar+3` are
unchanged (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_admissible_history_physical_fullSource_phase_profiles
    (T : PatchQuantitativeFamily P U hU) (i : Fin (d+1))
    {KP : Set (E × Par)} (hKP : IsCompact KP)
    (hKD : ∀ q ∈ KP, ((primaryCoordinateChange i).symm q.1,q.2.2) ∈ phaseDomain T)
    (G : FlatReference (d+1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    (hballU : closedBall ext.center ext.radius ⊆ U)
    (hstate : closedBall (0 : E) T.data.localReference.stateRadius ⊆
      closedBall ext.center ext.radius)
    {rStar Rstar kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : Rstar + 3 ≤ rStar)
    (horder : displacementLoss (d+1) + bandExponent * ((rStar : ℝ) + ((d+1 : ℕ) : ℝ)/2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ A : ℕ → ℝ, (∀ j, 0 ≤ A j) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (n : ℕ) (u : Fin n → Torus (d+1) → Euclidean (embeddingDimension (d+1)))
        (ell : Fin n → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ Q, Q.1 = ProjectedStressFrame.projectedStress (finiteHistoryMap G.map u) →
      ∀ j, cNorm KP j (Function.uncurry (T.fullSourcePhaseInCoordinates i Q)) ≤
        A j * currentCoefficientScale R₀ n ^ (j-Rstar) := by
  obtain ⟨S,hS,AQ,_,hAQ,_,hcoeff⟩ :=
    exists_admissible_history_retained_coefficient_profiles G hr hrR hR ext
      hextcenter hextradius hStar (reserve := Rstar+1) (by omega) horder
  obtain ⟨B,hB,hphase⟩ := T.exists_fullSourcePhaseInCoordinates_frame_bound i hKP hKD
  refine ⟨S,hS,fun j ↦ B j * (1+AQ (j+1)),
    fun j ↦ mul_nonneg (hB j).le (by linarith [hAQ (j+1)]),?_⟩
  intro R₀ hR₀ n u ell hu Q hQ j
  have hL := one_le_currentCoefficientScale (by linarith : 1 ≤ R₀) n
  have he : cNorm (closedBall (0 : E) T.data.localReference.stateRadius) (j+1) Q.1 =
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) (j+1)
        (extendedProjectedStress ext (finiteHistoryMap G.map u)) := by
    rw [← cNorm_affineFrameExtension_on_subset ext hU hballU Q.1 Q.property.1 hstate (j+1),hQ]
    rfl
  have hc := ((hcoeff R₀ hR₀ n u ell hu).2.2
    (closedBall (0 : E) T.data.localReference.stateRadius) (isCompact_closedBall _ _)).1 (j+1)
  have hframe : cNorm (closedBall (0 : E) T.data.localReference.stateRadius) (j+1) Q.1 ≤
      AQ (j+1) * currentCoefficientScale R₀ n ^ (j-Rstar) := by
    rw [he]
    simpa only [show j+1-(Rstar+1) = j-Rstar by omega] using hc
  apply (hphase Q j).trans
  have h1 := one_le_pow₀ hL (n := j-Rstar)
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 hframe) (hB j).le]

end JanetCartan.ResponseTransfer.DiagonalPdo
