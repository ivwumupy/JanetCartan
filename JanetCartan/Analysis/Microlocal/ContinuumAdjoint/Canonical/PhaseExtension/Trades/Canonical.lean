module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Trades.Fields
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Supported

/-!
# Agreement with the actual canonical mixed phase matrix

The extended position's spatial matrix is the published canonical mixed phase
matrix wherever the actual phase is smooth and the extension agrees on a
neighborhood. On the cutoff plateau this identifies the literal Gram formula
with `Canonical.phaseLeftInverse`. These comparisons feed the canonical
instantiation of the scalar transport endpoint.

Source: `app:ch_background:eq:bg-derivative-trade`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter Matrix
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts

variable {n : ℕ}

/-- Neighborhood agreement preserves the full spatial matrix, as needed for the
supported extension in `app:ch_background:eq:bg-derivative-trade`. -/
theorem spatialMatrix_eq_of_eventuallyEq
    {Y₁ Y₂ : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {x : Euclidean n} {z : CarrierParameter} (hY : Y₁ =ᶠ[𝓝 (x, z)] Y₂) :
    spatialMatrix Y₁ z x = spatialMatrix Y₂ z x := by
  have he := (hY.comp_tendsto
    (continuousAt_id.prodMk continuousAt_const).tendsto).fderiv_eq (𝕜 := ℝ)
  ext i j
  exact congrArg (fun D : Euclidean n →L[ℝ] Euclidean (n - 1) ↦
    (D (EuclideanSpace.single i 1)) j) he

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The transpose of `D_x Y` for the literal transported position equals the
actual canonical mixed phase matrix on the published phase ball
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem spatialMatrix_transportPosition_eq_phaseMatrix
    (z : CarrierParameter) (x : Euclidean n)
    (h : (CanonicalCarrier.physicalCoordinates T x,
      T.reference.spatialPatch (CanonicalCarrier.parameter z)) ∈
        ball (0, ActualPhase.covectorCenter T) (2 * T.family.radius)) :
    spatialMatrix (CanonicalCarrier.transportPosition T Q) z x = phaseMatrix T Q z x := by
  have hd : ContDiffAt ℝ ∞
      (fun y ↦ fderiv ℝ (hamiltonPhase T Q y)
        (T.reference.spatialPatch (CanonicalCarrier.parameter z))) x :=
    (hamiltonPhase_contDiffAt T Q h).fderiv contDiffAt_const (by simp)
  have hg := (InnerProductSpace.toDual ℝ (Euclidean (n - 1))).symm.contDiff.contDiffAt.comp x hd
  have hY : DifferentiableAt ℝ (fun y ↦ CanonicalCarrier.transportPosition T Q (y, z)) x := by
    have he : (fun y ↦ CanonicalCarrier.transportPosition T Q (y, z)) =
        (fun y ↦ gradient (hamiltonPhase T Q y)
          (T.reference.spatialPatch (CanonicalCarrier.parameter z))) := by
      funext y
      exact CanonicalCarrier.transportPosition_eq_hamiltonGradient T Q (y, z)
    rw [he]
    exact hg.differentiableAt (by simp)
  ext i j
  have he := partialDeriv_transportPhase_physical T Q z x h (EuclideanSpace.single j 1) i
  change fderiv ℝ (fun y ↦ phase (CanonicalCarrier.transportPosition T Q) z y
    (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) = _ at he
  rw [fderiv_phase_spatial hY] at he
  simpa [spatialMatrix, EuclideanSpace.inner_single_right, Matrix.mulVec, dotProduct,
    EuclideanSpace.single] using he

/-- Transfer the canonical matrix identity through neighborhood agreement,
without assuming an inverse identity (`app:ch_background:eq:bg-derivative-trade`). -/
theorem spatialMatrix_eq_phaseMatrix_of_eventuallyEq
    {Y : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {z : CarrierParameter} {x : Euclidean n}
    (hY : Y =ᶠ[𝓝 (x, z)] CanonicalCarrier.transportPosition T Q)
    (h : (CanonicalCarrier.physicalCoordinates T x,
      T.reference.spatialPatch (CanonicalCarrier.parameter z)) ∈
        ball (0, ActualPhase.covectorCenter T) (2 * T.family.radius)) :
    spatialMatrix Y z x = phaseMatrix T Q z x :=
  (spatialMatrix_eq_of_eventuallyEq hY).trans
    (spatialMatrix_transportPosition_eq_phaseMatrix T Q z x h)

/-- The same Gram formula is the published canonical left inverse wherever the
extension agrees locally (`app:ch_background:eq:bg-derivative-trade`). -/
theorem transverseLeftInverse_eq_phaseLeftInverse_of_eventuallyEq
    {Y : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {z : CarrierParameter} {x : Euclidean n}
    (hY : Y =ᶠ[𝓝 (x, z)] CanonicalCarrier.transportPosition T Q)
    (h : (CanonicalCarrier.physicalCoordinates T x,
      T.reference.spatialPatch (CanonicalCarrier.parameter z)) ∈
        ball (0, ActualPhase.covectorCenter T) (2 * T.family.radius)) :
    transverseLeftInverse (spatialMatrix Y z x) = phaseLeftInverse T Q z x := by
  rw [spatialMatrix_eq_phaseMatrix_of_eventuallyEq T Q hY h]
  rfl

/-- The published extension domain lies in the actual phase-smoothness ball.
This discharges the phase-domain premise of the supported matrix comparison,
using the actual covector buffer (`app:ch_background:eq:bg-derivative-trade`). -/
theorem phasePoint_mem_ball_of_mem_extensionDomain {c C : ℝ} (hP : P.IsValid c C)
    {x : Euclidean n} {z : CarrierParameter} (hp : (x, z) ∈ extensionDomain T) :
    (CanonicalCarrier.physicalCoordinates T x,
      T.reference.spatialPatch (CanonicalCarrier.parameter z)) ∈
        ball (0, ActualPhase.covectorCenter T) (2 * T.family.radius) := by
  have hx : x ∈ ball 0 T.family.radius := by
    apply ball_subset_ball (show T.physicalRadius ≤ T.family.radius from ?_) hp.1
    have hpos := T.physicalRadius_pos
    dsimp [PatchQuantitativeFamily.physicalRadius] at hpos ⊢
    linarith [min_le_left T.family.radius (3 * T.family.sourceRadius)]
  have hx' : CanonicalCarrier.physicalCoordinates T x ∈ ball 0 T.family.radius := by
    simpa only [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
  have hz : T.reference.spatialPatch (CanonicalCarrier.parameter z) ∈
      ball (ActualPhase.covectorCenter T) T.family.radius := by
    obtain ⟨ε, hε, hshift⟩ :=
      ActualPhase.exists_covector_shift_buffer T hP (by norm_num : (0 : ℝ) < 1)
    have hh := hshift (CanonicalCarrier.parameter z) (fun i ↦ (hp.2 i).le)
      0 (by simp) 0 (by simpa using hε.le) 0 (by constructor <;> norm_num)
    simpa only [zero_mul, zero_smul, add_zero] using hh
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  exact ⟨(mem_ball.mp hx').trans (by linarith [T.family.radius_pos]),
    (mem_ball.mp hz).trans (by linarith [T.family.radius_pos])⟩

/-- On the COMPLETE supported chart the plateau extension has the canonical
mixed matrix. The domain inclusion is supplied by
`supportedChart_subset_extensionDomain`, and the plateau by
`exists_supported_affine_extensions`
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem spatialMatrix_affineExtension_eq_phaseMatrix_on_supportedChart
    {c C : ℝ} (hP : P.IsValid c C)
    (A : Euclidean n →L[ℝ] Euclidean (n - 1))
    {χ : Euclidean n × CarrierParameter → ℝ} {z₀ : Euclidean 3} {a : ℝ}
    (hdomain : supportedChart z₀ a ⊆ extensionDomain T)
    (hplateau : supportedChart z₀ a ⊆ interior {p | χ p = 1})
    {x : Euclidean n} {z : CarrierParameter} (hp : (x, z) ∈ supportedChart z₀ a) :
    spatialMatrix (affineExtension A χ (CanonicalCarrier.transportPosition T Q)) z x =
      phaseMatrix T Q z x :=
  spatialMatrix_eq_phaseMatrix_of_eventuallyEq T Q
    (affineExtension_eventuallyEq A _ (hplateau hp))
    (phasePoint_mem_ball_of_mem_extensionDomain T hP (hdomain hp))

/-- The literal Gram left inverse of the supported affine extension is exactly
`Canonical.phaseLeftInverse`, for the coefficients in
`app:ch_background:eq:bg-derivative-trade`. No rank-gap or inverse identity is
needed merely to identify the two formulas. -/
theorem transverseLeftInverse_affineExtension_eq_phaseLeftInverse_on_supportedChart
    {c C : ℝ} (hP : P.IsValid c C)
    (A : Euclidean n →L[ℝ] Euclidean (n - 1))
    {χ : Euclidean n × CarrierParameter → ℝ} {z₀ : Euclidean 3} {a : ℝ}
    (hdomain : supportedChart z₀ a ⊆ extensionDomain T)
    (hplateau : supportedChart z₀ a ⊆ interior {p | χ p = 1})
    {x : Euclidean n} {z : CarrierParameter} (hp : (x, z) ∈ supportedChart z₀ a) :
    transverseLeftInverse
        (spatialMatrix (affineExtension A χ (CanonicalCarrier.transportPosition T Q)) z x) =
      phaseLeftInverse T Q z x := by
  rw [spatialMatrix_affineExtension_eq_phaseMatrix_on_supportedChart T Q hP A hdomain hplateau hp]
  rfl

end JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
