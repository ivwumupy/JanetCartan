module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.PhaseTrade
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.Chart
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalPhase

/-!
# The canonical phase in the rectangular derivative API

Identify the actual Hamilton phase and carrier map in the literal adjoint
kernel, and derive its physical derivative from their actual local smoothness.
The rank gap, smooth extensions, and uniform coefficient profiles needed by
`Assembly.ScalarTransport` remain separate construction obligations. In
particular local conic regularity is not asserted to be global regularity.

Source: `app:ch_background:eq:bg-derivative-trade`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open DerivativeKernels

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Restrict the SAME current Hamilton phase to zero energy, in the original
physical coordinates (`app:ch_background:eq:bg-derivative-trade`). -/
def hamiltonPhase (x : Euclidean n) (ζ : Euclidean (n - 1)) : ℝ :=
  HamiltonPhase.phase (T.currentChart Q).coordinates (x, (0, ζ))

/-- The rectangular mixed matrix of the actual canonical carrier
(`app:ch_background:eq:bg-derivative-trade`). -/
def phaseMatrix (z : CarrierParameter) (x : Euclidean n) : TransverseMatrix n :=
  transversePhaseMatrix (hamiltonPhase T Q) x
    (T.reference.spatialPatch (CanonicalCarrier.parameter z))

/-- The Gram formula for the canonical rectangular left inverse. Its
left-inverse property still requires the actual transverse gap
(`app:ch_background:eq:bg-derivative-trade`). -/
def phaseLeftInverse (z : CarrierParameter) (x : Euclidean n) :
    Matrix (Fin (n - 1)) (Fin n) ℝ :=
  transverseLeftInverse (phaseMatrix T Q z x)

/-- The phase used by the literal physical adjoint kernel
(`app:ch_background:eq:bg-T`). -/
def transportPhase (z : CarrierParameter) (x : Euclidean n) (η : Euclidean (n - 1)) : ℝ :=
  inner ℝ (CanonicalCarrier.transportPosition T Q (x,z)) η

/-- The canonical kernel phase is exactly the phase in the proved rectangular
calculus, including the original carrier coordinate map and with no Fourier
rescaling (`app:ch_background:eq:bg-derivative-trade`). -/
theorem transportPhase_eq_transverseTransportPhase
    (z : CarrierParameter) (x : Euclidean n) (η : Euclidean (n - 1)) :
    transportPhase T Q z x η =
      transverseTransportPhase (hamiltonPhase T Q) T.reference.spatialPatch
        x (CanonicalCarrier.parameter z) η := by
  unfold transportPhase
  rw [CanonicalCarrier.transportPosition_eq_hamiltonGradient]
  exact inner_gradient_left

/-- The actual Hamilton producer supplies local smoothness at every point of
its stated phase ball. This is not a global extension assertion
(`app:ch_background:eq:bg-derivative-trade`). -/
theorem hamiltonPhase_contDiffAt {x : Euclidean n} {ζ : Euclidean (n - 1)}
    (h : (CanonicalCarrier.physicalCoordinates T x, ζ) ∈
      ball (0, ActualPhase.covectorCenter T) (2 * T.family.radius)) :
    ContDiffAt ℝ ∞ (Function.uncurry (hamiltonPhase T Q)) (x, ζ) := by
  have he : Function.uncurry (hamiltonPhase T Q) =
      fun p : Euclidean n × Euclidean (n - 1) ↦
        ActualPhase.current T Q (CanonicalCarrier.physicalCoordinates T p.1, p.2) := by
    funext p
    exact (CanonicalCarrier.current_physicalCoordinates T Q p.1 p.2).symm
  rw [he]
  have hmap : ContDiffAt ℝ ∞ (fun p : Euclidean n × Euclidean (n - 1) ↦
      (CanonicalCarrier.physicalCoordinates T p.1, p.2)) (x, ζ) :=
    (((CanonicalCarrier.physicalCoordinates T).contDiff.comp contDiff_fst).contDiffAt.prodMk
      contDiffAt_snd)
  have hc := ((ActualPhase.current_smooth T Q).contDiffAt
    (isOpen_ball.mem_nhds h)).comp (x, ζ) hmap
  exact hc

/-- The literal physical derivative is the actual rectangular mixed matrix
times the initial covector. Its smoothness premise is discharged by the
Hamilton producer on the explicit chart (`app:ch_background:eq:bg-derivative-trade`). -/
theorem partialDeriv_transportPhase_physical
    (z : CarrierParameter) (x : Euclidean n)
    (h : (CanonicalCarrier.physicalCoordinates T x,
      T.reference.spatialPatch (CanonicalCarrier.parameter z)) ∈
        ball (0, ActualPhase.covectorCenter T) (2 * T.family.radius))
    (η : Euclidean (n - 1)) (i : Fin n) :
    partialDeriv (fun y ↦ transportPhase T Q z y η) x i =
      (phaseMatrix T Q z x *ᵥ (fun j ↦ η j)) i := by
  simp_rw [transportPhase_eq_transverseTransportPhase]
  exact partialDeriv_transverseTransportPhase_physical T.reference.spatialPatch
    (CanonicalCarrier.parameter z)
    ((hamiltonPhase_contDiffAt T Q h).of_le (by simp)) η i

/-- The function above is the SAME phase for every actual canonical normal
and scalar; these amplitude choices do not change the phase
(`app:ch_background:eq:bg-T`). -/
theorem carrierChartPhase_data {N : ℕ}
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ) :
    carrierChartPhase (CanonicalCarrier.data T Q F row col Φ Y initial hr hcell angular high) =
      transportPhase T Q := rfl

end JanetCartan.ContinuumAdjoint.Canonical
