module

public import JanetCartan.Analysis.Calculus.PhaseQuotient
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.Frozen
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Literal maps for the full phase comparison

The maps in `app:ch_seed:prop:seed-phase-charts` are built from the published
integral quotient and physical averaged gradient. The physical space is a real
Hilbert space; the full spacetime application uses `WithLp 2 (ℝ × E)`, retaining
the Euclidean norm. The carrier's first argument contains all spectators.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace

namespace JanetCartan.FullPhaseCharts.Comparison

variable {P X E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The literal integral modulation phase, including zero shift, in
`app:ch_seed:eq:seed-quotient-integral`. -/
def modulationPhase (S : X × E → ℝ) (ζ : P × ℝ → E)
    (ε : ℝ) (p : P) (u : ℝ × E) (x : X) : ℝ :=
  phaseShiftQuotient (fun x ξ ↦ S (x, ξ)) x (ζ (p, u.1)) u.2 ε

variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- The actual two-point physical gradient of the integral modulation phase
in `app:ch_seed:prop:seed-phase-charts`. No comparison estimate is stored. -/
def modulationChart (S : X × E → ℝ) (ζ : P × ℝ → E)
    (ε : ℝ) (p : P) (x x' : X) (u : ℝ × E) : X :=
  averagedPhaseGradient (modulationPhase S ζ ε p) u x x'

/-- The reference phase is exactly `t H₀(ξ) + ⟪y, ξ⟫`, as in the comparison
paragraph following `app:ch_seed:eq:seed-quotient-integral`. -/
def referencePhase (H₀ : E → ℝ) (q : WithLp 2 (ℝ × E) × E) : ℝ :=
  q.1.ofLp.1 * H₀ q.2 + ⟪q.1.ofLp.2, q.2⟫_ℝ

/-- The full physical gradient expressed in the time/transverse coordinates
used by `FullPhaseCharts.frozenChart` (`app:ch_seed:prop:seed-phase-charts`). -/
def fullChart (S : WithLp 2 (ℝ × E) × E → ℝ) (ζ : P × ℝ → E)
    (ε : ℝ) (p : P) (x x' : WithLp 2 (ℝ × E)) (u : ℝ × E) : ℝ × E :=
  (modulationChart S ζ ε p x x' u).ofLp

/-- The transverse two-point map at fixed time in
`app:ch_seed:prop:seed-phase-charts`, with its own physical segment. -/
def transverseChart (S : WithLp 2 (ℝ × E) × E → ℝ) (ζ : P × ℝ → E)
    (ε : ℝ) (p : P) (t : ℝ) (y y' : E) (u : ℝ × E) : E :=
  modulationChart (fun q : E × E ↦ S (WithLp.toLp 2 (t, q.1), q.2))
    ζ ε p y y' u

end JanetCartan.FullPhaseCharts.Comparison
