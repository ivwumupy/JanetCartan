module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Phase
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Kernels

/-!
# Factor and localizer interfaces

Literal operators for `app:ch_regular:lem:finite-chain`. The right input symbol
uses the source base, and the left output symbol uses the target base. All
frequencies passed to graph operators are physical; only the proof symbols are
rescaled. These definitions do not assert convergence of unregularized
oscillatory integrals. The final factor estimate must identify the regularized
joint kernels with these compositions and justify their limits.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph
open FourierIntegral

variable {n r : ℕ}

/-- Normalized base/covector symbol of a proof localizer
(`app:ch_regular:lem:finite-chain`). -/
abbrev LocalizerSymbol (n : ℕ) := Euclidean n × Euclidean n → ℝ

/-- Right quantization preserves the input base in
`app:ch_regular:eq:joint-kernel-phase`. -/
def rightLocalizer (ρ : ℝ) (m : LocalizerSymbol n)
    (f : Euclidean n → Fin r → ℂ) : Euclidean n → Fin r → ℂ :=
  graphOperator (fun x ξ => inner ℝ x ξ)
    (fun _ y η => (m (y, ρ⁻¹ • η) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) f

/-- Left quantization preserves the output base in
`app:ch_regular:eq:joint-kernel-phase`. -/
def leftLocalizer (ρ : ℝ) (m : LocalizerSymbol n)
    (f : Euclidean n → Fin r → ℂ) : Euclidean n → Fin r → ℂ :=
  graphOperator (fun x ξ => inner ℝ x ξ)
    (fun x _ ζ => (m (x, ρ⁻¹ • ζ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) f

/-- The discarded forward output retains the identity term in
`app:ch_regular:eq:chain-tail`. For nonintegrable amplitudes, a separate
regularization-limit theorem is required. -/
def forwardLeakage (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (f : Euclidean n → Fin r → ℂ) :
    Euclidean n → Fin r → ℂ :=
  graphOperator S A (rightLocalizer ρ mi f) -
    leftLocalizer ρ mo (graphOperator S A (rightLocalizer ρ mi f))

/-- The literal reverse leakage, in the original amplitude position order
`(u,z,ξ)`, with output `z` (`app:ch_regular:lem:finite-chain`). -/
def reverseLeakage (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (ρ : ℝ) (mi mo : LocalizerSymbol n) (f : Euclidean n → Fin r → ℂ) :
    Euclidean n → Fin r → ℂ :=
  reverseGraphOperator S A (rightLocalizer ρ mi f) -
    leftLocalizer ρ mo (reverseGraphOperator S A (rightLocalizer ρ mi f))

/-- The actual weighted inverse amplitude retains both physical cutoffs and
the frequency cutoff (`app:ch_regular_base:eq:actual-matrix-inverse`). The first
position is the source of the reverse operator. -/
def weightedInverseAmplitude (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) : FullAmplitude n r :=
  fun u z ξ => ((χs z : ℂ) * (χg ξ : ℂ) * (χt u : ℂ)) •
    reverseWeight (phaseJacobian S u ξ) (U u ξ)

/-- The shared literal reverse kernel specializes exactly to the existing
weighted coordinate inverse (`app:ch_regular_base:eq:actual-matrix-inverse`). -/
theorem reverseGraphOperator_weightedInverseAmplitude
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) (f : Euclidean n → Fin r → ℂ) :
    reverseGraphOperator S (weightedInverseAmplitude S U χs χt χg) f =
      weightedReverseGraph S U χs χt χg f := by
  funext z
  simp only [reverseGraphOperator, weightedInverseAmplitude, weightedReverseGraph,
    Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
  simp_rw [show ∀ ξ u, star (graphOscillation S u z ξ) *
      ((χs z : ℂ) * (χg ξ : ℂ) * (χt u : ℂ)) =
      (χs z : ℂ) * ((star (graphOscillation S u z ξ) * (χg ξ : ℂ)) * (χt u : ℂ))
      from fun _ _ => by ring]
  simp only [mul_smul, integral_smul]
  exact smul_comm _ _ _

/-- Five joint integration variables, grouped as two positions and three
normalized physical covectors (`app:ch_regular:eq:joint-kernel-phase`). -/
abbrev JointVariables (E : Type*) := (E × E) × (E × E × E)

/-- The packed phase for both literal orientations. `backward` selects the
inverse relation, not a signed conjugate partner
(`app:ch_regular:eq:joint-kernel-phase`). -/
def jointPhase {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (backward : Bool) (φ : E → E → ℝ) (x y : E) (p : JointVariables E) : ℝ :=
  if backward then reversePhase φ x y p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2
  else forwardPhase φ x y p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2

/-- Full normalized amplitude, including both amplitude positions, source
shoulders, complementary output symbol, and graph/output frequency
regularizers. Neither the graph amplitude nor `1 - mo` is assumed compact in
frequency (`app:ch_regular:lem:finite-chain`). The orientation affects the phase,
not this product, because the reverse amplitude keeps its original positions. -/
def jointAmplitude (ρ : ℝ) (A : FullAmplitude n r) (mi mo : LocalizerSymbol n)
    (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    (p : JointVariables (Euclidean n)) : Matrix (Fin r) (Fin r) ℂ :=
  ((χA (ρ • p.2.1) * χo (ρ • p.2.2.2) *
      (1 - mo (x, p.2.2.2)) * mi (y, p.2.2.1) : ℝ) : ℂ) •
    A p.1.1 p.1.2 (ρ • p.2.1)

end JanetCartan.FiniteChain.Graph
