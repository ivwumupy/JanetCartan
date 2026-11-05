module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.ForwardRegularized
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.ReverseRegularized
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Iteration

/-!
# Finite weak derivative expansions for nonlinear graphs and literal adjoints

The actual compact-frequency source and output integration-by-parts identities,
followed by distributional convergence and finite induction, prove
`app:ch_regular_base:eq:graph-derivative-transfer`. The shared finite sum is
`fullAmplitudeDerivativeTerms`; all physical masks remain in its amplitudes.

`graph_realization_weak_derivative_expansion` handles the forward graph, with the
fixed low-frequency exclusion in its amplitude carrier. The reverse theorem
allows amplitudes smooth away from zero and excludes zero in each regularizer.
`adjointGraph_realization_weak_derivative_expansion` starts the reverse branches
with the conjugate transpose in the original `(x,y,η)` order and conjugates the
forward regularizers exactly once. Its left side is the literal Hilbert adjoint.

The only operator inputs are supplied bounded L² realizations for the finitely
many branches through the requested derivative order, identified by
`GraphDistributionalRealization` with literal regularized integrals on compact
smooth source tests. No derivative recurrence or high-order estimate is assumed.
These realization premises are owed by `jc-deduce-graph-l2-realization` and
`jc-finite-fio-calculus`. Instantiating them and the geometric hypotheses, and
assembling the quantitative strong estimate, belong to
`jc-deduce-fio-strong-sobolev`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter LineDeriv JanetCartan.Pseudodifferential
open scoped ContDiff SchwartzMap Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The finite weak expansion for the actual nonlinear forward graph. Both
physical masks and every datum derivative are retained. The compact-frequency
pairing and coefficient-closure premises of the abstract iteration are proved
from primitive smoothness, homogeneity and support assumptions here.

The realization premise specifies the normalized Lebesgue kernels and complex
Hilbert outputs explicitly through `GraphDistributionalRealization`. The phase
need only be smooth away from zero; the closed frequency carrier implements the
fixed low-frequency exclusion in Step 3. No mixed inverse is needed in this
direction. Consumed by the strong forward Sobolev estimate.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graph_realization_weak_derivative_expansion
    {X Y F : Set E} (hX : IsCompact X) (hY : IsCompact Y)
    (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hhom : ∀ x η, η ≠ 0 → ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S z (t • η)) =ᶠ[𝓝 x] (fun z ↦ t * S z η))
    (χ : ℕ → E → ℂ) (hχ : ∀ k, ContDiff ℝ ∞ (χ k))
    (hχs : ∀ k, HasCompactSupport (χ k))
    (T : FullAmplitude n r → H →L[ℂ] H)
    (A : FullAmplitude n r) (hA : ForwardAmplitudeAdmissible X Y F A)
    (u : graphTestSpace n r) (is : List (Fin n))
    (hreal : ∀ js : List (Fin n), js.length ≤ is.length →
      ∀ p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S) (graphTransferDatum S) A js,
        GraphDistributionalRealization (graphOperator S) χ p.1 (T p.1)) :
    orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (T A (graphTestToLp u) : 𝓢'(E, V)) =
      ((fullAmplitudeDerivativeTerms (graphTransferRemainder S) (graphTransferDatum S) A is).map
        fun p ↦ (T p.1 (graphTestToLp (orderedTransferAction graphTestPartialDeriv p.2 u)) :
          𝓢'(E, V))).sum := by
  apply fullAmplitudeDerivativeTerms_expansion_of_branch_realizations
    (graphOperator S) χ (graphTransferRemainder S) (graphTransferDatum S) T
    (ForwardAmplitudeAdmissible X Y F) _ _ _ A hA u is hreal
  · intro i B hB
    exact hB.graphTransferRemainder hX.isClosed hY.isClosed hF hF0 S hS i
  · intro i j B hB
    exact hB.graphTransferDatum hF hF0 S hS i j
  · intro B hB k i v φ
    exact graphOperator_frequencyCut_weak_pairing hB hX hY hF hF0 hS hhom
      (χ k) (hχ k) (hχs k) i v φ

/-- The finite weak expansion for the literal reverse phase. The initial `C`
is already a reverse amplitude, and no branch is conjugated during iteration.
The inverse coefficients are those of the actual mixed phase matrix. Their
smoothness and the derivative of the entire inverse-weighted amplitude follow
from the phase hypotheses and the determinant gap on the physical support.

Only distributional realization of the normalized frequency-regularized kernels
is an operator premise. Consumed by the literal-adjoint theorem below and the
strong Sobolev estimate. Source: `app:ch_regular_base:eq:actual-adjoint-trade`
and `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem reverseGraph_realization_weak_derivative_expansion
    {K : Set (E × E)} (hK : IsCompact K) (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hinv : ∀ p ∈ K, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S p.1 η).det)
    (hhom : ∀ p ∈ K, ∀ η, η ≠ 0 → ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S z (t • η)) =ᶠ[𝓝 p.1] (fun z ↦ t * S z η))
    (χ : ℕ → E → ℂ) (hχ : ∀ k, ContDiff ℝ ∞ (χ k))
    (hχs : ∀ k, HasCompactSupport (χ k)) (hχ0 : ∀ k, (0 : E) ∉ tsupport (χ k))
    (T : FullAmplitude n r → H →L[ℂ] H)
    (C : FullAmplitude n r) (hC : ReverseAmplitudeAdmissible K C)
    (u : graphTestSpace n r) (is : List (Fin n))
    (hreal : ∀ js : List (Fin n), js.length ≤ is.length →
      ∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S) (adjointTransferDatum S) C js,
        GraphDistributionalRealization (reverseGraphOperator S) χ p.1 (T p.1)) :
    orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (T C (graphTestToLp u) : 𝓢'(E, V)) =
      ((fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
        (adjointTransferDatum S) C is).map fun p ↦
        (T p.1 (graphTestToLp (orderedTransferAction graphTestPartialDeriv p.2 u)) :
          𝓢'(E, V))).sum := by
  apply fullAmplitudeDerivativeTerms_expansion_of_branch_realizations
    (reverseGraphOperator S) χ (adjointTransferRemainder S) (adjointTransferDatum S) T
    (ReverseAmplitudeAdmissible K) _ _ _ C hC u is hreal
  · intro i B hB
    exact hB.adjointTransferRemainder S hS hinv i
  · intro i j B hB
    exact hB.adjointTransferDatum S hS hinv i j
  · intro B hB k i v φ
    exact reverseGraphOperator_frequencyCut_weak_pairing hB hK S hS hinv hhom
      (χ k) (hχ k) (hχs k) (hχ0 k) i v φ

/-- Conjugate transposition preserves the primitive admissibility conditions in
original coordinates. Used only to initialize the literal-adjoint expansion.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem ReverseAmplitudeAdmissible.conjTranspose
    {K : Set (E × E)} {A : FullAmplitude n r} (hA : ReverseAmplitudeAdmissible K A) :
    ReverseAmplitudeAdmissible K (fun x y η ↦ (A x y η).conjTranspose) := by
  refine ⟨fun p hp ↦ (starL ℝ : Matrix (Fin r) (Fin r) ℂ ≃L[ℝ]
    Matrix (Fin r) (Fin r) ℂ).contDiff.contDiffAt.comp p (hA.smooth p hp), ?_⟩
  apply Set.Subset.trans _ hA.support
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  apply subset_tsupport
  intro hz
  exact hp (by simp [hz])

/-- Two supplied realizations of the same literal regularized kernels agree as
distributions on compact smooth source tests, by uniqueness of their limits.
This identifies the initial reverse branch with the supplied Hilbert adjoint;
it is not assumed as an operator equality.
Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem GraphDistributionalRealization.eq_on_tests
    {K : FullAmplitude n r → (E → Fin r → ℂ) → E → Fin r → ℂ}
    {χ : ℕ → E → ℂ} {A : FullAmplitude n r} {T U : H →L[ℂ] H}
    (hT : GraphDistributionalRealization K χ A T)
    (hU : GraphDistributionalRealization K χ A U) (u : graphTestSpace n r) :
    (T (graphTestToLp u) : 𝓢'(E, V)) = (U (graphTestToLp u) : 𝓢'(E, V)) := by
  ext φ : 1
  exact tendsto_nhds_unique (hT u φ) (hU u φ)

/-- Finite weak derivatives of the literal Hilbert adjoint `U.adjoint`. The
reverse coefficients start at `A(x,y,η).conjTranspose` in original coordinate
order, and every later branch uses the same reverse transfer without further
conjugation. Complex regularizers are conjugated exactly once.

`hreal` supplies low L² realizations only of the finitely many modified reverse
amplitudes through the requested order; `hadjoint` identifies the literal Hilbert adjoint itself with the initial
regularized reverse kernel. Both are precise distributional-limit premises,
produced by the graph realization and finite-calculus tasks. Equality with the
initial branch is deduced by uniqueness of limits. The parent strong Sobolev
assembly must instantiate these premises and the geometric data.
Source: `app:ch_regular_base:eq:actual-adjoint-trade` and
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem adjointGraph_realization_weak_derivative_expansion
    {K : Set (E × E)} (hK : IsCompact K) (S : E → E → ℝ)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hinv : ∀ p ∈ K, ∀ η, η ≠ 0 → IsUnit (mixedPhaseMatrix S p.1 η).det)
    (hhom : ∀ p ∈ K, ∀ η, η ≠ 0 → ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S z (t • η)) =ᶠ[𝓝 p.1] (fun z ↦ t * S z η))
    (χ : ℕ → E → ℂ) (hχ : ∀ k, ContDiff ℝ ∞ (χ k))
    (hχs : ∀ k, HasCompactSupport (χ k)) (hχ0 : ∀ k, (0 : E) ∉ tsupport (χ k))
    (T : FullAmplitude n r → H →L[ℂ] H)
    (A : FullAmplitude n r) (hA : ReverseAmplitudeAdmissible K A) (U : H →L[ℂ] H)
    (hadjoint : GraphDistributionalRealization (reverseGraphOperator S)
      (fun k η ↦ star (χ k η)) (fun x y η ↦ (A x y η).conjTranspose) U.adjoint)
    (u : graphTestSpace n r) (is : List (Fin n))
    (hreal : ∀ js : List (Fin n), js.length ≤ is.length →
      ∀ p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S) (adjointTransferDatum S)
        (fun x y η ↦ (A x y η).conjTranspose) js,
        GraphDistributionalRealization (reverseGraphOperator S)
          (fun k η ↦ star (χ k η)) p.1 (T p.1)) :
    orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (U.adjoint (graphTestToLp u) : 𝓢'(E, V)) =
      ((fullAmplitudeDerivativeTerms (adjointTransferRemainder S) (adjointTransferDatum S)
        (fun x y η ↦ (A x y η).conjTranspose) is).map fun p ↦
        (T p.1 (graphTestToLp (orderedTransferAction graphTestPartialDeriv p.2 u)) :
          𝓢'(E, V))).sum := by
  have hinit := hreal [] (Nat.zero_le _) ((fun x y η ↦ (A x y η).conjTranspose), [])
    (List.mem_singleton_self _)
  rw [← hinit.eq_on_tests hadjoint u]
  apply reverseGraph_realization_weak_derivative_expansion hK S hS hinv hhom
    (fun k η ↦ star (χ k η)) (fun k ↦ (starL ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp (hχ k))
    _ _ T _ hA.conjTranspose u is hreal
  · intro k
    exact (hχs k).comp_left (star_zero _)
  · intro k
    apply fun hm ↦ hχ0 k ((tsupport_comp_subset (g := star) (star_zero _) _) hm)

end JanetCartan.FourierIntegral
