module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionProtection.Chains
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionProtection.Elapsed
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionProtection.CoordinatePairing

/-!
# Direct evolution and initialized protection

The geometric deduction for `app:ch_regular:thm:no-return` and
`app:ch_regular:lem:finite-chain`, consumed by the direct complete-chain
construction in `ArbitraryAccuracy`.

* `pencilRoot_differential` differentiates the actual common-root identity.
  `normalizedPencil_field_eq_root_velocity` identifies the physical normalized
  pencil field with the direct root velocity multiplied by the nonzero signed
  transverse speed. No positivity convention is imposed on this speed.
* `physicalPencilRootCurve_scaled_ode` proves the corresponding ODE on entire
  root trajectories. `comparisonFamily_preserves_pencilRootSegment` propagates
  the SAME comparison graph by ODE uniqueness with the resulting continuous
  scalar speed; no root-flow preservation premise is used.
* `elapsed_stationary_completePencilRootSegment` identifies the interior
  stationary relation of the actual two-time phase with these segments, in
  either orientation. `elapsed_boundary_physical_diagonal` handles the full
  boundary diagonal. The fixed-transverse retarded operator is not involved.
* `pencilRoot_chain_angular_buffer` transfers the retained angular radius to
  complete direct chains, including changing root patches and elliptic identity
  images. Whole physical/root-domain conditions and nonzero covectors are kept.

The primitive inputs and their actual producers are explicit:

1. `exists_pencilRoot_domain` supplies the open smooth root, nonzero spatial
   covector, literal determinant equation and nonzero transverse derivative.
   Its physical-domain component is automatic for the globally extended frame.
2. `exists_initialized_signed_no_return` supplies the globally smooth extended
   current frame, comparison charts, radius inequalities, characteristic source
   coverage and conic-family angular buffer. The source angular buffer in the
   elliptic case is its already proved characteristic-chain estimate at length
   zero, as checked by `retained_source_angular_buffer` below.
3. `coordinateSplit_inverse_pairing` discharges the exact pairing
   `inner (e.symm u) (e.symm v) = u.1 * v.1 + inner u.2 v.2` for the actual
   `coordinateSplit` selected by `exists_physical_pencil_kernel`.
   `adapted_pairing_of_orthogonal_recombination` also handles a retained
   orthogonal coordinate formula. An arbitrary continuous linear equivalence
   applied identically to bases and covectors is insufficient.
4. The two-time flow constructor supplies the actual ODE, initial condition,
   clock and phase differential. Its entire retained curve must stay in the
   root domain and protected physical ball; endpoint membership is insufficient.

The parent and `RegularSector` still instantiate these inputs at the SAME finite
current coefficient family and its actual physical localizers. This deduction
constructs no replacement reference, coefficient margin or operator estimate,
and is not the unconditional arbitrary-accuracy response theorem.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy
open ProtectedFlow HamiltonPhase

/-- The source buffer needed for the elliptic branch of the direct chain is
already retained by initialized protection, using its length-zero characteristic
chain. No new source margin is assumed or constructed
(`app:ch_regular:thm:no-return`). -/
theorem retained_source_angular_buffer {n : ℕ}
    {H : HomogeneousSymbol (Euclidean n)} {W : Set (Euclidean n)}
    {S : Set (Euclidean n × Euclidean n)} {G : Set (Euclidean n)} {ε : ℝ}
    (hretained : ∀ z ∈ S, ∀ w k,
      PositiveConicChain (CompleteCharacteristicSegment H W) z w k →
      closedBall (normalizedCovector w.2) ε ⊆ G) :
    ∀ z ∈ S, closedBall (normalizedCovector z.2) ε ⊆ G := by
  intro z hz
  exact hretained z hz z 0 (.refl z)

end JanetCartan.ArbitraryAccuracy
