module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveBounds.Geometry

/-!
# Compact support of the exact packed cycle symbol

Joint compactness of the original amplitudes is transported through the actual
forward chart. This supplies the compact-PDO identification input, separately
from the uniform budget (which does not require frequency compactness).
Source: `app:ch_regular_base:eq:actual-normal-amplitude`, actual-calculus Step 1.
-/

@[expose] public noncomputable section
open Set Function
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.LowBounds
open NormalComparison AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The closed original joint carrier for a cross-normal, retaining the common
input covector and both physical positions. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
def jointNormalCarrier (A B : E → E → Mat) : Set (NormalVariables n) :=
  {q | (q.1, q.2.2) ∈ tsupport (uncurry A) ∧ (q.2.1, q.2.2) ∈ tsupport (uncurry B)}

/-- Joint compact support of both original amplitudes implies compactness of
the original cross-normal carrier. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem isCompact_jointNormalCarrier (A B : E → E → Mat)
    (hA : HasCompactSupport (uncurry A)) (hB : HasCompactSupport (uncurry B)) :
    IsCompact (jointNormalCarrier A B) := by
  have hc := (hA.image continuous_fst).prod
    ((hB.image continuous_fst).prod (hA.image continuous_snd))
  apply hc.of_isClosed_subset
  · exact ((isClosed_tsupport (uncurry A)).preimage
      (continuous_fst.prodMk continuous_snd.snd)).inter
      ((isClosed_tsupport (uncurry B)).preimage
        (continuous_snd.fst.prodMk continuous_snd.snd))
  · intro q hq
    exact ⟨⟨_, hq.1, rfl⟩, ⟨_, hq.2, rfl⟩, ⟨_, hq.1, rfl⟩⟩

/-- Jointly compact original amplitudes give a compactly supported packed
cycle symbol. Forward continuity is needed only on their original joint
carrier; in particular no phase smoothness at the zero covector is assumed.
The Hamilton/compatible-geometry producer supplies this forward continuity.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem PrimitiveNormalGeometry.hasCompactSupport_cycleSymbol
    {X D : Set E} {S : E → E → ℝ} {A B : E → E → Mat}
    {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E} {W K : Set (NormalVariables n)}
    (G : PrimitiveNormalGeometry X D S A B η J W K)
    (hA : HasCompactSupport (uncurry A)) (hB : HasCompactSupport (uncurry B))
    (hΞ : ContinuousOn (normalForwardCoordinates S) (jointNormalCarrier A B)) :
    HasCompactSupport (uncurry (cycleCrossNormalSymbol D S A B η J)) := by
  let f := extendedCrossNormalAmplitude (bufferedNormalDomain X D S) A B η J
  have hs : support f ⊆ normalForwardCoordinates S '' jointNormalCarrier A B := by
    apply support_extendedCrossNormalAmplitude_subset S A B η J G.mapsTo G.rightInverse
    intro q _ hqa hqb
    exact ⟨subset_tsupport (uncurry A) hqa, subset_tsupport (uncurry B) hqb⟩
  let pack : NormalVariables n → E × Euclidean (2 * n) :=
    fun q ↦ ((2 * Real.pi)⁻¹ • q.2.2, pairedPosition q.1 q.2.1)
  have hpack : Continuous pack :=
    (continuous_snd.snd.const_smul ((2 * Real.pi : ℝ)⁻¹)).prodMk
      (continuous_pairedPosition.comp (continuous_fst.prodMk continuous_snd.fst))
  have hc := ((isCompact_jointNormalCarrier A B hA hB).image_of_continuousOn hΞ).image hpack
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hc.isClosed
  intro p hp
  change cycleCrossNormalSymbol D S A B η J p.1 p.2 ≠ 0 at hp
  rw [cycleCrossNormalSymbol_eq_pairedBuffered X D S A B η J G.left_output G.right_output] at hp
  let q : NormalVariables n :=
    (normalLeftPosition n p.2, (normalRightPosition n p.2, (2 * Real.pi) • p.1))
  have hq : q ∈ support f := hp
  refine ⟨q, hs hq, ?_⟩
  change ((2 * Real.pi)⁻¹ • ((2 * Real.pi) • p.1),
    pairedPosition (normalLeftPosition n p.2) (normalRightPosition n p.2)) = p
  rw [inv_smul_smul₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), pairedPosition_normalPositions]

end JanetCartan.FourierIntegral.LowBounds
