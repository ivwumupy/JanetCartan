module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.Graded
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Coordinates

/-!
# The literal matrix amplitudes in the evolution consumer's coordinates

`SymbolBudgets` groups the joint variables as `((t,(s,y)),η)`, while the
characteristic construction groups them as `(t,(s,(y,η)))`. The fixed linear
conversion below costs no derivatives and has no varying primitive factor.
It applies directly to each of the three proved complex matrix amplitudes.
Conic extension and its frequency normalization remain the parent's task.
Source: `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds

variable {n d : ℕ}

/-- The fixed regrouping of the same four variables for
`EvolutionIntegral.SymbolBudgets.jointAmplitude`. -/
def evolutionToCharacteristicPoint : EvolutionIntegral.SymbolBudgets.TwoTimePoint d →L[ℝ]
    TwoTimePoint (Euclidean d) :=
  ({ toFun := fun p ↦ (p.1.1, (p.1.2.1, (p.1.2.2, p.2)))
     map_add' := fun _ _ ↦ rfl
     map_smul' := fun _ _ ↦ rfl } :
    EvolutionIntegral.SymbolBudgets.TwoTimePoint d →ₗ[ℝ] TwoTimePoint (Euclidean d)).toContinuousLinearMap

/-- Curry the same matrix field into the exact type expected by the evolution
operator; this changes no value, cutoff, or frequency variable. -/
def curryCharacteristicMatrix (f : TwoTimePoint (Euclidean d) → Matrix (Fin n) (Fin n) ℂ) :
    EvolutionIntegral.TwoTimeAmplitude d n :=
  fun t s y η ↦ f (t, (s, (y, η)))

/-- Literal agreement with the evolution consumer's joint amplitude. -/
theorem jointAmplitude_curryCharacteristicMatrix
    (f : TwoTimePoint (Euclidean d) → Matrix (Fin n) (Fin n) ℂ) :
    EvolutionIntegral.SymbolBudgets.jointAmplitude (curryCharacteristicMatrix f) =
      f ∘ evolutionToCharacteristicPoint := rfl

/-- Product-norm compact balls have exactly the same radius after regrouping.
Thus the amplitude construction's fixed compact domains are retained. -/
theorem evolutionToCharacteristicPoint_maps_closedBall
    (q : EvolutionIntegral.SymbolBudgets.TwoTimePoint d) (ρ : ℝ) :
    MapsTo evolutionToCharacteristicPoint (closedBall q ρ)
      (closedBall (evolutionToCharacteristicPoint q) ρ) := by
  intro p hp
  change (p.1.1, (p.1.2.1, (p.1.2.2, p.2))) ∈
    closedBall (q.1.1, (q.1.2.1, (q.1.2.2, q.2))) ρ
  simpa only [mem_closedBall, Prod.dist_eq, max_assoc] using hp

/-- The proved local matrix estimates transfer to the consumer's actual joint
amplitude with the same derivative order. The cost depends only on the fixed
coordinate regrouping and `m`, so it preserves both single-high and graded
estimates (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem cNorm_jointAmplitude_curryCharacteristicMatrix_le
    (q : EvolutionIntegral.SymbolBudgets.TwoTimePoint d) (ρ : ℝ)
    {U : Set (TwoTimePoint (Euclidean d))} (hU : IsOpen U)
    (hKU : closedBall (evolutionToCharacteristicPoint q) ρ ⊆ U)
    {f : TwoTimePoint (Euclidean d) → Matrix (Fin n) (Fin n) ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) :
    cNorm (closedBall q ρ) m
        (EvolutionIntegral.SymbolBudgets.jointAmplitude (curryCharacteristicMatrix f)) ≤
      NullTransport.AmplitudeTame.linearNormCost (evolutionToCharacteristicPoint (d := d)) m *
        cNorm (closedBall (evolutionToCharacteristicPoint q) ρ) m f := by
  rw [jointAmplitude_curryCharacteristicMatrix]
  exact NullTransport.AmplitudeTame.cNorm_comp_linear_le evolutionToCharacteristicPoint
    (isCompact_closedBall _ _) hU hKU hf (evolutionToCharacteristicPoint_maps_closedBall q ρ) m

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds
