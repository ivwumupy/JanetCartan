module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.Amplitude

/-!
# Compact carriers for the regularized joint graph integrals

The common carrier retains both positions and all three frequency variables.
The complementary output symbol need not have compact support. This supplies
the support volume in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelEstimates
open FourierIntegral
variable {n r : ℕ}

/-- The rectangular carrier for both literal orientations of
`app:ch_regular:eq:joint-kernel-phase`. -/
def jointCarrier (Kb : Set (Euclidean n × Euclidean n))
    (Kξ Kη Kζ : Set (Euclidean n)) : Set (JointVariables (Euclidean n)) :=
  Kb ×ˢ (Kξ ×ˢ Kη ×ˢ Kζ)

/-- Compactness of the primitive carriers suffices for joint integration
(`app:ch_regular:eq:chain-tail`). -/
theorem isCompact_jointCarrier {Kb : Set (Euclidean n × Euclidean n)}
    {Kξ Kη Kζ : Set (Euclidean n)} (hb : IsCompact Kb) (hξ : IsCompact Kξ)
    (hη : IsCompact Kη) (hζ : IsCompact Kζ) :
    IsCompact (jointCarrier Kb Kξ Kη Kζ) := hb.prod (hξ.prod (hη.prod hζ))

/-- Primitive support conditions bound the full amplitude's support. The
physical support is imposed on the actual two-position amplitude, so all
source shoulders and the weighted inverse are admitted without changing their
positions (`app:ch_regular:eq:chain-tail`). -/
theorem tsupport_jointAmplitude_subset (ρ : ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    {Kb : Set (Euclidean n × Euclidean n)} {Kξ Kη Kζ : Set (Euclidean n)}
    (hb : IsCompact Kb) (hξ : IsCompact Kξ) (hη : IsCompact Kη) (hζ : IsCompact Kζ)
    (hA : ∀ u z ξ, (u, z) ∉ Kb → A u z ξ = 0)
    (hχA : tsupport (fun ξ => χA (ρ • ξ)) ⊆ Kξ)
    (hmi : tsupport (fun η => mi (y, η)) ⊆ Kη)
    (hχo : tsupport (fun ζ => χo (ρ • ζ)) ⊆ Kζ) :
    tsupport (jointAmplitude ρ A mi mo χA χo x y) ⊆ jointCarrier Kb Kξ Kη Kζ := by
  apply closure_minimal ?_ (isCompact_jointCarrier hb hξ hη hζ).isClosed
  intro p hp
  have hbp : p.1 ∈ Kb := by
    by_contra hh
    have hz := hA p.1.1 p.1.2 (ρ • p.2.1) hh
    simp [Function.mem_support, jointAmplitude, hz] at hp
  have hξp : χA (ρ • p.2.1) ≠ 0 := by
    intro hz
    simp [Function.mem_support, jointAmplitude, hz] at hp
  have hηp : mi (y, p.2.2.1) ≠ 0 := by
    intro hz
    simp [Function.mem_support, jointAmplitude, hz] at hp
  have hζp : χo (ρ • p.2.2.2) ≠ 0 := by
    intro hz
    simp [Function.mem_support, jointAmplitude, hz] at hp
  exact ⟨hbp, hχA (subset_tsupport _ hξp), hmi (subset_tsupport _ hηp),
    hχo (subset_tsupport _ hζp)⟩

end JanetCartan.FiniteChain.Graph.KernelEstimates
