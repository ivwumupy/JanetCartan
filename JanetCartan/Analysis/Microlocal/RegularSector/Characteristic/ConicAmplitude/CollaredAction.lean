module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.CollaredBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.PhysicalAction
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.NestedBounds
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.KernelDifferentiation.CompactOperator

/-!
# The collar preserves the physical action and the actual masked graph

The initial spatial covector is fixed under the physical operator, so its
collar commutes exactly with all principal and zeroth-order terms. The nested
cutoff construction then removes that collar from the full elapsed amplitude
on the right multiplier's closed support. Both physical masks stay in place;
the resulting graph, its literal adjoint and elapsed integral are identical.
Source: `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ConicAmplitude
open FiniteMasks AmplitudeBounds EvolutionIntegral
open JanetCartan.CharacteristicTransport.KernelDifferentiation
variable {n d : ℕ}

/-- The actual spatial collar commutes with the literal physical operator,
including `B`. Together with `pencilCorrectionResidual_extend_column_eq_physicalApply`
this identifies the collared residual with `P W₁`; no commutator is omitted
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem firstOrderApply_collared_slice (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (a : Euclidean d → ℝ) (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (Q : Euclidean n → Fin n → MetricTensor n) (B : Euclidean n → MetricTensor n)
    (f : TwoTimePoint (Euclidean d) → Fin n → ℂ)
    (s : ℝ) (η : Euclidean d) (x : Euclidean n)
    (hf : DifferentiableAt ℝ (f ∘ physicalSlice e s ((ℓ η)⁻¹ • η)) x) :
    WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
      (collared ℓ o a f ∘ physicalSlice e s η) x =
      (conicMask a η : ℂ) • ((ℓ η)⁻¹ ^ o •
        WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
          (f ∘ physicalSlice e s ((ℓ η)⁻¹ • η)) x) := by
  have hg : DifferentiableAt ℝ (extend ℓ o f ∘ physicalSlice e s η) x :=
    hf.const_smul ((ℓ η)⁻¹ ^ o)
  change WKB.firstOrderApply _ _
    (fun y ↦ (conicMask a η : ℂ) • (extend ℓ o f ∘ physicalSlice e s η) y) x = _
  rw [firstOrderApply_const_smul _ _ hg,
    firstOrderApply_extend_slice ℓ o e Q B f s η x hf]

/-- The collar is literally absent from the complete elapsed amplitude once
its plateau contains the original right multiplier. All masks and the
original source covector are retained (`fixed-time-representation`). -/
theorem elapsedAmplitude_collared_eq_extend
    (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ) (a : Euclidean d → ℝ)
    (f : TwoTimePoint (Euclidean d) → Matrix (Fin n) (Fin n) ℂ)
    (χout χsource β : Euclidean (d + 1) → ℂ)
    (hβ : ∀ ξ ∈ tsupport β, conicMask a (spatialPart ξ) = 1) (r : ℝ) :
    elapsedAmplitude (curryCharacteristicMatrix (collared ℓ o a f)) χout χsource β r =
      elapsedAmplitude (curryCharacteristicMatrix (extend ℓ o f)) χout χsource β r := by
  funext x z ξ
  by_cases hz : β ξ = 0
  · simp [elapsedAmplitude, hz]
  · simp [elapsedAmplitude, curryCharacteristicMatrix, collared,
      hβ ξ (subset_tsupport β hz)]

/-- The exact cutoffs constructed by `exists_nested_spatial_conicMask`
preserve the full graph and its literal Hilbert adjoint. This is an identity
of the existing canonical operators, not a new realization or bound
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem elapsedGraph_collared_eq_extend
    (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ) (a : Euclidean d → ℝ)
    (b : Euclidean (d + 1) → ℝ) (L : ℝ)
    (hnest : ∀ ξ ∈ tsupport (dilatedConicMask b L),
      conicMask a =ᶠ[𝓝 (spatialPart ξ)] (fun _ ↦ 1))
    (f : TwoTimePoint (Euclidean d) → Matrix (Fin n) (Fin n) ℂ)
    (Ψ : TwoTimePhase d) (χout χsource : Euclidean (d + 1) → ℂ) (r : ℝ) :
    let β := fun ξ ↦ (dilatedConicMask b L ξ : ℂ)
    elapsedGraph Ψ (curryCharacteristicMatrix (collared ℓ o a f)) χout χsource β r =
      elapsedGraph Ψ (curryCharacteristicMatrix (extend ℓ o f)) χout χsource β r ∧
    (elapsedGraph Ψ (curryCharacteristicMatrix (collared ℓ o a f)) χout χsource β r).adjoint =
      (elapsedGraph Ψ (curryCharacteristicMatrix (extend ℓ o f)) χout χsource β r).adjoint := by
  dsimp only
  have hβ : ∀ ξ ∈ tsupport (fun ξ ↦ (dilatedConicMask b L ξ : ℂ)),
      conicMask a (spatialPart ξ) = 1 := by
    intro ξ hξ
    exact (hnest ξ (tsupport_comp_subset Complex.ofReal_zero (dilatedConicMask b L) hξ)).eq_of_nhds
  have h := congrArg (FourierIntegral.FullLowBounds.fullGraphOperator (elapsedPhase Ψ r))
    (elapsedAmplitude_collared_eq_extend ℓ o a f χout χsource _ hβ r)
  exact ⟨h, congrArg (fun T ↦ T.adjoint) h⟩

/-- The same equality holds for the literal datum-wise elapsed integral,
with its original time interval and both physical cutoffs. No integral
estimate or interchange is assumed (`fixed-time-representation`). -/
theorem elapsedGraphIntegral_collared_eq_extend
    (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ) (a : Euclidean d → ℝ)
    (b : Euclidean (d + 1) → ℝ) (L : ℝ)
    (hnest : ∀ ξ ∈ tsupport (dilatedConicMask b L),
      conicMask a =ᶠ[𝓝 (spatialPart ξ)] (fun _ ↦ 1))
    (f : TwoTimePoint (Euclidean d) → Matrix (Fin n) (Fin n) ℂ)
    (Ψ : TwoTimePhase d) (χout χsource : Euclidean (d + 1) → ℂ)
    (Δ : ℝ) (u : SpacetimeL2 d n) :
    let β := fun ξ ↦ (dilatedConicMask b L ξ : ℂ)
    elapsedGraphIntegral Δ Ψ (curryCharacteristicMatrix (collared ℓ o a f)) χout χsource β u =
      elapsedGraphIntegral Δ Ψ (curryCharacteristicMatrix (extend ℓ o f)) χout χsource β u := by
  dsimp only [elapsedGraphIntegral]
  congr 1
  funext r
  rw [(elapsedGraph_collared_eq_extend ℓ o a b L hnest f Ψ χout χsource r).1]

end JanetCartan.RegularSector.Characteristic.ConicAmplitude
