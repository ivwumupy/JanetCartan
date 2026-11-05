module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.MaskAssembly

/-!
# Exact root-constructor inputs to the radial mask assembly

The global normalized speed estimate is part of the original root
constructor, so the radial family needs no additional speed assumption.
These projections match `exists_uniform_radial_nested_localizers_and_gap`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior

open RegularSector.Characteristic RootFamily AmplitudeBounds ActualCarriers

variable {d : ℕ}

/-- Extract the original mask-assembly primitives from the EXACT fixed-state
and global-root conclusions of `exists_uniform_fieldRoot_conicGeometry`.
In particular, the speed estimate is global on `fieldDomain`; it is not
postulated on new radial buffers. The physical closed-ball conclusion gives
`B ∩ W` membership as soon as the original selected physical ball is included
there. Smoothness, homogeneity, the ODE, source identity and inverse-segment
fields are used directly by the assembly without changing their signatures.
Consumer: `exists_uniform_radial_nested_localizers_and_gap`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:thm:no-return`). -/
theorem fieldRoot_maskAssembly_primitives
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    (Ω : Set (Euclidean (d + 1))) (ℓ : Euclidean d →L[ℝ] ℝ)
    (η₀ : Euclidean d) (H : (Fin (d + 1) → MetricTensor (d + 1)) × Euclidean d → ℝ)
    (U : Set ((Fin (d + 1) → MetricTensor (d + 1)) × Euclidean d)) (V : Set ℝ)
    (x : Euclidean (d + 1)) (z : RootState (Euclidean d))
    (r c : Fin (d + 1)) {R ρ ε κ μ ν G : ℝ} (hκ : 0 < κ)
    (hstate : ∀ w ∈ closedBall z (3 * ρ),
      w ∈ fieldDomain e Ω ℓ η₀ ε ∧
      rootPhysicalPosition e w ∈ closedBall x R ∧
      w.2.2 ∈ closedBall η₀ ε ∧ (1 / 2 : ℝ) ≤ ℓ w.2.2)
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (hroot : ∀ w ∈ fieldDomain e Ω ℓ η₀ ε,
      let h := fieldRoot e Q H
      let p := (Q (e.symm (w.1, w.2.1)), w.2.2)
      let pNorm := normalizedFieldParameter e Q ℓ w
      let PNorm := coefficientRootPencil e H pNorm
      w.2.2 ≠ 0 ∧ (rootPencil e Q h w).det = 0 ∧
      (p, h w) ∈ CharacteristicRoot.conicBand ℓ U V ∧
      (∀ τ, (p, τ) ∈ CharacteristicRoot.conicBand ℓ U V →
        (determinant p.1 (e.symm (τ, p.2)) = 0 ↔ h w = τ)) ∧
      κ ≤ |determinantNormalization (e.symm (h w, w.2.2)) *
        fderiv ℝ (determinant p.1) (e.symm (h w, w.2.2)) (e.symm (1, 0))| ∧
      h w = ℓ w.2.2 * H pNorm ∧ |h w| ≤ ℓ w.2.2 * G ∧
      rootPencil e Q h w = ℓ w.2.2 • PNorm ∧
      μ ≤ |PNorm.adjugate r c| ∧
      ν ≤ |minorTransportCoefficient PNorm (rootTimeCoefficient e Q w) r c| ∧
      (ℓ w.2.2) ^ d * μ ≤ |(rootPencil e Q h w).adjugate r c| ∧
      (ℓ w.2.2) ^ (2 * d) * ν ≤
        |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c|) :
    let h := fieldRoot e Q H
    let D := fieldDomain e Ω ℓ η₀ ε
    closedBall z (3 * ρ) ⊆ D ∧
    (∀ w ∈ D, w.2.2 ≠ 0 ∧
      determinant (Q (e.symm (w.1, w.2.1))) (e.symm (h w, w.2.2)) = 0 ∧
      fderiv ℝ (determinant (Q (e.symm (w.1, w.2.1))))
        (e.symm (h w, w.2.2)) (e.symm (1, 0)) ≠ 0) ∧
    (∀ w ∈ closedBall z (3 * ρ),
      w.2.2 ∈ closedBall η₀ ε ∧ (1 / 2 : ℝ) ≤ ℓ w.2.2 ∧ |h w| ≤ ℓ w.2.2 * G) ∧
    (∀ w ∈ closedBall z (3 * ρ), e.symm (w.1, w.2.1) ∈ closedBall x R) ∧
    ∀ w ∈ D, κ ≤ |pencilRootSpeed Q e h w| := by
  refine ⟨fun w hw ↦ (hstate w hw).1, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hwroot := hroot w hw
    refine ⟨hwroot.1, hwroot.2.1, ?_⟩
    have hspeed := hwroot.2.2.2.2.1
    intro hz
    rw [hz, mul_zero, abs_zero] at hspeed
    exact (not_le_of_gt hκ) hspeed
  · intro w hw
    have hs := hstate w hw
    exact ⟨hs.2.2.1, hs.2.2.2, (hroot w hs.1).2.2.2.2.2.2.1⟩
  · exact fun w hw ↦ (hstate w hw).2.1
  · exact fun w hw ↦ (hroot w hw).2.2.2.2.1

/-- The homogeneous-domain input of the radial mask assembly is the SAME
constructor homogeneity together with the already proved positive invariance
of `fieldDomain`. No new domain or root is chosen
(`app:ch_regular:thm:no-return`). -/
theorem fieldRoot_maskAssembly_radial_invariance
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    (Ω : Set (Euclidean (d + 1))) (ℓ : Euclidean d →L[ℝ] ℝ)
    (η₀ : Euclidean d) (ε : ℝ)
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (H : (Fin (d + 1) → MetricTensor (d + 1)) × Euclidean d → ℝ)
    (hhom : ∀ w ∈ fieldDomain e Ω ℓ η₀ ε, ∀ a : ℝ, 0 < a →
      fieldRoot e Q H (w.1, (w.2.1, a • w.2.2)) = a * fieldRoot e Q H w) :
    ∀ w ∈ fieldDomain e Ω ℓ η₀ ε, ∀ a : ℝ, 0 < a →
      (w.1, (w.2.1, a • w.2.2)) ∈ fieldDomain e Ω ℓ η₀ ε ∧
        fieldRoot e Q H (w.1, (w.2.1, a • w.2.2)) = a * fieldRoot e Q H w :=
  fun w hw a ha ↦ ⟨fieldDomain_smul e Ω ℓ η₀ ε hw ha, hhom w hw a ha⟩

end JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior
