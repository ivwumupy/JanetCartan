module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ConicInterior.RadialBuffers.Geometry
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformGeometry.Construction

/-!
# Primitive controls on the actual radial image buffers

The input `hstate` below is exactly the fixed closed-ball conclusion of
`UniformGeometry.exists_uniform_fieldRoot_conicGeometry` (also of `RootFlow`'s
`exists_uniform_fieldRoot_twoTimeHamiltonPhase`). The input `hroot` is exactly
that same constructor's global `fieldDomain` root conclusion after choosing
`Q`. In particular its normalized transverse-speed lower bound is already
global. No new derivative gap or compact class of coefficients is required.

Consumer: all primitive root and domain arguments of
`exists_uniform_nested_physicalDirectLocalizers` for the finite radial family,
in `app:ch_regular:lem:finite-chain` and `app:ch_regular:thm:no-return`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior

open RegularSector.Characteristic RootFamily AmplitudeBounds ActualCarriers

variable {d : ℕ}

/-- Rescaling the section cancels the actual radial state dilation. Consumer:
the `1/2` section lower bound in the mask construction
(`app:ch_regular:lem:finite-chain`). -/
theorem radial_section_apply (ℓ : Euclidean d →L[ℝ] ℝ) {a : ℝ} (ha : a ≠ 0)
    (w : RootState (Euclidean d)) :
    (a⁻¹ • ℓ) (rootRadialEquiv a ha w).2.2 = ℓ w.2.2 := by
  simp [ha]

/-- The scaled frequency ball is the actual image of the original frequency
bound, with its radius multiplied by `a` (`app:ch_regular:lem:finite-chain`). -/
theorem radial_frequency_mem_closedBall {a : ℝ} (ha : 0 < a)
    {η η₀ : Euclidean d} {ε : ℝ} (hη : η ∈ closedBall η₀ ε) :
    a • η ∈ closedBall (a • η₀) (a * ε) := by
  rw [mem_closedBall, dist_smul₀, Real.norm_eq_abs, abs_of_pos ha]
  exact mul_le_mul_of_nonneg_left hη ha.le

/-- The positively invariant constructor domain contains the actual image
of each original root buffer. This leaves the domain and root function
unchanged (`app:ch_regular:thm:no-return`). -/
theorem radial_image_subset_fieldDomain
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean (d + 1))} {ℓ : Euclidean d →L[ℝ] ℝ}
    {η₀ : Euclidean d} {ε a : ℝ} (ha : 0 < a)
    {K : Set (RootState (Euclidean d))} (hK : K ⊆ fieldDomain e Ω ℓ η₀ ε) :
    rootRadialEquiv a ha.ne' '' K ⊆ fieldDomain e Ω ℓ η₀ ε := by
  rintro _ ⟨w, hw, rfl⟩
  exact fieldDomain_smul e Ω ℓ η₀ ε (hK hw) ha

/-- The exact fixed state and global root conclusions of the uniform geometry
constructor supply the primitive mask controls on every actual radial buffer.
`U'` can be any one of the compact pieces constructed in
`exists_finite_radial_initial_buffers`; its inclusion in the common image
buffer is proved there, before `Q` is chosen. The physical ball, coordinate
split, root, and global domain are the SAME as in the original constructor.
The speed bound is its global normalized bound, not a new assumption on the
radial copy (`app:ch_regular:thm:no-return`). -/
theorem fieldRoot_radial_buffer_primitives
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    (Ω : Set (Euclidean (d + 1))) (ℓ : Euclidean d →L[ℝ] ℝ)
    (η₀ : Euclidean d) (H : (Fin (d + 1) → MetricTensor (d + 1)) × Euclidean d → ℝ)
    (U : Set ((Fin (d + 1) → MetricTensor (d + 1)) × Euclidean d)) (V : Set ℝ)
    (x : Euclidean (d + 1)) (z : RootState (Euclidean d))
    (r c : Fin (d + 1)) {R ρ ε κ μ ν G a : ℝ} (hκ : 0 < κ) (ha : 0 < a)
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
        |minorTransportCoefficient (rootPencil e Q h w) (rootTimeCoefficient e Q w) r c|)
    {U' : Set (RootState (Euclidean d))}
    (hU' : U' ⊆ rootRadialEquiv a ha.ne' '' closedBall z (3 * ρ)) :
    let h := fieldRoot e Q H
    let D := fieldDomain e Ω ℓ η₀ ε
    let K' := rootRadialEquiv a ha.ne' '' closedBall z (3 * ρ)
    U' ⊆ D ∧ K' ⊆ D ∧
    (∀ v ∈ D, v.2.2 ≠ 0 ∧
      determinant (Q (e.symm (v.1, v.2.1))) (e.symm (h v, v.2.2)) = 0 ∧
      fderiv ℝ (determinant (Q (e.symm (v.1, v.2.1))))
        (e.symm (h v, v.2.2)) (e.symm (1, 0)) ≠ 0) ∧
    (∀ v ∈ U' ∪ K',
      v.2.2 ∈ closedBall (a • η₀) (a * ε) ∧
      (1 / 2 : ℝ) ≤ (a⁻¹ • ℓ) v.2.2 ∧
      |h v| ≤ (a⁻¹ • ℓ) v.2.2 * (a * G)) ∧
    (∀ v ∈ U' ∪ K', e.symm (v.1, v.2.1) ∈ closedBall x R) ∧
    ∀ v ∈ K', κ ≤ |pencilRootSpeed Q e h v| := by
  let K' := rootRadialEquiv a ha.ne' '' closedBall z (3 * ρ)
  have hKD : K' ⊆ fieldDomain e Ω ℓ η₀ ε :=
    radial_image_subset_fieldDomain e ha (fun w hw ↦ (hstate w hw).1)
  have hunion : U' ∪ K' ⊆ K' := union_subset hU' Subset.rfl
  refine ⟨hU'.trans hKD, hKD, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hvroot := hroot v hv
    refine ⟨hvroot.1, hvroot.2.1, ?_⟩
    have hgap := hvroot.2.2.2.2.1
    intro hz
    rw [hz, mul_zero, abs_zero] at hgap
    exact (not_le_of_gt hκ) hgap
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := hunion hv
    have hs := hstate w hw
    have hvD := hKD (mem_image_of_mem _ hw)
    have hvalue := (hroot _ hvD).2.2.2.2.2.2.1
    refine ⟨radial_frequency_mem_closedBall ha hs.2.2.1, ?_, ?_⟩
    · simpa only [radial_section_apply] using hs.2.2.2
    · convert hvalue using 1
      simp [rootRadialEquiv_apply, ha.ne', mul_assoc, mul_left_comm]
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := hunion hv
    exact (hstate w hw).2.1
  · intro v hv
    exact (hroot v (hKD hv)).2.2.2.2.1

end JanetCartan.ArbitraryAccuracy.ProtectedMasks.ConicInterior
