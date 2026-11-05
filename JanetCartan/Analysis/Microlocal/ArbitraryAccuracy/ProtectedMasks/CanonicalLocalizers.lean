module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Nesting
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Exclusions

/-!
# Proof masks in the factors' own coordinates

Pull the constructed physical masks through the actual coordinate permutation.
The support and plateau identities retain their complete closed shoulders.
The resulting canonical masks buffer both orientations of the supported
zero-energy relation and the full diagonal; this supplies the interior and
boundary exclusions of `EvolutionIntegratedLocalization.GradientGaps` and
`UniformCollar` (`app:ch_regular:lem:finite-chain`). No physical angular cone
is imposed directly on a canonical covector.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open FiniteChain.Graph EvolutionIntegratedLocalization

variable {d : ℕ}

/-- The linear equivalence underlying the actual phase-space coordinate change.
Consumer: pullback of the buffered masks in `app:ch_regular:lem:finite-chain`. -/
def adaptedPhaseEquiv (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d)) :
    (Euclidean (d + 1) × Euclidean (d + 1)) ≃L[ℝ]
      (Euclidean (d + 1) × Euclidean (d + 1)) :=
  ((coordinateSplit 0).trans e.symm).prodCongr ((coordinateSplit 0).trans e.symm)

/-- The pullback uses exactly the physical conversion of the actual relation
(`app:ch_regular:lem:finite-chain`). -/
theorem adaptedPhaseEquiv_apply (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    (p : Euclidean (d + 1) × Euclidean (d + 1)) :
    adaptedPhaseEquiv e p = adaptedPhysicalPhaseState e p := by
  have he (x : Euclidean (d + 1)) : coordinateSplit 0 x = (x 0, spatialPart x) := by
    ext j
    · rfl
    · simp [spatialPart]
  change (e.symm (coordinateSplit 0 p.1), e.symm (coordinateSplit 0 p.2)) = _
  simp only [he, adaptedPhysicalPhaseState]

/-- A proof mask in one factor's own canonical coordinates. It depends on
fixed proof depth through `m`, not on the requested accuracy
(`app:ch_regular:lem:finite-chain`). -/
def canonicalProofLocalizer
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    (m : LocalizerSymbol (d + 1)) : LocalizerSymbol (d + 1) :=
  m ∘ adaptedPhaseEquiv e

/-- Complete closed support, including shoulders, is transported exactly
(`app:ch_regular:lem:finite-chain`). -/
theorem tsupport_canonicalProofLocalizer
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    (m : LocalizerSymbol (d + 1)) :
    tsupport (canonicalProofLocalizer e m) = adaptedPhaseEquiv e ⁻¹' tsupport m := by
  unfold tsupport canonicalProofLocalizer
  rw [Function.support_comp_eq_preimage]
  exact ((adaptedPhaseEquiv e).toHomeomorph.preimage_closure _).symm

/-- Open plateaus are transported exactly, rather than only their pointwise
one-level sets (`app:ch_regular:lem:finite-chain`). -/
theorem plateau_canonicalProofLocalizer
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    (m : LocalizerSymbol (d + 1)) :
    interior {p | canonicalProofLocalizer e m p = 1} =
      adaptedPhaseEquiv e ⁻¹' interior {p | m p = 1} := by
  exact ((adaptedPhaseEquiv e).toHomeomorph.preimage_interior {p | m p = 1}).symm

/-- Smoothness, compact support, range, shoulders and plateau survive the
literal coordinate change (`app:ch_regular:lem:finite-chain`). -/
theorem IsBufferedLocalizer.canonicalProofLocalizer
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    {m : LocalizerSymbol (d + 1)}
    {K O : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hm : IsBufferedLocalizer m K O) :
    IsBufferedLocalizer (canonicalProofLocalizer e m)
      (adaptedPhaseEquiv e ⁻¹' K) (adaptedPhaseEquiv e ⁻¹' O) := by
  refine ⟨hm.smooth.comp (adaptedPhaseEquiv e).contDiff,
    fun p ↦ hm.range _, hm.compactSupport.comp_homeomorph (adaptedPhaseEquiv e).toHomeomorph,
    ?_, ?_⟩
  · rw [tsupport_canonicalProofLocalizer]
    exact preimage_mono hm.support_subset
  · rw [plateau_canonicalProofLocalizer]
    exact preimage_mono hm.plateau

/-- A physical adjacent-mask buffer gives the full diagonal and both actual
oriented zero-energy buffers in every chart's own coordinates. The premise
is supplied by `exists_nested_physicalDirectLocalizers_of_primitive_buffers`,
not by a separate successful-mask assumption (`app:ch_regular:lem:finite-chain`). -/
theorem canonicalProofLocalizer_complete_image {J : Type*}
    {i : J → Fin (d + 1)} {h : J → RootState (Euclidean d) → ℝ}
    {Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : J → Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    {χsource χout : J → Euclidean (d + 1) → ℂ} {Δ : ℝ}
    {mi mo : LocalizerSymbol (d + 1)}
    (hbuffer : ∀ p ∈ tsupport mi, ∀ q,
      p = q ∨ physicalDirectRelation i h Φ U K W χsource χout Δ p q →
        q ∈ interior {q | mo q = 1})
    (j : J) (backward : Bool) {a b : Euclidean (d + 1) × Euclidean (d + 1)}
    (ha : a ∈ tsupport (canonicalProofLocalizer (coordinateSplit (i j)) mi))
    (hab : a = b ∨ maskedZeroEnergyRelation (coordinateSplit (i j)) (h j) (Φ j)
      (U j) (K j) W (χsource j) (χout j) Δ backward a b) :
    b ∈ interior {q | canonicalProofLocalizer (coordinateSplit (i j)) mo q = 1} := by
  rw [tsupport_canonicalProofLocalizer] at ha
  rw [plateau_canonicalProofLocalizer]
  apply hbuffer _ ha
  rcases hab with rfl | hab
  · exact Or.inl rfl
  · exact Or.inr ⟨j, backward, a, b, hab, adaptedPhaseEquiv_apply _ _,
      adaptedPhaseEquiv_apply _ _⟩

/-- The canonical input covector has the same norm as its physical image.
This transports annular bounds without confusing the product split norm with
the Euclidean norm (`app:ch_regular:lem:finite-chain`). -/
theorem adaptedPhaseEquiv_covector_norm (i : Fin (d + 1))
    (p : Euclidean (d + 1) × Euclidean (d + 1)) :
    ‖(adaptedPhaseEquiv (coordinateSplit i) p).2‖ = ‖p.2‖ := by
  have hpair := adaptedPhysicalPhaseState_pairing (coordinateSplit i)
    (coordinateSplit_inverse_pairing i) (p.2, p.2)
  simp only [adaptedPhysicalPhaseState, real_inner_self_eq_norm_sq] at hpair
  rw [adaptedPhaseEquiv_apply]
  dsimp only [adaptedPhysicalPhaseState]
  nlinarith [norm_nonneg ((coordinateSplit i).symm (p.2 0, spatialPart p.2)),
    norm_nonneg p.2]

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
