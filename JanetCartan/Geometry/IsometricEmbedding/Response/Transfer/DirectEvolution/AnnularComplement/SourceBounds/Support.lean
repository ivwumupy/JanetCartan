module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.Literal

/-!
# Fixed supports of the literal annular source kernels

Source: `app:ch_response:lem:energy-carrier-jets`. Compactness in the source
comes from the original envelope, whereas output support comes from the
original physical masks. Neither depends on frequency or integration order.
The adjoint exchanges the two masks, as its literal kernel requires.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral JanetCartan.Localization
open RegularSector.Characteristic.EvolutionIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- The original envelope supports the full forward source amplitude. -/
theorem tsupport_forwardAnnularSourceAmplitude_subset
    (A : FullAmplitude n r) (π : E → ℂ) (lam : ℝ) (a : E → F) (x ξ : E) :
    tsupport (forwardAnnularSourceAmplitude A π lam a x ξ) ⊆ tsupport a := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro z hz
  by_contra h
  have ha := image_eq_zero_of_notMem_tsupport h
  exact hz (by simp [forwardAnnularSourceAmplitude, ha])

/-- The adjoint source amplitude has the same original envelope support. -/
theorem tsupport_adjointAnnularSourceAmplitude_subset
    (A : FullAmplitude n r) (π : E → ℂ) (lam : ℝ) (a : E → F) (x ξ : E) :
    tsupport (adjointAnnularSourceAmplitude A π lam a x ξ) ⊆ tsupport a := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro z hz
  by_contra h
  have ha := image_eq_zero_of_notMem_tsupport h
  exact hz (by simp [adjointAnnularSourceAmplitude, ha])

/-- Forward kernel support is inherited from the first physical position. -/
theorem tsupport_forwardAnnularSourceKernel_subset
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (ξ : E)
    {X : Set E} (hX : IsClosed X) (hs : ∀ x ∉ X, ∀ z, A x z ξ = 0) :
    tsupport (fun x => forwardAnnularSourceKernel Θ A π φ lam a x ξ) ⊆ X := by
  apply closure_minimal _ hX
  intro x hx
  by_contra h
  exact hx (by simp [forwardAnnularSourceKernel, forwardAnnularSourceAmplitude,
    annularComplementAmplitude, frequencyCutFullAmplitude, hs x h])

/-- The literal adjoint kernel uses the support in the second physical
position, after reversing the full amplitude. -/
theorem tsupport_adjointAnnularSourceKernel_subset
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (ξ : E)
    {Y : Set E} (hY : IsClosed Y) (hs : ∀ x ∉ Y, ∀ z, A z x ξ = 0) :
    tsupport (fun x => adjointAnnularSourceKernel Θ A π φ lam a x ξ) ⊆ Y := by
  apply closure_minimal _ hY
  intro x hx
  by_contra h
  exact hx (by simp [adjointAnnularSourceKernel, adjointAnnularSourceAmplitude,
    annularComplementAmplitude, frequencyCutFullAmplitude, hs x h])

/-- The actual forward demodulator preserves the original output support. -/
theorem tsupport_demodulatedForwardAnnularSourceKernel_subset
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (ξ : E)
    {X : Set E} (hX : IsClosed X) (hs : ∀ x ∉ X, ∀ z, A x z ξ = 0) :
    tsupport (fun x => demodulatedForwardAnnularSourceKernel Θ A π φ lam a x ξ) ⊆ X :=
  (tsupport_smul_subset_right _ _).trans
    (tsupport_forwardAnnularSourceKernel_subset Θ A π φ lam a ξ hX hs)

/-- Demodulation of the adjoint keeps its exchanged output support. -/
theorem tsupport_demodulatedAdjointAnnularSourceKernel_subset
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (ξ : E)
    {Y : Set E} (hY : IsClosed Y) (hs : ∀ x ∉ Y, ∀ z, A z x ξ = 0) :
    tsupport (fun x => demodulatedAdjointAnnularSourceKernel Θ A π φ lam a x ξ) ⊆ Y :=
  (tsupport_smul_subset_right _ _).trans
    (tsupport_adjointAnnularSourceKernel_subset Θ A π φ lam a ξ hY hs)

/-- No forward kernel remains on the plateau of the same normalized selector.
This supplies the zero branch before applying the exterior gap estimates. -/
theorem forwardAnnularSourceKernel_eq_zero_of_selector_eq_one
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E)
    (hπ : π (lam⁻¹ • ξ) = 1) :
    forwardAnnularSourceKernel Θ A π φ lam a x ξ = 0 := by
  simp [forwardAnnularSourceKernel, forwardAnnularSourceAmplitude,
    annularComplementAmplitude, frequencyCutFullAmplitude, hπ]

/-- The literal adjoint has the same plateau, despite conjugation. -/
theorem adjointAnnularSourceKernel_eq_zero_of_selector_eq_one
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E)
    (hπ : π (lam⁻¹ • ξ) = 1) :
    adjointAnnularSourceKernel Θ A π φ lam a x ξ = 0 := by
  simp [adjointAnnularSourceKernel, adjointAnnularSourceAmplitude,
    annularComplementAmplitude, frequencyCutFullAmplitude, hπ]

/-- All four literal elapsed kernels have fixed compact output support,
derived directly from the two original physical masks. This is the support
input to the independent annular Sobolev deduction. -/
theorem hasCompactSupport_elapsedAnnularSourceKernels {d : ℕ}
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d r)
    (χout χsource β π : Euclidean (d + 1) → ℂ)
    (φ : Euclidean (d + 1) → ℝ) (t lam : ℝ)
    (a : Euclidean (d + 1) → F) (ξ : Euclidean (d + 1))
    (hout : HasCompactSupport χout) (hsource : HasCompactSupport χsource) :
    let Θ := elapsedPhase Ψ t
    let A := elapsedAmplitude b χout χsource β t
    HasCompactSupport (fun x => forwardAnnularSourceKernel Θ A π φ lam a x ξ) ∧
    HasCompactSupport (fun x => adjointAnnularSourceKernel Θ A π φ lam a x ξ) ∧
    HasCompactSupport (fun x => demodulatedForwardAnnularSourceKernel Θ A π φ lam a x ξ) ∧
    HasCompactSupport (fun x => demodulatedAdjointAnnularSourceKernel Θ A π φ lam a x ξ) := by
  dsimp only
  have h₁ (x : Euclidean (d + 1)) (hx : x ∉ tsupport χout) (z : Euclidean (d + 1)) :
      elapsedAmplitude b χout χsource β t x z ξ = 0 :=
    elapsedAmplitude_eq_zero_of_mask b χout χsource β t x z ξ
      (Or.inl (image_eq_zero_of_notMem_tsupport hx))
  have h₂ (x : Euclidean (d + 1)) (hx : x ∉ tsupport χsource) (z : Euclidean (d + 1)) :
      elapsedAmplitude b χout χsource β t z x ξ = 0 :=
    elapsedAmplitude_eq_zero_of_mask b χout χsource β t z x ξ
      (Or.inr (Or.inl (image_eq_zero_of_notMem_tsupport hx)))
  exact ⟨hout.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_forwardAnnularSourceKernel_subset _ _ _ _ _ _ _ (isClosed_tsupport _) h₁),
    hsource.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_adjointAnnularSourceKernel_subset _ _ _ _ _ _ _ (isClosed_tsupport _) h₂),
    hout.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_demodulatedForwardAnnularSourceKernel_subset _ _ _ _ _ _ _ (isClosed_tsupport _) h₁),
    hsource.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_demodulatedAdjointAnnularSourceKernel_subset _ _ _ _ _ _ _ (isClosed_tsupport _) h₂)⟩

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
