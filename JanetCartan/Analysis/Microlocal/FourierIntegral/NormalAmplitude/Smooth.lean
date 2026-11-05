module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Basic
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InverseAmplitude.Determinant
public import JanetCartan.Analysis.Microlocal.Localization.CompactSupport

/-!
# Buffered zero extension of the full matrix amplitude

Smoothness in Step 1 of `app:ch_regular_base:thm:actual-calculus` is deduced
from smooth input matrices, the joint inverse, and a Jacobian gap. Support is
transported from the original numerator: smoothness of the zero extension is
not an input. The compact-carrier version applies to compact frequency pieces;
no compactness assertion about a whole unbounded conic symbol is made.
-/

@[expose] public noncomputable section
open Set Function Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- The joint inverse preserves both physical positions
(`app:ch_regular_base:eq:actual-normal-amplitude`). -/
def normalInverseCoordinates
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (q : NormalVariables n) : NormalVariables n := (q.1, (q.2.1, η q.1 q.2.1 q.2.2))

/-- The joint forward change of physical covectors
(`app:ch_regular_base:eq:actual-normal-amplitude`). -/
def normalForwardCoordinates (S : Euclidean n → Euclidean n → ℝ)
    (q : NormalVariables n) : NormalVariables n :=
  (q.1, (q.2.1, NormalComparison.averagedGradient S q.1 q.2.1 q.2.2))

/-- Smoothness of the cross-normal on the open inverse chart from the primitive
input regularity and nonvanishing determinant. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem crossNormalAmplitude_contDiffOn
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    {Ω W : Set (NormalVariables n)}
    (hη : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ η q.1 q.2.1 q.2.2) Ω)
    (hmap : MapsTo (normalInverseCoordinates η) Ω W)
    (hA : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ A q.1 q.2.2) W)
    (hB : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ B q.2.1 q.2.2) W)
    (hJ : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ J q.1 q.2.1 q.2.2) W)
    (hgap : ∀ q ∈ W, (J q.1 q.2.1 q.2.2).det ≠ 0) :
    ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦
      crossNormalAmplitude A B η J q.1 q.2.1 q.2.2) Ω := by
  have hT : ContDiffOn ℝ ∞ (normalInverseCoordinates η) Ω :=
    contDiffOn_fst.prodMk (contDiffOn_snd.fst.prodMk hη)
  have hstar : ContDiff ℝ ∞
      (fun a : Matrix (Fin r) (Fin r) ℂ ↦ a.conjTranspose) :=
    (Matrix.conjTransposeLinearEquiv (Fin r) (Fin r) ℝ ℂ).toContinuousLinearEquiv.contDiff
  have hrec : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦
      |(J q.1 q.2.1 q.2.2).det|⁻¹) W := by
    intro q hq
    exact (NormalComparison.contDiffAt_reciprocalAbsNormalJacobian (hgap q hq)).comp_contDiffWithinAt
      (g := fun L : Euclidean n →L[ℝ] Euclidean n ↦ |L.det|⁻¹)
      (f := fun q : NormalVariables n ↦ J q.1 q.2.1 q.2.2) q (hJ q hq)
  exact (hrec.comp hT hmap).smul
    ((hA.comp hT hmap).mul (hstar.comp_contDiffOn (hB.comp hT hmap)))

/-- The support of the literal extension lies in the transported original
carrier. The hypotheses concern the original matrices and the inverse law,
not the transformed amplitude. Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem support_extendedCrossNormalAmplitude_subset
    (S : Euclidean n → Euclidean n → ℝ)
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    {Ω W K : Set (NormalVariables n)}
    (hmap : MapsTo (normalInverseCoordinates η) Ω W)
    (hright : ∀ q ∈ Ω,
      normalForwardCoordinates S (normalInverseCoordinates η q) = q)
    (hsupp : ∀ q ∈ W, A q.1 q.2.2 ≠ 0 → B q.2.1 q.2.2 ≠ 0 → q ∈ K) :
    support (extendedCrossNormalAmplitude Ω A B η J) ⊆ normalForwardCoordinates S '' K := by
  intro q hq
  have hΩ : q ∈ Ω := by
    by_contra h
    exact hq (by simp [extendedCrossNormalAmplitude, h])
  have ha : A q.1 (η q.1 q.2.1 q.2.2) ≠ 0 := by
    intro ha
    exact hq (by simp [extendedCrossNormalAmplitude, hΩ, crossNormalAmplitude,
      crossNormalNumerator, ha])
  have hb : B q.2.1 (η q.1 q.2.1 q.2.2) ≠ 0 := by
    intro hb
    exact hq (by simp [extendedCrossNormalAmplitude, hΩ, crossNormalAmplitude,
      crossNormalNumerator, hb])
  exact ⟨normalInverseCoordinates η q, hsupp _ (hmap hΩ) ha hb, hright q hΩ⟩

/-- Closed buffered carriers suffice for smooth zero extension, including
unbounded chart pieces when their image carrier is closed. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`, Step 1. -/
theorem extendedCrossNormalAmplitude_contDiff
    (S : Euclidean n → Euclidean n → ℝ)
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    {Ω W K : Set (NormalVariables n)} (hΩ : IsOpen Ω)
    (hη : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ η q.1 q.2.1 q.2.2) Ω)
    (hmap : MapsTo (normalInverseCoordinates η) Ω W)
    (hA : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ A q.1 q.2.2) W)
    (hB : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ B q.2.1 q.2.2) W)
    (hJ : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ J q.1 q.2.1 q.2.2) W)
    (hgap : ∀ q ∈ W, (J q.1 q.2.1 q.2.2).det ≠ 0)
    (hright : ∀ q ∈ Ω, normalForwardCoordinates S (normalInverseCoordinates η q) = q)
    (hsupp : ∀ q ∈ W, A q.1 q.2.2 ≠ 0 → B q.2.1 q.2.2 ≠ 0 → q ∈ K)
    (hclosed : IsClosed (normalForwardCoordinates S '' K))
    (hbuffer : normalForwardCoordinates S '' K ⊆ Ω) :
    ContDiff ℝ ∞ (extendedCrossNormalAmplitude Ω A B η J) := by
  apply Localization.contDiff_of_contDiffOn_support_neighborhood hΩ
  · apply (crossNormalAmplitude_contDiffOn A B η J hη hmap hA hB hJ hgap).congr
    intro q hq
    simp [extendedCrossNormalAmplitude, hq]
  · exact (closure_minimal
      (support_extendedCrossNormalAmplitude_subset S A B η J hmap hright hsupp)
      hclosed).trans hbuffer

/-- Compact original support gives a compact transported support for the
literal extension (`app:ch_regular_base:eq:actual-normal-amplitude`). Combined
with the preceding theorem this is the compact buffered-support construction. -/
theorem extendedCrossNormalAmplitude_hasCompactSupport
    (S : Euclidean n → Euclidean n → ℝ)
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    {Ω W K : Set (NormalVariables n)}
    (hmap : MapsTo (normalInverseCoordinates η) Ω W)
    (hright : ∀ q ∈ Ω, normalForwardCoordinates S (normalInverseCoordinates η q) = q)
    (hsupp : ∀ q ∈ W, A q.1 q.2.2 ≠ 0 → B q.2.1 q.2.2 ≠ 0 → q ∈ K)
    (hK : IsCompact K) (hΞ : ContinuousOn (normalForwardCoordinates S) K) :
    HasCompactSupport (extendedCrossNormalAmplitude Ω A B η J) := by
  have hc := hK.image_of_continuousOn hΞ
  exact hc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal
    (support_extendedCrossNormalAmplitude_subset S A B η J hmap hright hsupp) hc.isClosed)

/-- Within the open chart every ambient jet of the literal extension is
exactly the full-amplitude jet, with both positions retained. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem iteratedFDeriv_extendedCrossNormalAmplitude_eq
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    {Ω : Set (NormalVariables n)} (hΩ : IsOpen Ω) {q : NormalVariables n}
    (hq : q ∈ Ω) (k : ℕ) :
    iteratedFDeriv ℝ k (extendedCrossNormalAmplitude Ω A B η J) q =
      iteratedFDeriv ℝ k (fun z : NormalVariables n ↦
        crossNormalAmplitude A B η J z.1 z.2.1 z.2.2) q := by
  have he : extendedCrossNormalAmplitude Ω A B η J =ᶠ[𝓝 q]
      (fun z : NormalVariables n ↦ crossNormalAmplitude A B η J z.1 z.2.1 z.2.2) := by
    filter_upwards [hΩ.mem_nhds hq] with z hz
    exact indicator_of_mem hz _
  exact (he.iteratedFDeriv ℝ k).eq_of_nhds

/-- Off the inverse chart every jet of the literal zero extension vanishes.
This follows from the original support and closed buffer, without assuming
regularity of the extension. Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem iteratedFDeriv_extendedCrossNormalAmplitude_eq_zero
    (S : Euclidean n → Euclidean n → ℝ)
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    {Ω W K : Set (NormalVariables n)}
    (hmap : MapsTo (normalInverseCoordinates η) Ω W)
    (hright : ∀ q ∈ Ω, normalForwardCoordinates S (normalInverseCoordinates η q) = q)
    (hsupp : ∀ q ∈ W, A q.1 q.2.2 ≠ 0 → B q.2.1 q.2.2 ≠ 0 → q ∈ K)
    (hclosed : IsClosed (normalForwardCoordinates S '' K))
    (hbuffer : normalForwardCoordinates S '' K ⊆ Ω)
    {q : NormalVariables n} (hq : q ∉ Ω) (k : ℕ) :
    iteratedFDeriv ℝ k (extendedCrossNormalAmplitude Ω A B η J) q = 0 := by
  have hs : tsupport (extendedCrossNormalAmplitude Ω A B η J) ⊆ Ω :=
    (closure_minimal (support_extendedCrossNormalAmplitude_subset S A B η J
      hmap hright hsupp) hclosed).trans hbuffer
  have he := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hq (hs h))
  have hd := (he.iteratedFDeriv ℝ k).eq_of_nhds
  simpa using hd

end JanetCartan.FourierIntegral
