module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.PhaseBounds

/-!
# The homogeneous phase seminorm convention

In Step 3 of `app:ch_regular_base:thm:actual-calculus`, the phase is normalized
with degree one, whereas the amplitude and scalar primitives have order zero.
The phase seminorm used by the profile assembly is exactly the joint `cNorm`
of the phase divided by the dilation radius, on every normalized box. The dummy
second physical position is retained in the domain.
-/

@[expose] public noncomputable section
namespace JanetCartan.FourierIntegral.PrimitiveProfiles
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
variable {n : ℕ}

/-- Dividing a positively homogeneous phase by the radial scale preserves every
joint seminorm on a buffered normalized chart. This identifies the phase
quantity in `exists_finitePrimitiveProfile_inputs` with the degree-one normalized
phase convention of `app:ch_regular_base:eq:fio-input`. -/
theorem cNorm_normalizedPhase_eq
    {K U : Set (Point n)} (hU : IsOpen U) (hKU : K ⊆ U)
    {X D : Set (Euclidean n)} (hchart : ∀ p ∈ U, p.1.1 ∈ X ∧ p.2 ∈ D)
    {S : Euclidean n → Euclidean n → ℝ}
    (hhom : ∀ R : ℝ, 0 < R → ∀ x ∈ X, ∀ η ∈ D, S x (R • η) = R * S x η)
    {R : ℝ} (hR : 0 < R) (k : ℕ) :
    cNorm K k (fun p : Point n ↦ R⁻¹ * S p.1.1 (R • p.2)) =
      cNorm K k (fun p : Point n ↦ S p.1.1 p.2) := by
  have he : Set.EqOn (fun p : Point n ↦ R⁻¹ * S p.1.1 (R • p.2))
      (fun p : Point n ↦ S p.1.1 p.2) U := by
    intro p hp
    dsimp only
    rw [hhom R hR p.1.1 (hchart p hp).1 p.2 (hchart p hp).2,
      ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  unfold cNorm
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Set.image_congr
  intro p hp
  exact congrArg norm ((Filter.eventuallyEq_of_mem (hU.mem_nhds (hKU hp)) he).iteratedFDeriv
    (𝕜 := ℝ) j).self_of_nhds

end JanetCartan.FourierIntegral.PrimitiveProfiles
