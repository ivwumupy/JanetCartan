module

public import JanetCartan.Iteration.PhysicalForwardMean.BranchOperators

/-!
# Exact original forward-kernel physical differentiation

A normalized phase is used ONLY to calculate the physical derivatives. Its
agreement with the literal original phase is needed only where the original
input mask and physical amplitude are active. The kernel, its input measure,
all original masks and the output field are unchanged. The full corrected
amplitude is differentiated, not replaced by its principal component.
Consumer: `app:ch_mean_pairs:eq:block-normal` and `block-fields`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.PhysicalForwardMean
open RawPrimary.SliceBounds PhysicalMean NormalComparison

variable {n : ℕ} {X : Type*}
local notation "E" => Euclidean n

/-- The literal forward coefficient, in the shared native-kernel convention
whose last argument is the adjoint amplitude. -/
def physicalForwardKernel (φ : X → E → ℝ) (m : X → ℝ) (A : X → E → ℂ) : E → X → ℂ :=
  sampledMomentKernel φ m (fun u x ↦ star (A u x))

/-- A phase extension off the ORIGINAL active support does not change the
forward kernel at any point. No cutoff is changed or reselected
(`app:ch_mean_pairs:eq:block-normal`). -/
theorem physicalForwardKernel_eq_normalized
    (φ θ : X → E → ℝ) (lam m : X → ℝ) (A : X → E → ℂ)
    {K : Set E} (hAK : ∀ u, tsupport (A u) ⊆ K)
    (hphase : ∀ u, m u ≠ 0 → ∀ x ∈ K, φ u x = lam u * θ u x) (u : X) :
    (fun x ↦ physicalForwardKernel φ m A x u) =
      fun x ↦ (m u : ℂ) •
        (Complex.exp (Complex.I * (lam u * θ u x : ℝ)) • A u x) := by
  funext x
  by_cases hm : m u = 0
  · simp [physicalForwardKernel, sampledMomentKernel, hm]
  by_cases ha : A u x = 0
  · simp [physicalForwardKernel, sampledMomentKernel, ha]
  · simp only [physicalForwardKernel, sampledMomentKernel, star_star, oscillatoryFactor,
      one_mul, hphase u hm x (hAK u (subset_tsupport _ ha)), smul_eq_mul, mul_assoc]

/-- Physical smoothness of the literal kernel follows from the original
normalized phase and COMPLETE amplitude. Literal raw phase behavior away from
the source support is irrelevant (`app:ch_mean_pairs:eq:block-normal`). -/
theorem physicalForwardKernel_smooth
    (φ θ : X → E → ℝ) (lam m : X → ℝ) (A : X → E → ℂ)
    (hθ : ∀ u, ContDiff ℝ ∞ (θ u)) (hA : ∀ u, ContDiff ℝ ∞ (A u))
    {K : Set E} (hAK : ∀ u, tsupport (A u) ⊆ K)
    (hphase : ∀ u, m u ≠ 0 → ∀ x ∈ K, φ u x = lam u * θ u x) (u : X) :
    ContDiff ℝ ∞ (fun x ↦ physicalForwardKernel φ m A x u) := by
  rw [physicalForwardKernel_eq_normalized φ θ lam m A hAK hphase u]
  exact (((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul (hθ u)))).cexp).smul (hA u)).const_smul _

/-- Every physical derivative of the SAME original forward kernel is the
finite sum of its actual binary coefficients and the exact frequency powers.
All plus/minus/realization choices remain in the original full amplitude
(`app:ch_mean_pairs:eq:block-normal`, `app:ch_mean_pairs:eq:block-fields`). -/
theorem physicalForwardKernel_jet_eq_branches
    (φ θ : X → E → ℝ) (lam m : X → ℝ) (A : X → E → ℂ)
    (hθ : ∀ u, ContDiff ℝ ∞ (θ u)) (hA : ∀ u, ContDiff ℝ ∞ (A u))
    {K : Set E} (hAK : ∀ u, tsupport (A u) ⊆ K)
    (hphase : ∀ u, m u ≠ 0 → ∀ x ∈ K, φ u x = lam u * θ u x)
    (s : ℕ) (v : Fin s → E) (x : E) (u : X) :
    iteratedFDeriv ℝ s (fun y ↦ physicalForwardKernel φ m A y u) x v =
      ∑ b : SliceDerivativeBranch s,
        physicalForwardKernel φ m (fun u y ↦ sliceDerivativeAmplitude (θ u) (A u) v b y) x u *
          (lam u : ℂ) ^ b.phaseCount := by
  rw [physicalForwardKernel_eq_normalized φ θ lam m A hAK hphase u]
  have he : ContDiff ℝ ∞ (fun y ↦ Complex.exp (Complex.I * (lam u * θ u y : ℝ)) • A u y) :=
    ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul (hθ u)))).cexp).smul (hA u)
  rw [iteratedFDeriv_const_smul_apply' (he.contDiffAt.of_le (by simp)),
    smul_apply,
    iteratedFDeriv_oscillation_smul_eq_branches isOpen_univ (hθ u).contDiffOn (hA u).contDiffOn
      (lam u) s (mem_univ x) v]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hm : m u = 0
  · simp [physicalForwardKernel, sampledMomentKernel, hm]
  by_cases hb : sliceDerivativeAmplitude (θ u) (A u) v b x = 0
  · simp [physicalForwardKernel, sampledMomentKernel, hb]
  · have hx : x ∈ K := hAK u
      (tsupport_sliceDerivativeAmplitude_subset (θ u) (A u) v b (subset_tsupport _ hb))
    simp only [physicalForwardKernel, sampledMomentKernel, star_star, oscillatoryFactor,
      one_mul, hphase u hm x hx, smul_eq_mul]
    ring

end JanetCartan.PhysicalForwardMean
