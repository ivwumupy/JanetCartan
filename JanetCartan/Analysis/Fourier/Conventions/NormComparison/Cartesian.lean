module

public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import JanetCartan.Analysis.Sobolev.Local.Comparison.SmoothBounds.SymmetricJets

/-!
# Cartesian maximum and the project's derivative seminorm

For `app:not:fourier`, the Cartesian multiindices are the existing canonical
coordinate lists, counted once by `sobolevMultiindices`. The maximum convention
and the sum of Fréchet operator norms are compared on a compact set where the
function is smooth on a neighborhood. In particular, no use of an unbounded
real conditional supremum as a finite norm is made.

Scalar outputs give the manuscript's scalar norm. The componentwise vector
and Frobenius matrix versions are supplied in the sibling `Components` module.
The reverse inequality reuses the proved symmetry and Cartesian jet comparison;
it does not identify an operator norm with a sum of component norms.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.FourierConventions
open LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]

section Normed
variable [NormedSpace ℝ F]

/-- Maximum of the Cartesian derivatives through order `r` on `D`, using
the fixed coordinate multiindices of `app:not:fourier`. For nonscalar outputs
the codomain norm is used; the componentwise maximum is defined separately.
Applications of this real supremum supply bounded jets. -/
def cartesianCNorm (D : Set (EuclideanSpace ℝ (Fin n))) (r : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → F) : ℝ :=
  sSup {t | ∃ α ∈ sobolevMultiindices n r, ∃ x ∈ D,
    t = ‖cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f)
      (fun i ↦ α (some i)) x‖}

/-- Nonnegativity includes the empty domain (`app:not:fourier`). -/
theorem cartesianCNorm_nonneg (D : Set (EuclideanSpace ℝ (Fin n))) (r : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → F) : 0 ≤ cartesianCNorm D r f :=
  Real.sSup_nonneg (by rintro _ ⟨α, _, x, _, rfl⟩; exact norm_nonneg _)

/-- A common pointwise bound controls the Cartesian maximum, including an
empty domain (`app:not:fourier`). -/
theorem cartesianCNorm_le_of_bound
    {D : Set (EuclideanSpace ℝ (Fin n))} {r : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → F} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ α ∈ sobolevMultiindices n r, ∀ x ∈ D,
      ‖cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f)
        (fun i ↦ α (some i)) x‖ ≤ B) : cartesianCNorm D r f ≤ B :=
  Real.sSup_le (by rintro _ ⟨α, hα, x, hx, rfl⟩; exact hf α hα x hx) hB

private theorem coordinate_order_le {r : ℕ} {α : Option (Fin n) → ℕ}
    (hα : α ∈ sobolevMultiindices n r) : ∑ i, α (some i) ≤ r := by
  have := mem_sobolevMultiindices.mp hα
  omega

/-- The Cartesian maximum is bounded by the project's sum of derivative
operator norms on a compact domain (`app:not:fourier`). Finite-order local
smoothness proves the boundedness needed for the real suprema. -/
theorem cartesianCNorm_le_cNorm
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsCompact D) {r : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : ∀ x ∈ D, ContDiffAt ℝ r f x) :
    cartesianCNorm D r f ≤ cNorm D r f := by
  apply cartesianCNorm_le_of_bound (cNorm_nonneg D r f)
  intro α hα x hx
  exact (norm_cartesianJetDerivative_le _ _ _).trans
    (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hD hf hx (coordinate_order_le hα))

/-- Each actual Cartesian derivative is bounded by its maximum, with
boundedness proved from compactness and smoothness (`app:not:fourier`). -/
theorem norm_cartesianJetDerivative_le_cartesianCNorm
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsCompact D) {r : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : ∀ x ∈ D, ContDiffAt ℝ r f x)
    {α : Option (Fin n) → ℕ} (hα : α ∈ sobolevMultiindices n r)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ D) :
    ‖cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j f)
      (fun i ↦ α (some i)) x‖ ≤ cartesianCNorm D r f := by
  unfold cartesianCNorm
  refine le_csSup ?_ ⟨α, hα, x, hx, rfl⟩
  refine ⟨cNorm D r f, ?_⟩
  rintro t ⟨β, hβ, y, hy, rfl⟩
  exact (norm_cartesianJetDerivative_le _ _ _).trans
    (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hD hf hy (coordinate_order_le hβ))

end Normed

/-- Fixed dimension and order constant in the Cartesian/Fréchet maximum
comparison of `app:not:fourier`. -/
def cartesianCNormComparisonConstant (n r : ℕ) : ℝ :=
  ((r : ℝ) + 1) *
    (Real.sqrt (BallExtension.frechetEnergyComparisonConstant n r *
      (sobolevMultiindices n r).card) + 1)

/-- The constant is positive at every dimension and order (`app:not:fourier`). -/
theorem cartesianCNormComparisonConstant_pos (n r : ℕ) :
    0 < cartesianCNormComparisonConstant n r := by
  unfold cartesianCNormComparisonConstant
  positivity

section Hilbert
variable [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The sum of the actual Fréchet derivative suprema is bounded by the
Cartesian maximum. The constant depends only on the domain dimension and
order; symmetry is derived from smoothness on the specified neighborhood.
This is the reverse convention bridge in `app:not:fourier`. -/
theorem cNorm_le_cartesianCNorm
    {D U : Set (EuclideanSpace ℝ (Fin n))} (hD : IsCompact D)
    (hU : IsOpen U) (hDU : D ⊆ U) {r : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : ContDiffOn ℝ ∞ f U) :
    cNorm D r f ≤ cartesianCNormComparisonConstant n r * cartesianCNorm D r f := by
  let P := cartesianCNorm D r f
  let C := BallExtension.frechetEnergyComparisonConstant n r
  let N : ℝ := (sobolevMultiindices n r).card
  have hP : 0 ≤ P := cartesianCNorm_nonneg D r f
  have hC : 0 < C := BallExtension.frechetEnergyComparisonConstant_pos n r
  have hN : 0 ≤ N := by positivity
  have hlocal : ∀ x ∈ D, ContDiffAt ℝ r f x := fun x hx ↦
    (hf.contDiffAt (hU.mem_nhds (hDU hx))).of_le (by simp)
  have hbound (j : ℕ) (hj : j ≤ r) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D) :
      ‖iteratedFDeriv ℝ j f x‖ ≤ (Real.sqrt (C * N) + 1) * P := by
    have hsym (k : ℕ) (_hk : k ≤ r) (v : Fin k → EuclideanSpace ℝ (Fin n))
        (σ : Equiv.Perm (Fin k)) :
        iteratedFDeriv ℝ k f x (v ∘ σ) = iteratedFDeriv ℝ k f x v := by
      simpa only [iteratedFDerivWithin_of_isOpen k hU (hDU hx)] using
        BallExtension.iteratedFDerivWithin_comp_perm_of_contDiffOn hU hf (hDU hx) k v σ
    have hsum := sum_sq_norm_symmetricJet_le r (fun k ↦ iteratedFDeriv ℝ k f x) hsym
    have hcoords : (∑ α ∈ sobolevMultiindices n r,
        ‖cartesianJetDerivative (fun k ↦ iteratedFDeriv ℝ k f)
          (fun i ↦ α (some i)) x‖ ^ 2) ≤ N * P ^ 2 := by
      calc
        _ ≤ ∑ _α ∈ sobolevMultiindices n r, P ^ 2 := by
          apply Finset.sum_le_sum
          intro α hα
          exact pow_le_pow_left₀ (norm_nonneg _)
            (norm_cartesianJetDerivative_le_cartesianCNorm hD hlocal hα hx) 2
        _ = _ := by simp [N]
    have hsq : ‖iteratedFDeriv ℝ j f x‖ ^ 2 ≤ C * N * P ^ 2 := by
      calc
        _ ≤ ∑ k ∈ Finset.range (r + 1), ‖iteratedFDeriv ℝ k f x‖ ^ 2 :=
          Finset.single_le_sum (fun _ _ ↦ sq_nonneg _)
            (Finset.mem_range.mpr (by omega))
        _ ≤ C * ∑ α ∈ sobolevMultiindices n r,
            ‖cartesianJetDerivative (fun k ↦ iteratedFDeriv ℝ k f)
              (fun i ↦ α (some i)) x‖ ^ 2 := hsum
        _ ≤ C * (N * P ^ 2) := mul_le_mul_of_nonneg_left hcoords hC.le
        _ = _ := by ring
    have hroot : ‖iteratedFDeriv ℝ j f x‖ ≤ Real.sqrt (C * N) * P := by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hP)).mp
      simpa only [mul_pow, Real.sq_sqrt (mul_nonneg hC.le hN)] using hsq
    exact hroot.trans (mul_le_mul_of_nonneg_right (by linarith) hP)
  have h := cNorm_le_sum_of_bounds (s := D) (r := r)
    (fun _ _ ↦ mul_nonneg (by positivity : 0 ≤ Real.sqrt (C * N) + 1) hP) hbound
  simpa [cartesianCNormComparisonConstant, C, N, P, mul_assoc] using h

/-- The two conventions give the same notion of convergence to zero on the
fixed compact domain. This transfers the Section 4 coefficient convergence
to the `C^m` terminology of `app:not:fourier`. -/
theorem tendsto_cartesianCNorm_zero_iff
    {A : Type*} {l : Filter A} {D U : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U) (r : ℕ)
    (f : A → EuclideanSpace ℝ (Fin n) → F) (hf : ∀ a, ContDiffOn ℝ ∞ (f a) U) :
    Tendsto (fun a ↦ cartesianCNorm D r (f a)) l (𝓝 0) ↔
      Tendsto (fun a ↦ cNorm D r (f a)) l (𝓝 0) := by
  constructor
  · intro h
    have hm := h.const_mul (cartesianCNormComparisonConstant n r)
    simp only [mul_zero] at hm
    exact squeeze_zero (fun a ↦ cNorm_nonneg D r (f a))
      (fun a ↦ cNorm_le_cartesianCNorm hD hU hDU (hf a)) hm
  · intro h
    exact squeeze_zero (fun a ↦ cartesianCNorm_nonneg D r (f a))
      (fun a ↦ cartesianCNorm_le_cNorm hD (fun x hx ↦
        ((hf a).contDiffAt (hU.mem_nhds (hDU hx))).of_le (by simp))) h

end Hilbert
end JanetCartan.FourierConventions
