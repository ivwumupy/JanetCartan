module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.Hermitian
public import JanetCartan.Analysis.ContDiff.Norm.Basic
import Mathlib.Tactic.Ring

/-!
# Density differences from linear amplitude estimates

The final bilinear argument of `app:ch_response:cor:current-atoms`. The domain of
the amplitude may contain both physical and carrier variables, so the estimate
controls their joint `cNorm`. The finite-jet amplitude estimates are explicit
inputs: this module does not prove those analytic estimates for the actual waves.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan
namespace CorrectedAtoms

variable {R D E G : Type*} [AddCommGroup R] [Module ℝ R]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `app:ch_response:eq:current-density-lipschitz`: the difference of quadratic
densities of two linear amplitude maps. -/
def bilinearDensityError (B : E →L[ℝ] E →L[ℝ] G)
    (A L : R →ₗ[ℝ] (D → E)) (u : R) : D → G :=
  fun x ↦ B (A u x) (A u x) - B (L u x) (L u x)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- `app:ch_response:eq:current-density-lipschitz`: exact four-term expansion.
Every term contains one amplitude error, including for the initial-data difference. -/
theorem bilinearDensityError_sub (B : E →L[ℝ] E →L[ℝ] G)
    (A L : R →ₗ[ℝ] (D → E)) (u v : R) :
    bilinearDensityError B A L u - bilinearDensityError B A L v =
      (fun x ↦ B ((A - L) (u - v) x) (A u x)) +
      (fun x ↦ B (L (u - v) x) ((A - L) u x)) +
      (fun x ↦ B ((A - L) v x) (A (u - v) x)) +
      (fun x ↦ B (L v x) ((A - L) (u - v) x)) := by
  ext x
  simp only [bilinearDensityError, LinearMap.sub_apply, map_sub, Pi.sub_apply,
    sub_apply, Pi.add_apply]
  abel

/-- `app:ch_response:eq:current-density-lipschitz`: the bilinear density estimate
from linear amplitude bounds. `p` can be the initial scalar's finite-jet seminorm;
`η` is the small amplitude-error bound (in the application, `C / lam`). -/
theorem cNorm_bilinearDensityError_sub_le (B : E →L[ℝ] E →L[ℝ] G)
    (A L : R →ₗ[ℝ] (D → E)) {s : Set D} (hs : IsCompact s) {q : ℕ}
    (hA : ∀ u, ContDiff ℝ q (A u)) (hL : ∀ u, ContDiff ℝ q (L u))
    (p : R → ℝ) (hp : ∀ u, 0 ≤ p u) {C η : ℝ} (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hAb : ∀ u, cNorm s q (A u) ≤ C * p u)
    (hLb : ∀ u, cNorm s q (L u) ≤ C * p u)
    (hΔb : ∀ u, cNorm s q ((A - L) u) ≤ η * p u) (u v : R) :
    cNorm s q (bilinearDensityError B A L u - bilinearDensityError B A L v) ≤
      2 * (2 : ℝ) ^ q * ‖B‖ * C * η * (p u + p v) * p (u - v) := by
  have hΔ (w : R) : ContDiff ℝ q ((A - L) w) := (hA w).sub (hL w)
  have hc {f g : D → E} (hf : ContDiff ℝ q f) (hg : ContDiff ℝ q g) :
      ContDiff ℝ q (fun x ↦ B (f x) (g x)) :=
    B.isBoundedBilinearMap.contDiff.comp (hf.prodMk hg)
  have hb {f g : D → E} (hf : ContDiff ℝ q f) (hg : ContDiff ℝ q g)
      {a b : ℝ} (ha : 0 ≤ a) (hf' : cNorm s q f ≤ a) (hg' : cNorm s q g ≤ b) :
      cNorm s q (fun x ↦ B (f x) (g x)) ≤ (2 : ℝ) ^ q * ‖B‖ * a * b := by
    apply (cNorm_bilinear_le B hs hf hg).trans
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hf' (by positivity)) hg'
      (cNorm_nonneg _ _ _) (by positivity)
  let f₁ := fun x ↦ B ((A - L) (u - v) x) (A u x)
  let f₂ := fun x ↦ B (L (u - v) x) ((A - L) u x)
  let f₃ := fun x ↦ B ((A - L) v x) (A (u - v) x)
  let f₄ := fun x ↦ B (L v x) ((A - L) (u - v) x)
  have h₁ : ContDiff ℝ q f₁ := hc (hΔ (u - v)) (hA u)
  have h₂ : ContDiff ℝ q f₂ := hc (hL (u - v)) (hΔ u)
  have h₃ : ContDiff ℝ q f₃ := hc (hΔ v) (hA (u - v))
  have h₄ : ContDiff ℝ q f₄ := hc (hL v) (hΔ (u - v))
  rw [bilinearDensityError_sub]
  change cNorm s q (f₁ + f₂ + f₃ + f₄) ≤ _
  calc
    _ ≤ cNorm s q (f₁ + f₂ + f₃) + cNorm s q f₄ :=
      cNorm_add_le hs ((h₁.add h₂).add h₃) h₄
    _ ≤ (cNorm s q (f₁ + f₂) + cNorm s q f₃) + cNorm s q f₄ :=
      add_le_add (cNorm_add_le hs (h₁.add h₂) h₃) le_rfl
    _ ≤ (cNorm s q f₁ + cNorm s q f₂) + cNorm s q f₃ + cNorm s q f₄ :=
      add_le_add (add_le_add (cNorm_add_le hs h₁ h₂) le_rfl) le_rfl
    _ ≤ (2 : ℝ) ^ q * ‖B‖ * (η * p (u - v)) * (C * p u) +
        (2 : ℝ) ^ q * ‖B‖ * (C * p (u - v)) * (η * p u) +
        (2 : ℝ) ^ q * ‖B‖ * (η * p v) * (C * p (u - v)) +
        (2 : ℝ) ^ q * ‖B‖ * (C * p v) * (η * p (u - v)) := by
      exact add_le_add (add_le_add (add_le_add
        (hb (hΔ (u - v)) (hA u) (mul_nonneg hη (hp (u - v))) (hΔb (u - v)) (hAb u))
        (hb (hL (u - v)) (hΔ u) (mul_nonneg hC (hp (u - v))) (hLb (u - v)) (hΔb u)))
        (hb (hΔ v) (hA (u - v)) (mul_nonneg hη (hp v)) (hΔb v) (hAb (u - v))))
        (hb (hL v) (hΔ (u - v)) (mul_nonneg hC (hp v)) (hLb v) (hΔb (u - v)))
    _ = _ := by ring

/-- `app:ch_response:eq:current-density-lipschitz`: the actual real Hermitian
density error. For a real leading amplitude, its second term is exactly `A₀ᵀ A₀`
by `hermitianTensor_ofReal`. -/
def atomicDensityError {m n : Type*} [Fintype m] [Fintype n]
    (A L : R →ₗ[ℝ] (D → Matrix m n ℂ)) (u : R) : D → Matrix n n ℝ :=
  fun x ↦ hermitianTensor (A u x) - hermitianTensor (L u x)

/-- `app:ch_response:eq:current-density-lipschitz`: the joint physical/carrier
density Lipschitz bound, conditional on the finite-jet estimates for the two
linear amplitude maps. The factor `lam⁻¹` is preserved without a frequency-dependent
constant. No construction or bounds for the actual corrected atoms are assumed
to have been proved by this lemma. -/
theorem cNorm_atomicDensityError_sub_le {m n : Type*} [Fintype m] [Fintype n]
    (A L : R →ₗ[ℝ] (D → Matrix m n ℂ)) {s : Set D} (hs : IsCompact s) {q : ℕ}
    (hA : ∀ u, ContDiff ℝ q (A u)) (hL : ∀ u, ContDiff ℝ q (L u))
    (p : R → ℝ) (hp : ∀ u, 0 ≤ p u) {C K lam : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hlam : 0 < lam)
    (hAb : ∀ u, cNorm s q (A u) ≤ C * p u)
    (hLb : ∀ u, cNorm s q (L u) ≤ C * p u)
    (hΔb : ∀ u, cNorm s q ((A - L) u) ≤ K * lam⁻¹ * p u) (u v : R) :
    cNorm s q (atomicDensityError A L u - atomicDensityError A L v) ≤
      (2 * (2 : ℝ) ^ q * C * K) * lam⁻¹ * (p u + p v) * p (u - v) := by
  have h := cNorm_bilinearDensityError_sub_le (hermitianCrossBilinear m n) A L hs
    hA hL p hp hC (mul_nonneg hK (inv_nonneg.mpr hlam.le)) hAb hLb hΔb u v
  change cNorm s q (atomicDensityError A L u - atomicDensityError A L v) ≤ _ at h
  apply h.trans
  calc
    _ ≤ 2 * (2 : ℝ) ^ q * 1 * C * (K * lam⁻¹) * (p u + p v) * p (u - v) := by
      gcongr <;> first
        | exact hp _
        | exact add_nonneg (hp u) (hp v)
        | exact norm_hermitianCrossBilinear_le m n
    _ = _ := by ring

end CorrectedAtoms
end JanetCartan
