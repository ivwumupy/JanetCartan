module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.TransportedDerivative

/-!
# Fixed cutoff insertion for the transport channels

The transport coefficients in `app:ch_osc:prop:osc-normal` retain the original
closed support. A scalar cutoff equal to one there therefore leaves the full
two-position channel kernel unchanged, including its normalization squared.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace JanetCartan.NormalComparison

open AmplitudeBound

variable {n : ℕ}
local notation "E" => Euclidean n

/-- Parameter differentiation and the input divergence retain a fixed closed
carrier (`app:ch_osc:prop:osc-normal`). This support statement also applies
when the velocity is only defined smoothly on the interior input domain. -/
theorem transportCoefficient_eq_zero_off_carrier
    {S : Set E} (hS : IsClosed S) {A : ℝ → E → ℂ}
    (hs : ∀ s u, u ∉ S → A s u = 0)
    (s : ℝ) (w : E → E) {u : E} (hu : u ∉ S) :
    transportCoefficient (fun v ↦ deriv (fun t ↦ A t v) s)
      (fun j v ↦ (w v j : ℂ) * A s v) u = 0 := by
  have hparam : (fun t ↦ A t u) = fun _ ↦ 0 := funext fun t ↦ hs t u hu
  have hB (j : Fin n) : tsupport (fun v ↦ (w v j : ℂ) * A s v) ⊆ S := by
    apply closure_minimal _ hS
    intro v hv
    by_contra hn
    exact hv (by simp only [hs s v hn, mul_zero])
  have hpartial (j : Fin n) :
      partialDeriv (fun v ↦ (w v j : ℂ) * A s v) u j = 0 := by
    unfold partialDeriv
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h ↦ hu (hB j h))]
    rfl
  simp only [transportCoefficient, hparam, deriv_const, hpartial,
    Finset.sum_const_zero, sub_self]

/-- The two physical cutoff factors leave the divergence transport entry
unchanged (`app:ch_osc:prop:osc-normal`). Support is derived from the actual
amplitude family, including its parameter and input derivatives. -/
theorem cutoff_mul_transportCoefficient
    {S : Set (E × E)} (hS : IsClosed S)
    {a b : ℝ → E → E → ℂ}
    (ha : ∀ s z, z ∉ S → a s z.1 z.2 = 0)
    (hb : ∀ s z, z ∉ S → b s z.1 z.2 = 0)
    (χ : E → E → ℂ) (hχ : ∀ z ∈ S, χ z.1 z.2 = 1)
    (s : ℝ) (x y : E) (w : E → E) (u : E) :
    let c := transportCoefficient
      (fun v ↦ deriv (fun t ↦ a t x v * star (b t y v)) s)
      (fun j v ↦ (w v j : ℂ) * (a s x v * star (b s y v))) u
    χ x u * c * star (χ y u) = c := by
  dsimp only
  by_cases hx : (x, u) ∈ S
  · by_cases hy : (y, u) ∈ S
    · rw [hχ (x, u) hx, hχ (y, u) hy, star_one, one_mul, mul_one]
    · have hz := transportCoefficient_eq_zero_off_carrier
        (hS.preimage (continuous_const.prodMk continuous_id))
        (A := fun t v ↦ a t x v * star (b t y v))
        (fun t v hv ↦ by rw [hb t (y, v) hv, star_zero, mul_zero]) s w hy
      rw [hz, mul_zero, zero_mul]
  · have hz := transportCoefficient_eq_zero_off_carrier
      (hS.preimage (continuous_const.prodMk continuous_id))
      (A := fun t v ↦ a t x v * star (b t y v))
      (fun t v hv ↦ by rw [ha t (x, v) hv, zero_mul]) s w hx
    rw [hz, mul_zero, zero_mul]

/-- The first-mask-derivative entry is also unchanged by both scalar cutoff
factors (`app:ch_osc:prop:osc-normal`). -/
theorem cutoff_mul_transportVectorEntry
    {S : Set (E × E)} {a b : E → E → ℂ}
    (ha : ∀ z, z ∉ S → a z.1 z.2 = 0)
    (hb : ∀ z, z ∉ S → b z.1 z.2 = 0)
    (χ : E → E → ℂ) (hχ : ∀ z ∈ S, χ z.1 z.2 = 1)
    (x y : E) (w : E → E) (u : E) (j : Fin n) :
    χ x u * (-((w u j : ℂ) * (a x u * star (b y u)))) * star (χ y u) =
      -((w u j : ℂ) * (a x u * star (b y u))) := by
  by_cases hx : (x, u) ∈ S
  · by_cases hy : (y, u) ∈ S
    · simp only [hχ (x, u) hx, hχ (y, u) hy, star_one, one_mul, mul_one]
    · simp only [hb (y, u) hy, star_zero, mul_zero, neg_zero, zero_mul]
  · simp only [ha (x, u) hx, zero_mul, mul_zero, neg_zero]

/-- Inserting a fixed scalar cutoff gives the existing literal
`fullNormalAmplitudeKernel`, with the normalization squared and both physical
positions retained (`app:ch_osc:prop:osc-normal`). The cutoff compatibility
premise is discharged for the actual transport entries by the two preceding
support lemmas. No integral exchange is used in this algebraic identity. -/
theorem fullNormalAmplitudeKernel_normalized_cutoff
    (D : Set E) (scale K : ℝ) (φ : E → E → ℝ) (χ : E → E → ℂ)
    (c : E → Euclidean (2 * n) → ℂ)
    (hc : ∀ x y u, χ x u * c u (pairedPosition x y) * star (χ y u) =
      c u (pairedPosition x y))
    (g f : E → ℂ) (x : E) :
    fullNormalAmplitudeKernel (μ := volume.restrict D)
      (normalizedOscillatoryKernel scale K φ χ) c g f x =
      ∫ y, (((scale ^ 2 : ℝ) : ℂ) * ∫ u in D,
        oscillatoryFactor K (φ x u - φ y u) * c u (pairedPosition x y) * g u) * f y := by
  unfold fullNormalAmplitudeKernel
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  dsimp only
  calc
    _ = (normalizedOscillatoryKernel scale K φ χ x u *
        star (normalizedOscillatoryKernel scale K φ χ y u)) *
          c u (pairedPosition x y) * g u := by ring
    _ = _ := by
      rw [normalizedOscillatoryKernel_mul_star]
      have he := hc x y u
      calc
        _ = ((scale ^ 2 : ℝ) : ℂ) * oscillatoryFactor K (φ x u - φ y u) *
            (χ x u * c u (pairedPosition x y) * star (χ y u)) * g u := by ring
        _ = _ := by rw [he]; ring

end JanetCartan.NormalComparison
