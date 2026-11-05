module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.FiniteBand
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Matrix action of the regularized carrier normal

The literal composition, finite component sums and Fubini calculation behind
`app:ch_background:eq:bg-full-complex-amplitude`. The shared finite-band kernel
bounds justify all exchanges, including for arbitrary complex output L² data.
Hilbert realization of each individual factor is a separate producer input.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace JanetCartan.ContinuumRow.TransportKernel

variable {n N : ℕ} {d : CarrierData n N} {m : CarrierVariable n → ℝ}
local notation "V" => EuclideanSpace ℂ (Fin n)

/-- At fixed initial variable, the real mask multiplies the literal adjoint.
The conjugation in the adjoint is retained
(`app:ch_background:eq:bg-realification`). -/
theorem masked_adjoint_integral (w : Torus n → V) (u : CarrierVariable n) :
    (m u : ℂ) * carrierAdjointIntegral d w u =
      ∫ y, inner ℂ (maskedCarrierKernel d m y u) (w y) := by
  simp only [maskedCarrierKernel, inner_smul_left, Complex.conj_ofReal,
    carrierAdjointIntegral, integral_const_mul]

/-- Finite component expansion of the literal adjoint. Each summand is
integrable by the shared finite-band bounds
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem integral_masked_inner_eq_sum (h : FiniteCarrierKernelBounds d m)
    {w : Torus n → V} (hw : Integrable w) (u : CarrierVariable n) :
    (∫ y, inner ℂ (maskedCarrierKernel d m y u) (w y)) =
      ∑ j, ∫ y, star (maskedCarrierKernel d m y u j) * w y j := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply]
  simpa only [mul_comm] using integral_finsetSum Finset.univ (fun j _ ↦
    integrable_maskedKernel_star_mul h u j (hw.eval_piLp j))

/-- Scalar Fubini for an entry of the rectangular normal, using the original
carrier measure (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem integral_masked_composition_eq_normalEntry (h : FiniteCarrierKernelBounds d m)
    (x : Torus n) (i j : Fin n) {f : Torus n → ℂ} (hf : Integrable f) :
    (∫ u, maskedCarrierKernel d m x u i *
      (∫ y, star (maskedCarrierKernel d m y u j) * f y) ∂carrierMeasure n) =
      ∫ y, regularizedNormalEntry d m x y i j * f y := by
  simp_rw [← integral_const_mul, ← mul_assoc]
  rw [← integral_integral_swap (integrable_carrierNormalDensity_mul h x i j hf)]
  simp only [carrierNormalDensity, integral_mul_const,
    regularizedNormalEntry_eq_integral_carrierNormalDensity]

private theorem integrable_masked_composition (h : FiniteCarrierKernelBounds d m)
    (x : Torus n) (i j : Fin n) {f : Torus n → ℂ} (hf : Integrable f) :
    Integrable (fun u ↦ maskedCarrierKernel d m x u i *
      (∫ y, star (maskedCarrierKernel d m y u j) * f y)) (carrierMeasure n) := by
  simpa only [carrierNormalDensity, mul_assoc, integral_const_mul] using
    (integrable_carrierNormalDensity_mul h x i j hf).integral_prod_right

/-- The composed vector integrand is integrable, so coordinate evaluation may
pass through its Bochner integral
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem integrable_masked_adjoint_action (h : FiniteCarrierKernelBounds d m)
    {w : Torus n → V} (hw : Integrable w) (x : Torus n) :
    Integrable (fun u ↦ ((m u : ℂ) * carrierAdjointIntegral d w u) •
      maskedCarrierKernel d m x u) (carrierMeasure n) := by
  apply Integrable.of_eval_piLp
  intro i
  simp_rw [PiLp.smul_apply, smul_eq_mul, masked_adjoint_integral,
    integral_masked_inner_eq_sum h hw, Finset.sum_mul]
  apply integrable_finsetSum
  intro j _
  simpa only [mul_comm] using integrable_masked_composition h x i j (hw.eval_piLp j)

/-- Exact finite matrix action of `T_R T_R*`, at the level of the two literal
integrals. No boundedness of the unregularized carrier is assumed
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem regularizedCarrierIntegral_adjoint_eq_matrix (h : FiniteCarrierKernelBounds d m)
    {w : Torus n → V} (hw : Integrable w) (x : Torus n) (i : Fin n) :
    regularizedCarrierIntegral d m
      (fun u ↦ (m u : ℂ) * carrierAdjointIntegral d w u) x i =
      ∑ j, ∫ y, regularizedNormalEntry d m x y i j * w y j := by
  rw [regularizedCarrierIntegral_eq_masked,
    eval_integral_piLp (integrable_masked_adjoint_action h hw x).eval_piLp]
  simp_rw [PiLp.smul_apply, smul_eq_mul, masked_adjoint_integral,
    integral_masked_inner_eq_sum h hw, Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    simpa only [mul_comm] using
      integral_masked_composition_eq_normalEntry h x i j (hw.eval_piLp j)
  · intro j _
    simpa only [mul_comm] using integrable_masked_composition h x i j (hw.eval_piLp j)

/-- The literal matrix formula identifies the actual Hilbert normal as soon as
the compact carrier producer supplies its individual action and adjoint formulas.
These premises concern the two factors, not their normal
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem carrierHilbertNormal_eq_matrix (h : FiniteCarrierKernelBounds d m)
    (T : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hT : ∀ f : CarrierL2 n, T f =ᵐ[volume] regularizedCarrierIntegral d m f)
    (w : ComplexOutputL2 n)
    (hAdj : T.adjoint w =ᵐ[carrierMeasure n]
      fun u ↦ (m u : ℂ) * carrierAdjointIntegral d w u) :
    ∀ᵐ x ∂volume, ∀ i, T (T.adjoint w) x i =
      ∑ j, ∫ y, regularizedNormalEntry d m x y i j * w y j := by
  filter_upwards [hT (T.adjoint w)] with x hx
  intro i
  rw [hx]
  have he : regularizedCarrierIntegral d m (T.adjoint w) x =
      regularizedCarrierIntegral d m
        (fun u ↦ (m u : ℂ) * carrierAdjointIntegral d w u) x := by
    apply integral_congr_ae
    filter_upwards [hAdj] with u hu
    simp only [hu]
  rw [he]
  exact regularizedCarrierIntegral_adjoint_eq_matrix h
    ((Lp.memLp w).integrable (by norm_num)) x i

end JanetCartan.ContinuumRow.TransportKernel
