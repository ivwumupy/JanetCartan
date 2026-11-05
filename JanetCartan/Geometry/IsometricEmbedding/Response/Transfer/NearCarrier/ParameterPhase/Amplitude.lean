module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Carrier
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Full-amplitude carrier chain rule

The amplitude term of `app:ch_response:thm:response-literal-transfer`, before
`app:ch_response:eq:direct-envelope-profile`. The two physical positions are
retained. The selector is allowed explicit parameter dependence, and its
normalized covector derivative is retained in the formula.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer

open FourierIntegral

variable {n r : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The full amplitude evaluated on the physical carrier, with a normalized
selector (`app:ch_response:thm:response-literal-transfer`). -/
def parameterSelectedAmplitude (A : FullAmplitude n r)
    (q : P × Euclidean n → ℂ) (x y ζ δ : P → Euclidean n) (ρ : ℝ) (c : P) :=
  q (c, ρ⁻¹ • δ c) • A (x c) (y c) (ρ • ζ c + δ c)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The parameter amplitude is the existing full selected amplitude at the
physical shifted covector (`app:ch_response:thm:response-literal-transfer`). -/
theorem parameterSelectedAmplitude_eq_selectedAmplitude (A : FullAmplitude n r)
    (q : P × Euclidean n → ℂ) (x y ζ δ : P → Euclidean n) (ρ : ℝ) (c : P) :
    parameterSelectedAmplitude A q x y ζ δ ρ c =
      selectedAmplitude A (ζ c) ρ (fun η ↦ q (c, ρ⁻¹ • η))
        (x c) (y c) (ρ • ζ c + δ c) := by
  simp [parameterSelectedAmplitude, selectedAmplitude]

/-- Chain rule retaining both physical positions in the full amplitude of
`app:ch_response:thm:response-literal-transfer`. In particular `x'` and `y'`
need not vanish when parameters also include physical derivatives. -/
theorem hasFDerivAt_shiftedFullAmplitude
    (A : FullAmplitude n r) (x y ζ δ : P → Euclidean n) (ρ : ℝ) (c : P)
    (x' y' ζ' δ' : P →L[ℝ] Euclidean n)
    (A' : (Euclidean n × Euclidean n × Euclidean n) →L[ℝ]
      Matrix (Fin r) (Fin r) ℂ)
    (hx : HasFDerivAt x x' c) (hy : HasFDerivAt y y' c)
    (hζ : HasFDerivAt ζ ζ' c) (hδ : HasFDerivAt δ δ' c)
    (hA : HasFDerivAt (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2) A' (x c, y c, ρ • ζ c + δ c)) :
    HasFDerivAt (fun c ↦ A (x c) (y c) (ρ • ζ c + δ c))
      (A'.comp (x'.prod (y'.prod (ρ • ζ' + δ')))) c := by
  have h := hA.comp c (hx.prodMk (hy.prodMk ((hζ.const_smul ρ).add hδ)))
  exact h

/-- Exact chain and product rules for the selected full amplitude in
`app:ch_response:thm:response-literal-transfer`. The second summand is the
selector derivative, including its explicit parameter dependence and its
`ρ⁻¹ δ'` covector term. No support or derivative term is dropped. -/
theorem hasFDerivAt_parameterSelectedAmplitude
    (A : FullAmplitude n r) (q : P × Euclidean n → ℂ)
    (x y ζ δ : P → Euclidean n) (ρ : ℝ) (c : P)
    (x' y' ζ' δ' : P →L[ℝ] Euclidean n)
    (A' : (Euclidean n × Euclidean n × Euclidean n) →L[ℝ]
      Matrix (Fin r) (Fin r) ℂ) (q' : (P × Euclidean n) →L[ℝ] ℂ)
    (hx : HasFDerivAt x x' c) (hy : HasFDerivAt y y' c)
    (hζ : HasFDerivAt ζ ζ' c) (hδ : HasFDerivAt δ δ' c)
    (hA : HasFDerivAt (fun p : Euclidean n × Euclidean n × Euclidean n ↦
      A p.1 p.2.1 p.2.2) A' (x c, y c, ρ • ζ c + δ c))
    (hq : HasFDerivAt q q' (c, ρ⁻¹ • δ c)) :
    HasFDerivAt (parameterSelectedAmplitude A q x y ζ δ ρ)
      (q (c, ρ⁻¹ • δ c) • (A'.comp (x'.prod (y'.prod (ρ • ζ' + δ')))) +
        (q'.comp ((ContinuousLinearMap.id ℝ P).prod (ρ⁻¹ • δ'))).smulRight
          (A (x c) (y c) (ρ • ζ c + δ c))) c := by
  have hqc := hq.comp c ((hasFDerivAt_id c).prodMk (hδ.const_smul ρ⁻¹))
  exact hqc.smul
    (hasFDerivAt_shiftedFullAmplitude A x y ζ δ ρ c x' y' ζ' δ' A' hx hy hζ hδ hA)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The factor `ρ` from differentiating `ρ ζ(c)` cancels one normalized
covector derivative in `app:ch_response:thm:response-literal-transfer`.
Here `D` is the primitive physical covector derivative of the amplitude. -/
theorem norm_carrierCovector_chain_le (D : Euclidean n →L[ℝ] F)
    (ζ' : P →L[ℝ] Euclidean n) (ρ M : ℝ) (hρ : 0 < ρ)
    (hD : ‖D‖ ≤ M / ρ) :
    ‖D.comp (ρ • ζ')‖ ≤ M * ‖ζ'‖ := by
  calc
    ‖D.comp (ρ • ζ')‖ ≤ ‖D‖ * ‖ρ • ζ'‖ := D.opNorm_comp_le _
    _ ≤ (M / ρ) * ‖ρ • ζ'‖ := mul_le_mul_of_nonneg_right hD (norm_nonneg _)
    _ = M * ‖ζ'‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      field_simp

/-- Cancellation at every covector order: `k` factors of `ρ` from carrier
differentiation cancel the primitive symbol weight `ρ⁻ᵏ`. This is the
normalized order-zero counting used before
`app:ch_response:eq:direct-envelope-profile`. Physical derivative orders may
already have been taken in the supplied multilinear primitive `D`. -/
theorem norm_carrierCovector_multilinear_le {k : ℕ}
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ Euclidean n) F)
    (v : Fin k → Euclidean n) (ρ M : ℝ) (hρ : 0 < ρ)
    (hD : ‖D‖ ≤ M / ρ ^ k) :
    ‖D (fun i ↦ ρ • v i)‖ ≤ M * ∏ i, ‖v i‖ := by
  calc
    ‖D (fun i ↦ ρ • v i)‖ ≤ ‖D‖ * ∏ i, ‖ρ • v i‖ := D.le_opNorm _
    _ ≤ (M / ρ ^ k) * ∏ i, ‖ρ • v i‖ :=
      mul_le_mul_of_nonneg_right hD (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))
    _ = M * ∏ i, ‖v i‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      field_simp

end JanetCartan.ResponseTransfer
