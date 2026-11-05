module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.Remainder

/-!
# Fixed masks and literal adjoint amplitudes

The source, target and angle masks in
`app:ch_regular_base:eq:actual-global-cutoff` are retained as three independent
primitives. The estimates apply in the full joint domain, so no derivative of
any mask is omitted. Matrix adjunction is the literal conjugate transpose in
the Frobenius norm, as required in `app:ch_regular_base:eq:actual-one-high`.
-/

@[expose] public noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℂ R]

/-- The three actual cutoff multipliers have a single total derivative budget
in `app:ch_regular_base:eq:actual-global-cutoff`. -/
theorem norm_iteratedFDeriv_maskedTransportAmplitude_le {N : ℕ∞ω}
    {χt χs χg : E → ℂ} {b : E → R}
    (ht : ContDiff ℝ N χt) (hs : ContDiff ℝ N χs)
    (hg : ContDiff ℝ N χg) (hb : ContDiff ℝ N b)
    (x : E) (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun y ↦ maskedTransportAmplitude (χt y) (χs y) (χg y) (b y)) x‖ ≤
      transportLeibnizBound (fun k ↦ ‖iteratedFDeriv ℝ k χt x‖)
        (transportLeibnizBound (fun k ↦ ‖iteratedFDeriv ℝ k χs x‖)
          (transportLeibnizBound (fun k ↦ ‖iteratedFDeriv ℝ k χg x‖)
            (fun k ↦ ‖iteratedFDeriv ℝ k b x‖))) n := by
  apply (norm_iteratedFDeriv_smul_le ht (hs.smul (hg.smul hb)) x hn).trans
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hni : ((n - i : ℕ) : ℕ∞ω) ≤ N :=
    (show ((n - i : ℕ) : ℕ∞ω) ≤ n by exact_mod_cast Nat.sub_le n i).trans hn
  apply (norm_iteratedFDeriv_smul_le hs (hg.smul hb) x hni).trans
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact norm_iteratedFDeriv_smul_le hg hb x
    ((show ((n - i - j : ℕ) : ℕ∞ω) ≤ (n - i : ℕ) by
      exact_mod_cast Nat.sub_le (n - i) j).trans hni)

variable {m : Type*} [Fintype m]

/-- Literal adjunction preserves every finite joint derivative norm, hence
also the normalized seminorm bounds in `app:ch_regular_base:eq:actual-one-high`.
This statement concerns amplitudes; it does not assert an operator identity. -/
theorem norm_iteratedFDeriv_transport_conjTranspose (f : E → Matrix m m ℂ)
    (x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y ↦ (f y).conjTranspose) x‖ =
      ‖iteratedFDeriv ℝ n f x‖ := by
  let L : Matrix m m ℂ ≃ₗᵢ[ℝ] Matrix m m ℂ :=
    { Matrix.conjTransposeLinearEquiv m m ℝ ℂ with
      norm_map' := Matrix.frobenius_norm_conjTranspose }
  exact L.norm_iteratedFDeriv_comp_left f x n

/-- Entrywise conjugation also preserves every joint Frobenius derivative
norm (`app:ch_regular_base:eq:actual-one-high`), including derivatives of masks. -/
theorem norm_iteratedFDeriv_transport_conjugate (f : E → Matrix m m ℂ)
    (x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y ↦ (f y).map star) x‖ =
      ‖iteratedFDeriv ℝ n f x‖ := by
  let L : Matrix m m ℂ ≃ₗᵢ[ℝ] Matrix m m ℂ :=
    { Matrix.transposeLinearEquiv m m ℝ ℂ with
      norm_map' := Matrix.frobenius_norm_transpose }
  exact (L.norm_iteratedFDeriv_comp_left (fun y ↦ (f y).conjTranspose) x n).trans
    (norm_iteratedFDeriv_transport_conjTranspose f x n)

end JanetCartan.FourierIntegral
