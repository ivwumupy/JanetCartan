module
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.ParameterIntegral
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Diagonal
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.FrequencyBounds

/-!
# Frequency estimates for the explicit diagonal remainder

The Taylor integral and frequency divergence of
`app:ch_regular_base:eq:actual-pdo-remainder`. At frequency order `n` the
remainder uses one source derivative and `n + 1` frequency derivatives of the
primitive amplitude: the fixed total shift is two. The cutoff is retained.

These are pointwise frequency-jet bounds, with the supremum along the source
segment supplied explicitly. Mixed physical/frequency symbol seminorm estimates
and the unregularized oscillatory limit remain separate obligations.
-/

@[expose] public noncomputable section
open scoped ContDiff
open MeasureTheory Set
universe u v
namespace JanetCartan.Pseudodifferential
variable {V : Type u} {F : Type (max u v)}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [FiniteDimensional ℝ V] in
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: joint smoothness of the actual source Taylor
integrand. -/
theorem contDiff_sourceTaylorIntegrand (c : V → V → V → F) (x y : V)
    (hc : ContDiff ℝ ∞ (fun p : V × V ↦ c x p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : V × ℝ ↦
      fderiv ℝ (fun z ↦ c x z p.1) (x + p.2 • (y - x))) := by
  have h : ContDiff ℝ ∞ (fun q : (V × ℝ) × V ↦ c x q.2 q.1.1) :=
    hc.comp (contDiff_snd.prodMk contDiff_fst.fst)
  exact h.fderiv (contDiff_const.add (contDiff_snd.smul contDiff_const)) (by simp)

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: frequency smoothness of the constructed Taylor
coefficient, derived from the primitive amplitude. -/
theorem contDiff_fullTaylorCoefficient_frequency (c : V → V → V → F) (β : V → ℝ)
    (x y : V) (hc : ContDiff ℝ ∞ (fun p : V × V ↦ c x p.1 p.2)) :
    ContDiff ℝ ∞ (fullTaylorCoefficient c β x y) :=
  (contDiff_unitIntervalIntegral _ (contDiff_sourceTaylorIntegrand c x y hc)).const_smul (β y)

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: frequency derivatives of the Taylor coefficient
cost precisely one source derivative; the unit interval introduces no extra loss. -/
theorem norm_iteratedFDeriv_fullTaylorCoefficient_frequency_le
    (c : V → V → V → F) (β : V → ℝ) (x y ξ : V) (n : ℕ)
    (hc : ContDiff ℝ ∞ (fun p : V × V ↦ c x p.1 p.2)) (M : ℝ)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ n (fun η ↦ fderiv ℝ (fun z ↦ c x z η)
        (x + t • (y - x))) ξ‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fullTaylorCoefficient c β x y) ξ‖ ≤ |β y| * M := by
  let g : V × ℝ → V →L[ℝ] F := fun p ↦
    fderiv ℝ (fun z ↦ c x z p.1) (x + p.2 • (y - x))
  have hg : ContDiff ℝ ∞ g := contDiff_sourceTaylorIntegrand c x y hc
  have hi := norm_iteratedFDeriv_unitIntervalIntegral_le n g hg ξ M hM
  have hs := (contDiff_unitIntervalIntegral g hg).of_le (show (n : WithTop ℕ∞) ≤ ∞ by simp)
  have heq : iteratedFDeriv ℝ n (fullTaylorCoefficient c β x y) ξ =
      β y • iteratedFDeriv ℝ n (fun z ↦ ∫ t in (0 : ℝ)..1, g (z, t)) ξ := by
    exact iteratedFDeriv_const_smul_apply (a := β y) hs.contDiffAt
  rw [heq, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hi (abs_nonneg _)
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the frequency derivative passes inside the
explicit source Taylor integral. -/
theorem fderiv_fullTaylorCoefficient_frequency (c : V → V → V → F) (β : V → ℝ)
    (x y ξ : V) (hc : ContDiff ℝ ∞ (fun p : V × V ↦ c x p.1 p.2)) :
    fderiv ℝ (fullTaylorCoefficient c β x y) ξ =
      β y • ∫ t in (0 : ℝ)..1, fderiv ℝ (fun η ↦
        fderiv ℝ (fun z ↦ c x z η) (x + t • (y - x))) ξ :=
  ((hasFDerivAt_unitIntervalIntegral _
    (contDiff_sourceTaylorIntegrand c x y hc) ξ).const_smul (β y)).fderiv

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: a finite frequency-jet bound for the actual
remainder, with total primitive derivative order `n + 2` and a fixed dimensional constant. -/
theorem norm_iteratedFDeriv_diagonalRemainderAmplitude_frequency_le
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β : V → ℝ) (x y ξ : V) (n : ℕ)
    (hc : ContDiff ℝ ∞ (fun p : V × V ↦ c x p.1 p.2)) (M : ℝ)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (n + 1) (fun η ↦ fderiv ℝ (fun z ↦ c x z η)
        (x + t • (y - x))) ξ‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (diagonalRemainderAmplitude b c β x y) ξ‖ ≤
      ‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι * (|β y| * M) := by
  apply (norm_iteratedFDeriv_normalizedFrequencyDivergence_le b _ n
    ((contDiff_fullTaylorCoefficient_frequency c β x y hc).of_le (by simp)) ξ).trans
  exact mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_fullTaylorCoefficient_frequency_le c β x y ξ (n + 1) hc M hM)
    (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))

variable [MeasurableSpace V] [BorelSpace V] [CompleteSpace F]
local instance : ContinuousENorm (V →L[ℝ] V →L[ℝ] F) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid
    (V →L[ℝ] V →L[ℝ] F) inferInstance).toContinuousENorm

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: exact diagonal kernel reduction with
coefficient differentiability discharged from joint smoothness of the primitive. Absolute
integrability remains explicit. -/
theorem amplitudeKernel_eq_diagonal_add_remainder_of_contDiff
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β : V → ℝ) (x y : V)
    (hc : ContDiff ℝ ∞ (fun p : V × V ↦ c x p.1 p.2))
    (hβ : ∀ ξ z, c x z ξ ≠ 0 → β z = 1)
    (hdiag : Integrable (diagonalAmplitude c β x y))
    (hB : Integrable (fullTaylorCoefficient c β x y))
    (hDB : Integrable (fderiv ℝ (fullTaylorCoefficient c β x y))) :
    amplitudeKernel c x y = amplitudeKernel (diagonalAmplitude c β) x y +
      amplitudeKernel (diagonalRemainderAmplitude b c β) x y := by
  apply amplitudeKernel_eq_diagonal_add_remainder b c β x y _ hβ hdiag hB _ hDB
  · intro ξ
    exact (hc.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  · exact (contDiff_fullTaylorCoefficient_frequency c β x y hc).differentiable (by simp)
end JanetCartan.Pseudodifferential
