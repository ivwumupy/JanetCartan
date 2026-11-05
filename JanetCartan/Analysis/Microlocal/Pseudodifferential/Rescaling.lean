module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.JointRemainder

/-!
# Frequency rescaling of the exact diagonal remainder

The finite remainder in `app:ch_regular_base:eq:actual-pdo-remainder` gains one
inverse frequency scale. The estimates control joint derivatives with the
frequency rescaled and therefore retain the anisotropic frequency budget.
-/

@[expose] public noncomputable section
open scoped ContDiff
open MeasureTheory Set
universe u v
namespace JanetCartan.Pseudodifferential
variable {V : Type u} {F : Type (max u v)} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: frequency divergence under a dilation. -/
theorem normalizedFrequencyDivergence_rescale
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (B : V → V →L[ℝ] F) (hB : Differentiable ℝ B) (ρ : ℝ) (ξ : V) :
    normalizedFrequencyDivergence b (fun η ↦ B (ρ • η)) ξ =
      ρ • normalizedFrequencyDivergence b B (ρ • ξ) := by
  have hD : fderiv ℝ (fun η ↦ B (ρ • η)) ξ =
      (fderiv ℝ B (ρ • ξ)).comp (ρ • ContinuousLinearMap.id ℝ V) :=
    ((hB (ρ • ξ)).hasFDerivAt.comp ξ ((hasFDerivAt_id ξ).const_smul ρ)).fderiv
  simp only [normalizedFrequencyDivergence, frequencyDivergence, hD,
    ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ smul_comm _ _ _

variable [FiniteDimensional ℝ V]
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the actual full remainder under a frequency dilation. -/
theorem diagonalRemainderAmplitude_rescale
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β : V → ℝ)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (ρ : ℝ) (x y ξ : V) :
    diagonalRemainderAmplitude b (fun x y η ↦ c x y (ρ • η)) β x y ξ =
      ρ • diagonalRemainderAmplitude b c β x y (ρ • ξ) := by
  have hcx : ContDiff ℝ ∞ (fun p : V × V ↦ c x p.1 p.2) :=
    hc.comp (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd))
  exact normalizedFrequencyDivergence_rescale b (fullTaylorCoefficient c β x y)
    ((contDiff_fullTaylorCoefficient_frequency c β x y hcx).differentiable (by simp)) ρ ξ

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the rescaled joint remainder gains one inverse frequency scale with fixed shift two. -/
theorem norm_iteratedFDeriv_diagonalRemainderAmplitude_rescaled_le
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (c : V → V → V → F) (β : V → ℝ)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (ρ : ℝ) (hρ : 0 < ρ)
    (p : V × V × V) (n : ℕ) (M : ℕ → ℝ)
    (hM : ∀ k ≤ n + 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (k + 1) (fun q : V × V × V ↦ c q.1 q.2.1 (ρ • q.2.2))
        (sourceSegmentMap t p)‖ ≤ M k) :
    ‖iteratedFDeriv ℝ n (fun q : V × V × V ↦
      diagonalRemainderAmplitude b c β q.1 q.2.1 (ρ • q.2.2)) p‖ ≤
      ρ⁻¹ * (‖(2 * Real.pi * Complex.I)⁻¹‖ * Fintype.card ι *
        ∑ i ∈ Finset.range (n + 2), ((n + 1).choose i : ℝ) *
          ‖iteratedFDeriv ℝ i β p.2.1‖ * M (n + 1 - i)) := by
  let cρ := fun x y ξ ↦ c x y (ρ • ξ)
  have hcρ : ContDiff ℝ ∞ (fun q : V × V × V ↦ cρ q.1 q.2.1 q.2.2) :=
    hc.comp (contDiff_fst.prodMk (contDiff_snd.fst.prodMk (contDiff_snd.snd.const_smul ρ)))
  have heq : (fun q : V × V × V ↦ diagonalRemainderAmplitude b c β q.1 q.2.1 (ρ • q.2.2)) =
      (fun q ↦ ρ⁻¹ • diagonalRemainderAmplitude b cρ β q.1 q.2.1 q.2.2) := by
    funext q
    rw [diagonalRemainderAmplitude_rescale b c β hc ρ, inv_smul_smul₀ hρ.ne']
  rw [heq]
  have hr := contDiff_diagonalRemainderAmplitude_joint b cρ β hcρ hβ
  have hder : iteratedFDeriv ℝ n (fun q : V × V × V ↦
      ρ⁻¹ • diagonalRemainderAmplitude b cρ β q.1 q.2.1 q.2.2) p =
      ρ⁻¹ • iteratedFDeriv ℝ n (fun q : V × V × V ↦
        diagonalRemainderAmplitude b cρ β q.1 q.2.1 q.2.2) p :=
    iteratedFDeriv_const_smul_apply (a := ρ⁻¹)
      (hr.of_le (show (n : WithTop ℕ∞) ≤ ∞ by simp)).contDiffAt
  rw [hder, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
  exact mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_diagonalRemainderAmplitude_joint_le b cρ β hcρ hβ p n M hM)
    (inv_nonneg.mpr hρ.le)
end JanetCartan.Pseudodifferential
