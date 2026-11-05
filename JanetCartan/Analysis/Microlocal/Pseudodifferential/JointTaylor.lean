module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.JointBounds

/-!
# Joint derivatives of the source Taylor integral

The actual Taylor coefficient in `app:ch_regular_base:eq:actual-pdo-remainder`
has a fixed shift of one in all three variables. The finite Leibniz sum retains
every derivative of the physical source cutoff.
-/

@[expose] public noncomputable section
open scoped ContDiff
open MeasureTheory Set
universe u v
namespace JanetCartan.Pseudodifferential
variable {V : Type u} {F : Type (max u v)} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the unmasked Taylor integral in joint variables. -/
def jointSourceTaylorIntegral (c : V → V → V → F) (p : V × V × V) :
    V →L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ (fun z ↦ c p.1 z p.2.2) ((1 - t) • p.1 + t • p.2.1)

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the source cutoff times the actual Taylor integral. -/
theorem fullTaylorCoefficient_eq_jointSourceTaylorIntegral
    (c : V → V → V → F) (β : V → ℝ) (p : V × V × V) :
    fullTaylorCoefficient c β p.1 p.2.1 p.2.2 = β p.2.1 • jointSourceTaylorIntegral c p := by
  unfold fullTaylorCoefficient sourceTaylorCoefficient jointSourceTaylorIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only [sub_smul, smul_sub, one_smul]
  abel_nf

variable [FiniteDimensional ℝ V]
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: joint smoothness of the Taylor integral. -/
theorem contDiff_jointSourceTaylorIntegral (c : V → V → V → F)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2)) :
    ContDiff ℝ ∞ (jointSourceTaylorIntegral c) :=
  contDiff_unitIntervalIntegral _ (contDiff_jointSourceIntegrand c hc)

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: a fixed shift of one bounds every joint derivative of the Taylor integral. -/
theorem norm_iteratedFDeriv_jointSourceTaylorIntegral_le (c : V → V → V → F)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (p : V × V × V) (n : ℕ) (M : ℝ)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (n + 1) (fun q : V × V × V ↦ c q.1 q.2.1 q.2.2)
        (sourceSegmentMap t p)‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (jointSourceTaylorIntegral c) p‖ ≤ M := by
  apply norm_iteratedFDeriv_unitIntervalIntegral_le n _ (contDiff_jointSourceIntegrand c hc)
  intro t ht
  exact (norm_iteratedFDeriv_jointSourceIntegrand_le c hc p n t ht).trans (hM t ht)

omit [FiniteDimensional ℝ V] in
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: source projection introduces no derivative loss. -/
theorem norm_iteratedFDeriv_sourceCutoff_le (β : V → ℝ) (hβ : ContDiff ℝ ∞ β)
    (p : V × V × V) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q : V × V × V ↦ β q.2.1) p‖ ≤
      ‖iteratedFDeriv ℝ n β p.2.1‖ := by
  let L : (V × V × V) →L[ℝ] V :=
    (ContinuousLinearMap.fst ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V))
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    exact (norm_fst_le q.2).trans ((norm_snd_le q).trans_eq (one_mul _).symm)
  change ‖iteratedFDeriv ℝ n (β ∘ L) p‖ ≤ _
  exact (norm_iteratedFDeriv_comp_linear_le L β hβ n p).trans
    (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL))

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the actual Taylor coefficient is jointly smooth. -/
theorem contDiff_fullTaylorCoefficient_joint (c : V → V → V → F) (β : V → ℝ)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (fun p : V × V × V ↦ fullTaylorCoefficient c β p.1 p.2.1 p.2.2) := by
  have heq : (fun q : V × V × V ↦ fullTaylorCoefficient c β q.1 q.2.1 q.2.2) =
      (fun q ↦ β q.2.1 • jointSourceTaylorIntegral c q) :=
    funext (fullTaylorCoefficient_eq_jointSourceTaylorIntegral c β)
  rw [heq]
  exact (hβ.comp contDiff_snd.fst).smul (contDiff_jointSourceTaylorIntegral c hc)

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: a finite Leibniz sum bounds joint derivatives of the actual masked Taylor coefficient. -/
theorem norm_iteratedFDeriv_fullTaylorCoefficient_joint_le
    (c : V → V → V → F) (β : V → ℝ)
    (hc : ContDiff ℝ ∞ (fun p : V × V × V ↦ c p.1 p.2.1 p.2.2))
    (hβ : ContDiff ℝ ∞ β) (p : V × V × V) (n : ℕ) (M : ℕ → ℝ)
    (hM : ∀ k ≤ n, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (k + 1) (fun q : V × V × V ↦ c q.1 q.2.1 q.2.2)
        (sourceSegmentMap t p)‖ ≤ M k) :
    ‖iteratedFDeriv ℝ n (fun q : V × V × V ↦ fullTaylorCoefficient c β q.1 q.2.1 q.2.2) p‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i β p.2.1‖ * M (n - i) := by
  have heq : (fun q : V × V × V ↦ fullTaylorCoefficient c β q.1 q.2.1 q.2.2) =
      (fun q ↦ β q.2.1 • jointSourceTaylorIntegral c q) :=
    funext (fullTaylorCoefficient_eq_jointSourceTaylorIntegral c β)
  rw [heq]
  apply (norm_iteratedFDeriv_smul_le (hβ.comp contDiff_snd.fst)
    (contDiff_jointSourceTaylorIntegral c hc) p (by simp)).trans
  apply Finset.sum_le_sum
  intro i _
  have hI := norm_iteratedFDeriv_jointSourceTaylorIntegral_le c hc p (n - i) (M (n - i))
    (hM (n - i) (Nat.sub_le _ _))
  calc
    _ ≤ (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i β p.2.1‖ *
        ‖iteratedFDeriv ℝ (n - i) (jointSourceTaylorIntegral c) p‖ := by
      gcongr
      exact norm_iteratedFDeriv_sourceCutoff_le β hβ p i
    _ ≤ _ := mul_le_mul_of_nonneg_left hI (by positivity)
end JanetCartan.Pseudodifferential
