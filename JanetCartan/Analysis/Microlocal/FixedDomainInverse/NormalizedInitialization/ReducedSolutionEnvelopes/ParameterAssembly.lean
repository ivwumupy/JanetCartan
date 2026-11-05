module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Inverse
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Ordered parameter envelopes from one finite Neumann expansion

Differentiate the literal finite expansion of the SAME inverse and observation.
The source and operator do not change with the depth. The analytic inputs are
the finite residual-word envelopes and the observed parameter remainder from
`ParameterRemainder` and `ObservedParameterRemainders`; neither is inferred from
an un-differentiated envelope. This deduction is used in
`app:ch_response:eq:response-graded-reduced` before the original-cell classical
reconstruction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Finset
open scoped ContDiff

namespace JanetCartan.FixedDomainInverse

open ResponseTransfer

variable {P E F ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every genuine parameter jet satisfies the same finite Neumann identity.
Only regularity of the actual finite words and remainder is used, supplied by
the common supported smooth realization. There is no derivative-of-inverse
assumption (`app:ch_regular:eq:finite-neumann-identity`). -/
theorem iteratedFDeriv_finite_neumann_observation_identity
    (R T : E →L[ℝ] E) (hT : T * (1 + R) = 1)
    (B : P → E →ₗ[ℝ] F) (source : P → E)
    (depth k : ℕ) (c : P) (v : Fin k → P)
    (hchain : ∀ j ∈ range depth,
      ContDiffAt ℝ ∞ (fun q ↦ B q ((R ^ j) (source q))) c)
    (hrem : ContDiffAt ℝ ∞ (fun q ↦ B q (T ((R ^ depth) (source q)))) c) :
    iteratedFDeriv ℝ k (fun q ↦ B q (T (source q))) c v -
        (∑ j ∈ range depth, ((-1 : ℝ) ^ j) •
          iteratedFDeriv ℝ k (fun q ↦ B q ((R ^ j) (source q))) c v) =
      ((-1 : ℝ) ^ depth) •
        iteratedFDeriv ℝ k (fun q ↦ B q (T ((R ^ depth) (source q)))) c v := by
  let word := fun j q ↦ B q ((R ^ j) (source q))
  let remainder := fun q ↦ B q (T ((R ^ depth) (source q)))
  have he : (fun q ↦ B q (T (source q))) =
      (fun q ↦ ∑ j ∈ range depth, ((-1 : ℝ) ^ j) • word j q) +
        ((-1 : ℝ) ^ depth) • remainder := by
    funext q
    exact sub_eq_iff_eq_add'.mp
      (finite_neumann_observation_identity R T hT (B q) depth (source q))
  have hword : ∀ j ∈ range depth,
      ContDiffAt ℝ k (fun q ↦ ((-1 : ℝ) ^ j) • word j q) c :=
    fun j hj ↦ ((hchain j hj).const_smul _).of_le (by simp)
  have hremk : ContDiffAt ℝ k (((-1 : ℝ) ^ depth) • remainder) c :=
    (hrem.const_smul ((-1 : ℝ) ^ depth)).of_le (by simp)
  rw [he, iteratedFDeriv_add_apply (ContDiffAt.sum hword) hremk,
    iteratedFDeriv_fun_sum_apply hword]
  simp only [add_apply, _root_.sum_apply]
  have hjet (j : ℕ) (hj : j ∈ range depth) :
      iteratedFDeriv ℝ k (fun q ↦ ((-1 : ℝ) ^ j) • word j q) c v =
        ((-1 : ℝ) ^ j) • iteratedFDeriv ℝ k (word j) c v := by
    rw [iteratedFDeriv_const_smul_apply' (a := ((-1 : ℝ)^j))
      (show ContDiffAt ℝ k (word j) c from (hchain j hj).of_le (by simp))]
    rfl
  rw [iteratedFDeriv_const_smul_apply (hrem.of_le (by simp))]
  simp only [smul_apply]
  rw [Finset.sum_congr rfl hjet]
  change ((∑ j ∈ range depth, ((-1 : ℝ)^j) • iteratedFDeriv ℝ k (word j) c v) +
      ((-1 : ℝ)^depth) • iteratedFDeriv ℝ k remainder c v) - _ = _
  exact add_sub_cancel_left _ _

/-- Uniform finite-word parameter envelopes and the actual observed remainder
give the same parameter envelope for the single complete inverse. This is the
downstream algebraic use of the characteristic/reflected/full-elliptic word
producer and `ObservedParameterRemainders`. Its remainder constant and depth
are chosen before histories, parameters, and unit directions. The exact
total grade `s+k` is preserved; the statement does not construct either
analytic input (`app:ch_response:eq:response-graded-reduced`). -/
theorem parameter_inverse_envelope_of_finite_remainders
    (H : GradedScale F) (R T : ι → E →L[ℝ] E)
    (hT : ∀ i, T i * (1 + R i) = 1)
    (B : ι → P → E →ₗ[ℝ] F) (source : ι → P → E)
    (V : Set P) (hV : IsOpen V) (A K : ι → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 1 ≤ K i)
    (hchainSmooth : ∀ i j, ContDiffOn ℝ ∞
      (fun q ↦ B i q (((R i) ^ j) (source i q))) V)
    (hremSmooth : ∀ i depth, ContDiffOn ℝ ∞
      (fun q ↦ B i q (T i (((R i) ^ depth) (source i q)))) V)
    (hchain : ∀ j s k, ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → P, (∀ l, ‖v l‖ ≤ 1) →
        let f := iteratedFDeriv ℝ k (fun q ↦ B i q (((R i)^j) (source i q))) c v
        f ∈ H.level s ∧ H.gradeNorm s f ≤ C * A i * K i ^ (s + k))
    (hrem : ∀ s k, ∃ (depth : ℕ) (D : ℝ), 0 ≤ D ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → P, (∀ l, ‖v l‖ ≤ 1) →
        let f := iteratedFDeriv ℝ k
          (fun q ↦ B i q (T i (((R i)^depth) (source i q)))) c v
        f ∈ H.level s ∧ H.gradeNorm s f ≤ D * A i) :
    ∀ s k, ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → P, (∀ l, ‖v l‖ ≤ 1) →
        let f := iteratedFDeriv ℝ k (fun q ↦ B i q (T i (source i q))) c v
        f ∈ H.level s ∧ H.gradeNorm s f ≤ C * A i * K i ^ (s + k) := by
  intro s k
  obtain ⟨depth, D, hD, hremain⟩ := hrem s k
  choose C hC hwords using fun j ↦ hchain j s k
  refine ⟨(∑ j ∈ range depth, C j) + D,
    add_nonneg (Finset.sum_nonneg fun j _ ↦ hC j) hD, ?_⟩
  intro i c hc v hv f
  let word := fun j ↦ iteratedFDeriv ℝ k
    (fun q ↦ B i q (((R i)^j) (source i q))) c v
  let remainder := iteratedFDeriv ℝ k
    (fun q ↦ B i q (T i (((R i)^depth) (source i q)))) c v
  have he : f - (∑ j ∈ range depth, ((-1 : ℝ)^j) • word j) =
      ((-1 : ℝ)^depth) • remainder :=
    iteratedFDeriv_finite_neumann_observation_identity (R i) (T i) (hT i)
      (B i) (source i) depth k c v
      (fun j _ ↦ (hchainSmooth i j).contDiffAt (hV.mem_nhds hc))
      ((hremSmooth i depth).contDiffAt (hV.mem_nhds hc))
  obtain ⟨hrmem, hrbound⟩ := hremain i c hc v hv
  have hremainmem : f - (∑ j ∈ range depth, ((-1 : ℝ)^j) • word j) ∈ H.level s := by
    rw [he]
    exact (H.level s).smul_mem _ hrmem
  have hremainbound : H.gradeNorm s
      (f - (∑ j ∈ range depth, ((-1 : ℝ)^j) • word j)) ≤ D * (A i * K i ^ k) := by
    rw [he, H.gradeNorm_neg_one_pow_smul s depth hrmem]
    exact hrbound.trans ((le_mul_of_one_le_right (mul_nonneg hD (hA i))
      (one_le_pow₀ (hK i))).trans_eq (by ring))
  have hwordbound (j : ℕ) (_hj : j < depth) :
      word j ∈ H.level s ∧ H.gradeNorm s (word j) ≤ C j * (A i * K i ^ k) * K i ^ s := by
    obtain ⟨hm, hb⟩ := hwords j i c hc v hv
    refine ⟨hm, hb.trans_eq ?_⟩
    rw [pow_add]
    ring
  obtain ⟨hfmem, hfbound⟩ := signed_sum_remainder_bound H s depth word f C
    (mul_nonneg (hA i) (pow_nonneg (zero_le_one.trans (hK i)) _)) (hK i) hD
    hwordbound hremainmem hremainbound
  refine ⟨hfmem, hfbound.trans_eq ?_⟩
  rw [pow_add]
  ring

/-- Preserve the original natural derivative reserve in the SAME inverse.
The finite-word producer supplies `K^((s+k-reserve : ℕ))`; no negative
power is inferred at low total order. The arbitrary-accuracy remainder
needs only the unreserved bound `D*A`, since every natural power of `K`
is at least one. This is the version consumed by the original-cell
reconstruction and prepared atom estimates
(`app:ch_response:eq:response-graded-reduced`,
`app:ch_response:cor:current-atoms`). -/
theorem parameter_inverse_reserved_envelope_of_finite_remainders
    (H : GradedScale F) (R T : ι → E →L[ℝ] E)
    (hT : ∀ i, T i * (1 + R i) = 1)
    (B : ι → P → E →ₗ[ℝ] F) (source : ι → P → E)
    (V : Set P) (hV : IsOpen V) (A K : ι → ℝ) (reserve : ℕ)
    (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 1 ≤ K i)
    (hchainSmooth : ∀ i j, ContDiffOn ℝ ∞
      (fun q ↦ B i q (((R i) ^ j) (source i q))) V)
    (hremSmooth : ∀ i depth, ContDiffOn ℝ ∞
      (fun q ↦ B i q (T i (((R i) ^ depth) (source i q)))) V)
    (hchain : ∀ j s k, ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → P, (∀ l, ‖v l‖ ≤ 1) →
        let f := iteratedFDeriv ℝ k (fun q ↦ B i q (((R i)^j) (source i q))) c v
        f ∈ H.level s ∧ H.gradeNorm s f ≤ C * A i * K i ^ (s+k-reserve))
    (hrem : ∀ s k, ∃ (depth : ℕ) (D : ℝ), 0 ≤ D ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → P, (∀ l, ‖v l‖ ≤ 1) →
        let f := iteratedFDeriv ℝ k
          (fun q ↦ B i q (T i (((R i)^depth) (source i q)))) c v
        f ∈ H.level s ∧ H.gradeNorm s f ≤ D * A i) :
    ∀ s k, ∃ C : ℝ, 0 ≤ C ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → P, (∀ l, ‖v l‖ ≤ 1) →
        let f := iteratedFDeriv ℝ k (fun q ↦ B i q (T i (source i q))) c v
        f ∈ H.level s ∧ H.gradeNorm s f ≤ C * A i * K i ^ (s+k-reserve) := by
  intro s k
  obtain ⟨depth, D, hD, hremain⟩ := hrem s k
  choose C hC hwords using fun j ↦ hchain j s k
  refine ⟨(∑ j ∈ range depth, C j) + D,
    add_nonneg (Finset.sum_nonneg fun j _ ↦ hC j) hD, ?_⟩
  intro i c hc v hv f
  let word := fun j ↦ iteratedFDeriv ℝ k
    (fun q ↦ B i q (((R i)^j) (source i q))) c v
  let remainder := iteratedFDeriv ℝ k
    (fun q ↦ B i q (T i (((R i)^depth) (source i q)))) c v
  have he : f - (∑ j ∈ range depth, ((-1 : ℝ)^j) • word j) =
      ((-1 : ℝ)^depth) • remainder :=
    iteratedFDeriv_finite_neumann_observation_identity (R i) (T i) (hT i)
      (B i) (source i) depth k c v
      (fun j _ ↦ (hchainSmooth i j).contDiffAt (hV.mem_nhds hc))
      ((hremSmooth i depth).contDiffAt (hV.mem_nhds hc))
  obtain ⟨hrmem, hrbound⟩ := hremain i c hc v hv
  have hremainmem : f - (∑ j ∈ range depth, ((-1 : ℝ)^j) • word j) ∈ H.level s := by
    rw [he]
    exact (H.level s).smul_mem _ hrmem
  have hremainbound : H.gradeNorm s
      (f - (∑ j ∈ range depth, ((-1 : ℝ)^j) • word j)) ≤
        D * (A i * K i ^ (s+k-reserve)) := by
    rw [he, H.gradeNorm_neg_one_pow_smul s depth hrmem]
    exact hrbound.trans ((le_mul_of_one_le_right (mul_nonneg hD (hA i))
      (one_le_pow₀ (hK i))).trans_eq (by ring))
  have hwordbound (j : ℕ) (_hj : j < depth) :
      word j ∈ H.level s ∧ H.gradeNorm s (word j) ≤
        C j * (A i * K i ^ (s+k-reserve)) * (1 : ℝ)^s := by
    obtain ⟨hm, hb⟩ := hwords j i c hc v hv
    exact ⟨hm, hb.trans_eq (by simp only [one_pow, mul_one]; ring)⟩
  obtain ⟨hfmem, hfbound⟩ := signed_sum_remainder_bound H s depth word f C
    (mul_nonneg (hA i) (pow_nonneg (zero_le_one.trans (hK i)) _)) le_rfl hD
    hwordbound hremainmem hremainbound
  refine ⟨hfmem, hfbound.trans_eq ?_⟩
  simp only [one_pow, mul_one]
  ring

end JanetCartan.FixedDomainInverse
