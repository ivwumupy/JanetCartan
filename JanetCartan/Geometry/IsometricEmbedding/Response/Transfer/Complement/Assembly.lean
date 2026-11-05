module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.Assembly.Scales
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.Assembly.Costs
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.Assembly

/-!
# Conditional assembly of the complete complementary error

The complete-complement paragraph of
`app:ch_response:thm:response-literal-transfer`. The low/high source split is an
exact identity for one datum and one operator, independent of the proof orders.
The low estimate, high source tail, and polynomial Sobolev cost are analytic
inputs. This module does not construct the literal kernels or their cutoffs.

The abstract graded spaces can be the existing local restriction Sobolev spaces
with their original measures. No identification of torus and Lebesgue data is
made. The family index includes frequency, datum, coefficients and compact
parameters; all constants and integration orders precede that index.
-/

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer.Complement

open ArbitraryAccuracy

variable {ι E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Assemble the complete complementary estimate of
`app:ch_response:thm:response-literal-transfer` from the literal low estimate,
high source tail, and a fixed polynomial cost of the full operator (including
any input carrier). The losses `dLow`, `dHigh`, `b`, and `t` are fixed before
`q,p`; the source split and operator cannot depend on either proof order.
The conclusion is conditional on these analytic estimates, not an existence
claim about the paper's kernels. -/
theorem completeComplement_rapidDecay
    (G : GradedScale E) (H : GradedScale F) (T : ι → E →ₗ[ℝ] F)
    (f low high : ι → E) (ρ L K A : ι → ℝ)
    (s t n b : ℕ) (ν c dLow dHigh D : ℝ)
    (hν : ν ∈ Set.Ioo (0 : ℝ) 1) (hc : 0 < c)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 1 ≤ L i)
    (hLK : ∀ i, L i ≤ K i) (hKρ : ∀ i, K i ≤ (ρ i) ^ (1 - ν))
    (hA : ∀ i, 0 ≤ A i) (hD : 0 ≤ D)
    (hsplit : ∀ i, f i = low i + high i)
    (hTmem : ∀ i v, v ∈ G.level t → T i v ∈ H.level s)
    (hT : ∀ i v, v ∈ G.level t →
      H.gradeNorm s (T i v) ≤ D * (ρ i) ^ dHigh * G.gradeNorm t v)
    (hlow : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      T i (low i) ∈ H.level s ∧
      H.gradeNorm s (T i (low i)) ≤ C * A i * (ρ i) ^ dLow *
        (c * (ρ i) ^ (1 - ν / 2)) ^ ((n : ℝ) / 2) * (L i) ^ b * (L i / ρ i) ^ q)
    (hhigh : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      high i ∈ G.level t ∧ G.gradeNorm t (high i) ≤
        C * A i * (K i) ^ p * (c * (ρ i) ^ (1 - ν / 2)) ^ ((t : ℝ) - p)) :
    RapidDecayAt H s ρ A (fun i ↦ T i (f i)) := by
  intro Q
  obtain ⟨q, p, _, _, hq, hp⟩ := exists_complement_orders hν.1 dLow dHigh Q n b t
  obtain ⟨CL, hCL, hlo⟩ := hlow q
  obtain ⟨CH, hCH, hhi⟩ := hhigh p
  let B := CL * c ^ ((n : ℝ) / 2)
  let C := D * CH * c ^ ((t : ℝ) - p)
  have hB : 0 ≤ B := mul_nonneg hCL (Real.rpow_nonneg hc.le _)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hD hCH) (Real.rpow_nonneg hc.le _)
  refine ⟨B + C, add_nonneg hB hC, ?_⟩
  intro i
  have hρpos : 0 < ρ i := lt_of_lt_of_le zero_lt_one (hρ i)
  have hLi : 0 ≤ L i := le_trans zero_le_one (hL i)
  have hKi : 0 ≤ K i := hLi.trans (hLK i)
  have hlowBound : H.gradeNorm s (T i (low i)) ≤ B * A i * (ρ i) ^ (-Q) := by
    calc
      _ ≤ CL * A i * (ρ i) ^ dLow *
          (c * (ρ i) ^ (1 - ν / 2)) ^ ((n : ℝ) / 2) * (L i) ^ b *
          (L i / ρ i) ^ q := (hlo i).2
      _ = (CL * A i) * ((ρ i) ^ dLow *
          (c * (ρ i) ^ (1 - ν / 2)) ^ ((n : ℝ) / 2) * (L i) ^ b *
          (L i / ρ i) ^ q) := by ring
      _ ≤ (CL * A i) * (c ^ ((n : ℝ) / 2) *
          (ρ i) ^ (dLow + (1 - ν / 2) * ((n : ℝ) / 2) + b - ν * q)) :=
        mul_le_mul_of_nonneg_left
          (lowEnvelope_scale_bound (hρ i) hLi hν.1.le hc ((hLK i).trans (hKρ i)) n b q)
          (mul_nonneg hCL (hA i))
      _ ≤ (CL * A i) * (c ^ ((n : ℝ) / 2) * (ρ i) ^ (-Q)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hρ i) hq)
            (Real.rpow_nonneg hc.le _)) (mul_nonneg hCL (hA i))
      _ = _ := by dsimp [B]; ring
  have hhighBound : H.gradeNorm s (T i (high i)) ≤ C * A i * (ρ i) ^ (-Q) := by
    calc
      _ ≤ D * (ρ i) ^ dHigh * G.gradeNorm t (high i) := hT i _ (hhi i).1
      _ ≤ D * (ρ i) ^ dHigh *
          (CH * A i * (K i) ^ p * (c * (ρ i) ^ (1 - ν / 2)) ^ ((t : ℝ) - p)) :=
        mul_le_mul_of_nonneg_left (hhi i).2 (mul_nonneg hD (Real.rpow_nonneg hρpos.le _))
      _ = (D * CH * A i) * ((ρ i) ^ dHigh * (K i) ^ p *
          (c * (ρ i) ^ (1 - ν / 2)) ^ ((t : ℝ) - p)) := by ring
      _ ≤ (D * CH * A i) * (c ^ ((t : ℝ) - p) *
          (ρ i) ^ (dHigh + (1 - ν / 2) * t - (ν / 2) * p)) :=
        mul_le_mul_of_nonneg_left
          (highEnvelope_scale_bound (hρ i) hKi hc (hKρ i) t p)
          (mul_nonneg (mul_nonneg hD hCH) (hA i))
      _ ≤ (D * CH * A i) * (c ^ ((t : ℝ) - p) * (ρ i) ^ (-Q)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hρ i) hp)
            (Real.rpow_nonneg hc.le _)) (mul_nonneg (mul_nonneg hD hCH) (hA i))
      _ = _ := by dsimp [C]; ring
  dsimp only
  rw [hsplit i, map_add]
  refine ⟨(H.level s).add_mem (hlo i).1 (hTmem i _ (hhi i).1), ?_⟩
  calc
    _ ≤ H.gradeNorm s (T i (low i)) + H.gradeNorm s (T i (high i)) :=
      ResponseTransfer.gradeNorm_add_le H (hlo i).1 (hTmem i _ (hhi i).1)
    _ ≤ B * A i * (ρ i) ^ (-Q) + C * A i * (ρ i) ^ (-Q) :=
      add_le_add hlowBound hhighBound
    _ = _ := by ring

/-- Uniform physical, demodulated, and fixed finite parameter-jet estimates for
`app:ch_response:thm:response-literal-transfer`.

Take `α` to index the two carrier conventions and the finitely many derivatives
under consideration, and `β` to index their finite Leibniz terms. `Param` may be
the subtype of a fixed compact parameter box. Frequency `ρ i` and the actual
full factors `T a j i` do not depend on `x : Param`. The supplied identity
`hexact` must identify the actual outputs/derivatives with the finite expansion;
no differentiation of a frequency-dependent choice of operator is asserted.
`P` represents physical/demodulation multipliers and their fixed derivatives.

The source jet cost `e` and every other loss are fixed before integration orders.
The low/high split and all operators are the same for every order. Low/high
estimates are required only above `R`; a fixed polynomial estimate below `R`
suffices. The single resulting constant precedes output index, frequency, datum,
and parameter. Actual literal kernels, derivative identities, support/cutoff
compatibility and all stated analytic estimates remain obligations of the caller.
-/
theorem completeComplement_observations
    {α β Param : Type*} [Fintype α] [Fintype β]
    (G : GradedScale E) (H : GradedScale F) (J : GradedScale V)
    (T : α → β → ι → E →ₗ[ℝ] F) (P : α → β → ι → Param → F →ₗ[ℝ] V)
    (f low high : α → β → ι → Param → E) (out : α → ι → Param → V)
    (ρ L K A : ι → ℝ) (s n : ℕ) (t r b : α → β → ℕ)
    (ν c R : ℝ) (dLow dHigh D e DP dP : α → β → ℝ) (B dBound : α → ℝ)
    (hν : ν ∈ Set.Ioo (0 : ℝ) 1) (hc : 0 < c)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 1 ≤ L i)
    (hLK : ∀ i, L i ≤ K i) (hKρ : ∀ i, K i ≤ (ρ i) ^ (1 - ν))
    (hA : ∀ i, 0 ≤ A i) (hD : ∀ a j, 0 ≤ D a j)
    (hDP : ∀ a j, 0 ≤ DP a j) (hB : ∀ a, 0 ≤ B a)
    (hsplit : ∀ a j i x, f a j i x = low a j i x + high a j i x)
    (hexact : ∀ a i x, out a i x = ∑ j, P a j i x (T a j i (f a j i x)))
    (hT : ∀ a j i, R ≤ ρ i → ∀ v, v ∈ G.level (t a j) →
      T a j i v ∈ H.level (r a j) ∧
      H.gradeNorm (r a j) (T a j i v) ≤
        D a j * (ρ i) ^ (dHigh a j) * G.gradeNorm (t a j) v)
    (hP : ∀ a j i x, R ≤ ρ i → ∀ v, v ∈ H.level (r a j) →
      P a j i x v ∈ J.level s ∧ J.gradeNorm s (P a j i x v) ≤
        DP a j * (ρ i) ^ (dP a j) * H.gradeNorm (r a j) v)
    (hlow : ∀ a j (q : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, R ≤ ρ i →
      T a j i (low a j i x) ∈ H.level (r a j) ∧
      H.gradeNorm (r a j) (T a j i (low a j i x)) ≤
        C * (A i * (ρ i) ^ (e a j)) * (ρ i) ^ (dLow a j) *
          (c * (ρ i) ^ (1 - ν / 2)) ^ ((n : ℝ) / 2) * (L i) ^ (b a j) * (L i / ρ i) ^ q)
    (hhigh : ∀ a j (p : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, R ≤ ρ i →
      high a j i x ∈ G.level (t a j) ∧ G.gradeNorm (t a j) (high a j i x) ≤
        C * (A i * (ρ i) ^ (e a j)) * (K i) ^ p *
          (c * (ρ i) ^ (1 - ν / 2)) ^ ((t a j : ℝ) - p))
    (hsmall : ∀ a i x, ρ i < R → out a i x ∈ J.level s ∧
      J.gradeNorm s (out a i x) ≤ B a * A i * (ρ i) ^ (dBound a)) :
    ∀ Q : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a i x,
      out a i x ∈ J.level s ∧ J.gradeNorm s (out a i x) ≤ C * A i * (ρ i) ^ (-Q) := by
  classical
  let large := {z : ι × Param // R ≤ ρ z.1}
  have hρpos (i : ι) : 0 < ρ i := lt_of_lt_of_le zero_lt_one (hρ i)
  have hterm (a : α) (j : β) :
      RapidDecayAt J s (fun z : large ↦ ρ z.val.1) (fun z ↦ A z.val.1)
        (fun z ↦ P a j z.val.1 z.val.2 (T a j z.val.1 (f a j z.val.1 z.val.2))) := by
    have hbase := completeComplement_rapidDecay G H
      (fun z : large ↦ T a j z.val.1)
      (fun z ↦ f a j z.val.1 z.val.2) (fun z ↦ low a j z.val.1 z.val.2)
      (fun z ↦ high a j z.val.1 z.val.2)
      (fun z ↦ ρ z.val.1) (fun z ↦ L z.val.1) (fun z ↦ K z.val.1)
      (fun z ↦ A z.val.1 * (ρ z.val.1) ^ (e a j))
      (r a j) (t a j) n (b a j) ν c (dLow a j) (dHigh a j) (D a j)
      hν hc (fun z ↦ hρ z.val.1) (fun z ↦ hL z.val.1)
      (fun z ↦ hLK z.val.1) (fun z ↦ hKρ z.val.1)
      (fun z ↦ mul_nonneg (hA z.val.1) (Real.rpow_nonneg (hρpos z.val.1).le _))
      (hD a j) (fun z ↦ hsplit a j z.val.1 z.val.2)
      (fun z v hv ↦ (hT a j z.val.1 z.property v hv).1)
      (fun z v hv ↦ (hT a j z.val.1 z.property v hv).2)
      (fun q ↦ by
        obtain ⟨C, hC, hb⟩ := hlow a j q
        exact ⟨C, hC, fun z ↦ hb z.val.1 z.val.2 z.property⟩)
      (fun p ↦ by
        obtain ⟨C, hC, hb⟩ := hhigh a j p
        exact ⟨C, hC, fun z ↦ hb z.val.1 z.val.2 z.property⟩)
    have hremove := rapidDecayAt_remove_amplitude_power H _ _ _ (r a j) (e a j)
      (fun z : large ↦ hρpos z.val.1) hbase
    exact rapidDecayAt_polynomial_observation H J _ _ _ _ (r a j) s
      (DP a j) (dP a j) (fun z : large ↦ hρpos z.val.1) (hDP a j) hremove
      (fun z hv ↦ hP a j z.val.1 z.val.2 z.property _ hv)
  have hlarge (a : α) :
      RapidDecayAt J s (fun z : large ↦ ρ z.val.1) (fun z ↦ A z.val.1)
        (fun z ↦ out a z.val.1 z.val.2) := by
    exact rapidDecayAt_finite_expansion J Finset.univ _ _ _ _ s
      (fun z ↦ hexact a z.val.1 z.val.2) (fun j _ ↦ hterm a j)
  have hall (a : α) :
      RapidDecayAt J s (fun z : ι × Param ↦ ρ z.1) (fun z ↦ A z.1)
        (fun z ↦ out a z.1 z.2) :=
    rapidDecayAt_of_large_frequency J _ _ _ s R (B a) (dBound a)
      (fun z ↦ hρ z.1) (fun z ↦ hA z.1) (hB a) (hlarge a)
      (fun z hz ↦ hsmall a z.1 z.2 hz)
  intro Q
  obtain ⟨C, hC, hb⟩ := rapidDecayAt_uniform_finite J
    (fun a (z : ι × Param) ↦ out a z.1 z.2) _ _ s
    (fun z ↦ (hρpos z.1).le) (fun z ↦ hA z.1) hall Q
  exact ⟨C, hC, fun a i x ↦ hb a (i, x)⟩

end JanetCartan.ResponseTransfer.Complement
