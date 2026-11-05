module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Chains.Algebra
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Chains.Decay

/-!
# Envelope transfer through complete finite chains

Conditional deductions for `app:ch_response:eq:fixed-factor-transfer` and the
last chain paragraphs of `app:ch_response:thm:response-literal-transfer`.
The inputs are the exact full = near + complement identity, the direct near
estimate, complementary accuracy on each propagated near-family, and polynomial
Sobolev costs of the actual downstream factors. Every factor and cutoff remains
fixed at every precision; no successive projection of an envelope occurs.

`factorChain_matching_carriers` identifies these chains with demodulated actual
chains. A separate space and graded scale at each stage retain the actual input
and output measures. The actual graph, cutoff, retarded, and complementary
estimates must still be supplied by their producers. This does not prove the
unconditional response theorem or identify torus data with Lebesgue data.
-/

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer

open Finset ArbitraryAccuracy

variable {ι : Type*} {E : ℕ → Type*}
  [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℝ (E j)]

/-- The direct inequality, applied successively with matching carriers, preserves
the near-only profile (`app:ch_response:eq:direct-envelope-profile`).
It acts on the complete propagated envelope, without new source projections. -/
theorem factorChain_near_hasEnvelopeProfile
    (G : ∀ j, GradedScale (E j)) (N : ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (f : ι → E 0) (L K A : ι → ℝ) (d : ℕ)
    (hA : ∀ i, 0 ≤ A i) (hL : ∀ i, 0 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hf : HasEnvelopeProfile (G 0) f A K)
    (hmem : ∀ j < d, ∀ i s, N j i (factorChain N f j i) ∈ (G (j + 1)).level s)
    (hbound : ∀ j < d, ∀ s, ∃ D : ℝ, 0 ≤ D ∧ ∀ i,
      (G (j + 1)).gradeNorm s (N j i (factorChain N f j i)) ≤
        D * ∑ r ∈ range (s + 1), L i ^ (s - r) *
          (G j).gradeNorm r (factorChain N f j i)) :
    ∀ n ≤ d, HasEnvelopeProfile (G n) (factorChain N f n) A K := by
  intro n hn
  induction n with
  | zero => exact hf
  | succ n ih =>
    have hnd : n < d := by omega
    exact (ih (by omega)).of_direct_estimate hA hL hLK (hmem n hnd) (hbound n hnd)

/-- Every individual telescoping term, including its Sobolev membership, has
arbitrary accuracy. Each induction step selects precision before the family index
and pays the cost of the next full factor
(`app:ch_response:thm:response-literal-transfer`). -/
theorem chainLeakage_rapidDecayAt
    (G : ∀ j, GradedScale (E j)) (T N C : ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (f : ι → E 0) (ρ A : ι → ℝ) (d : ℕ)
    (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i)
    (hcost : ∀ j < d, HasPolynomialSobolevCost (G j) (G (j + 1)) ρ (T j))
    (hcomp : ∀ j < d, ∀ s, RapidDecayAt (G (j + 1)) s ρ A
      (fun i ↦ C j i (factorChain N f j i))) :
    ∀ n ≤ d, ∀ j < n, ∀ s, RapidDecayAt (G n) s ρ A (chainLeakage T N C f n j) := by
  intro n hn
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj s
    have hnd : n < d := by omega
    by_cases h : j = n
    · subst j
      simpa only [chainLeakage, ↓reduceIte] using hcomp n hnd s
    · have hjn : j < n := by omega
      simpa only [chainLeakage, h, ↓reduceIte] using
        rapidDecayAt_polynomial_factor hρ hA (hcost n hnd) (ih (by omega) j hjn) s

/-- The full chain differs from its near-only chain by an arbitrarily small
Sobolev error. This is a consequence of exact telescoping, not an assumed chain
estimate (`app:ch_response:thm:response-literal-transfer`). -/
theorem factorChain_sub_near_rapidDecayAt
    (G : ∀ j, GradedScale (E j)) (T N C : ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (f : ι → E 0) (ρ A : ι → ℝ) (d : ℕ)
    (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i)
    (hsplit : ∀ j < d, ∀ i, T j i = N j i + C j i)
    (hcost : ∀ j < d, HasPolynomialSobolevCost (G j) (G (j + 1)) ρ (T j))
    (hcomp : ∀ j < d, ∀ s, RapidDecayAt (G (j + 1)) s ρ A
      (fun i ↦ C j i (factorChain N f j i))) :
    ∀ s, RapidDecayAt (G d) s ρ A (fun i ↦ factorChain T f d i - factorChain N f d i) := by
  intro s
  have heq : (fun i ↦ factorChain T f d i - factorChain N f d i) =
      fun i ↦ ∑ j ∈ range d, chainLeakage T N C f d j i := by
    funext i
    rw [factorChain_eq_near_add_leakage T N C f d hsplit d le_rfl i,
      add_sub_cancel_left]
  rw [heq]
  exact rapidDecayAt_chain_sum (range d) s (fun j hj ↦
    chainLeakage_rapidDecayAt G T N C f ρ A d hρ hA hcost hcomp d le_rfl j
      (mem_range.mp hj) s)

/-- If one actual factor is entirely complementary, the full chain has arbitrary
accuracy. The near chain vanishes by the exact split, and the already proved
leakage theorem pays all downstream costs. No additional estimate on the
complete prefix is assumed (`app:ch_response:thm:response-literal-transfer`). -/
theorem factorChain_rapidDecayAt_of_complementary_factor
    (G : ∀ j, GradedScale (E j)) (T N C : ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (f : ι → E 0) (ρ A : ι → ℝ) (d k : ℕ)
    (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i)
    (hsplit : ∀ j < d, ∀ i, T j i = N j i + C j i)
    (hcost : ∀ j < d, HasPolynomialSobolevCost (G j) (G (j + 1)) ρ (T j))
    (hcomp : ∀ j < d, ∀ s, RapidDecayAt (G (j + 1)) s ρ A
      (fun i ↦ C j i (factorChain N f j i)))
    (hk : k < d) (hinactive : ∀ i, T k i = C k i) :
    ∀ s, RapidDecayAt (G d) s ρ A (factorChain T f d) := by
  have hN : ∀ i, N k i = 0 := fun i ↦
    add_eq_right.mp ((hsplit k hk i).symm.trans (hinactive i))
  have hzero : ∀ n, k < n → ∀ i, factorChain N f n i = 0 := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hn i
      by_cases h : k = n
      · subst n
        simp [factorChain, hN i]
      · change N n i (factorChain N f n i) = 0
        rw [ih (by omega) i, map_zero]
  simpa only [hzero d hk, sub_zero] using
    factorChain_sub_near_rapidDecayAt G T N C f ρ A d hρ hA hsplit hcost hcomp

/-- The complete, fixed chain preserves the envelope. The only analytic inputs
are the individual direct near bounds, complementary estimates on near-families,
and polynomial costs; the leakage estimate is proved internally
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem factorChain_hasEnvelopeProfile
    (G : ∀ j, GradedScale (E j)) (T N C : ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (f : ι → E 0) (ρ L K A : ι → ℝ) (d : ℕ)
    (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 1 ≤ K i)
    (hL : ∀ i, 0 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hf : HasEnvelopeProfile (G 0) f A K)
    (hsplit : ∀ j < d, ∀ i, T j i = N j i + C j i)
    (hmem : ∀ j < d, ∀ i s, N j i (factorChain N f j i) ∈ (G (j + 1)).level s)
    (hbound : ∀ j < d, ∀ s, ∃ D : ℝ, 0 ≤ D ∧ ∀ i,
      (G (j + 1)).gradeNorm s (N j i (factorChain N f j i)) ≤
        D * ∑ r ∈ range (s + 1), L i ^ (s - r) *
          (G j).gradeNorm r (factorChain N f j i))
    (hcost : ∀ j < d, HasPolynomialSobolevCost (G j) (G (j + 1)) ρ (T j))
    (hcomp : ∀ j < d, ∀ s, RapidDecayAt (G (j + 1)) s ρ A
      (fun i ↦ C j i (factorChain N f j i))) :
    HasEnvelopeProfile (G d) (factorChain T f d) A K := by
  have hn := factorChain_near_hasEnvelopeProfile G N f L K A d hA hL hLK hf hmem hbound d le_rfl
  have hr := hasEnvelopeProfile_of_rapidDecayAt hA hK
    (factorChain_sub_near_rapidDecayAt G T N C f ρ A d hρ hA hsplit hcost hcomp)
  let v : Bool → ι → E d := fun b i ↦
    if b then factorChain N f d i else factorChain T f d i - factorChain N f d i
  have hv : ∀ b ∈ (univ : Finset Bool), HasEnvelopeProfile (G d) (v b) A K := by
    intro b _
    cases b
    · exact hr
    · exact hn
  simpa [v, add_comm] using HasEnvelopeProfile.sum univ hv

/-- Propagate a small input through any fixed full downstream chain. This is used
after an inactive source factor, in both physical and demodulated scales
(`app:ch_response:thm:response-literal-transfer`). -/
theorem factorChain_rapidDecayAt
    (G : ∀ j, GradedScale (E j)) (T : ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (f : ι → E 0) (ρ A : ι → ℝ) (d : ℕ)
    (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i)
    (hf : ∀ s, RapidDecayAt (G 0) s ρ A f)
    (hcost : ∀ j < d, HasPolynomialSobolevCost (G j) (G (j + 1)) ρ (T j)) :
    ∀ n ≤ d, ∀ s, RapidDecayAt (G n) s ρ A (factorChain T f n) := by
  intro n hn
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact rapidDecayAt_polynomial_factor hρ hA (hcost n (by omega)) (ih (by omega))

/-- An inactive/complementary factor applied to a complete prefix is small:
apply its complementary estimate to the near prefix and its polynomial bound to
the leakage. This is the inactive-branch step of
`app:ch_response:thm:response-literal-transfer`, with no assumption that the
complete prefix is frequency projected. -/
theorem complementary_factorChain_rapidDecayAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ∀ j, GradedScale (E j)) (H : GradedScale F)
    (T N C : ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (f : ι → E 0) (ρ A : ι → ℝ) (d : ℕ) (B : ι → E d →ₗ[ℝ] F)
    (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i)
    (hsplit : ∀ j < d, ∀ i, T j i = N j i + C j i)
    (hcost : ∀ j < d, HasPolynomialSobolevCost (G j) (G (j + 1)) ρ (T j))
    (hcomp : ∀ j < d, ∀ s, RapidDecayAt (G (j + 1)) s ρ A
      (fun i ↦ C j i (factorChain N f j i)))
    (hBcost : HasPolynomialSobolevCost (G d) H ρ B)
    (hBnear : ∀ s, RapidDecayAt H s ρ A (fun i ↦ B i (factorChain N f d i))) :
    ∀ s, RapidDecayAt H s ρ A (fun i ↦ B i (factorChain T f d i)) := by
  have hr := rapidDecayAt_polynomial_factor hρ hA hBcost
    (factorChain_sub_near_rapidDecayAt G T N C f ρ A d hρ hA hsplit hcost hcomp)
  intro s
  let v : Bool → ι → F := fun b i ↦ if b then B i (factorChain N f d i)
    else B i (factorChain T f d i - factorChain N f d i)
  have hv : ∀ b ∈ (univ : Finset Bool), RapidDecayAt H s ρ A (v b) := by
    intro b _
    cases b
    · exact hr s
    · exact hBnear s
  simpa [v, map_sub, add_comm] using rapidDecayAt_chain_sum univ s hv

/-- The inactive output after all remaining full factors has arbitrary accuracy.
Here `B` is the actual complementary/inactive factor between the full prefix `T`
and the full suffix `P`. Its estimate is needed only on the propagated near
family; its action on all prefix leakage is handled by its polynomial cost.
Physical output and demodulated output are separate instances with their actual
scales and costs (`app:ch_response:thm:response-literal-transfer`). -/
theorem inactive_factorChain_rapidDecayAt
    {F : ℕ → Type*} [∀ j, NormedAddCommGroup (F j)] [∀ j, NormedSpace ℝ (F j)]
    (G : ∀ j, GradedScale (E j)) (H : ∀ j, GradedScale (F j))
    (T N C : ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (f : ι → E 0) (ρ A : ι → ℝ) (d e : ℕ) (B : ι → E d →ₗ[ℝ] F 0)
    (P : ∀ j, ι → F j →ₗ[ℝ] F (j + 1))
    (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i)
    (hsplit : ∀ j < d, ∀ i, T j i = N j i + C j i)
    (hcost : ∀ j < d, HasPolynomialSobolevCost (G j) (G (j + 1)) ρ (T j))
    (hcomp : ∀ j < d, ∀ s, RapidDecayAt (G (j + 1)) s ρ A
      (fun i ↦ C j i (factorChain N f j i)))
    (hBcost : HasPolynomialSobolevCost (G d) (H 0) ρ B)
    (hBnear : ∀ s, RapidDecayAt (H 0) s ρ A (fun i ↦ B i (factorChain N f d i)))
    (hPcost : ∀ j < e, HasPolynomialSobolevCost (H j) (H (j + 1)) ρ (P j)) :
    ∀ s, RapidDecayAt (H e) s ρ A
      (factorChain P (fun i ↦ B i (factorChain T f d i)) e) := by
  exact factorChain_rapidDecayAt H P _ ρ A e hρ hA
    (complementary_factorChain_rapidDecayAt G (H 0) T N C f ρ A d B hρ hA
      hsplit hcost hcomp hBcost hBnear) hPcost e le_rfl

/-- The envelope estimate for the actual modulated full chain. `T` contains the
original factors and cutoffs, `M` the matching carrier multiplication maps, and
`B` their exactly demodulated factors. This assembles carrier cancellation with
the proved leakage estimate, discharging the intermediate chain estimate
(`app:ch_response:eq:fixed-factor-transfer`). Finite sums of these outputs use
`HasEnvelopeProfile.sum` with the same `A` and `K`. -/
theorem matching_factorChain_hasEnvelopeProfile
    (G : ∀ j, GradedScale (E j))
    (T B N C : ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (M : ∀ j, ι → E j ≃ₗ[ℝ] E j)
    (f : ι → E 0) (ρ L K A : ι → ℝ) (d : ℕ)
    (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 1 ≤ K i)
    (hL : ∀ i, 0 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hf : HasEnvelopeProfile (G 0) f A K)
    (hmatch : ∀ j < d, ∀ i v, B j i v =
      (M (j + 1) i).symm (T j i (M j i v)))
    (hsplit : ∀ j < d, ∀ i, B j i = N j i + C j i)
    (hmem : ∀ j < d, ∀ i s, N j i (factorChain N f j i) ∈ (G (j + 1)).level s)
    (hbound : ∀ j < d, ∀ s, ∃ D : ℝ, 0 ≤ D ∧ ∀ i,
      (G (j + 1)).gradeNorm s (N j i (factorChain N f j i)) ≤
        D * ∑ r ∈ range (s + 1), L i ^ (s - r) *
          (G j).gradeNorm r (factorChain N f j i))
    (hcost : ∀ j < d, HasPolynomialSobolevCost (G j) (G (j + 1)) ρ (B j))
    (hcomp : ∀ j < d, ∀ s, RapidDecayAt (G (j + 1)) s ρ A
      (fun i ↦ C j i (factorChain N f j i))) :
    HasEnvelopeProfile (G d)
      (fun i ↦ (M d i).symm (factorChain T (fun k ↦ M 0 k (f k)) d i)) A K := by
  have heq := funext (factorChain_matching_carriers T B M f d hmatch d le_rfl)
  rw [← heq]
  exact factorChain_hasEnvelopeProfile G B N C f ρ L K A d hρ hA hK hL hLK hf
    hsplit hmem hbound hcost hcomp

/-- A fixed finite sum of actual chains with matching carriers has the same
profile (`app:ch_response:thm:response-literal-transfer`). This applies the
existing finite-sum theorem after discharging each chain's estimate from its
individual analytic inputs. All summands retain their given factors and cutoffs. -/
theorem matching_factorChain_sum_hasEnvelopeProfile
    {κ : Type*} (I : Finset κ) (G : ∀ j, GradedScale (E j))
    (T B N C : κ → ∀ j, ι → E j →ₗ[ℝ] E (j + 1))
    (M : κ → ∀ j, ι → E j ≃ₗ[ℝ] E j)
    (f : κ → ι → E 0) (ρ L K A : ι → ℝ) (d : ℕ)
    (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 1 ≤ K i)
    (hL : ∀ i, 0 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hf : ∀ a ∈ I, HasEnvelopeProfile (G 0) (f a) A K)
    (hmatch : ∀ a ∈ I, ∀ j < d, ∀ i v, B a j i v =
      (M a (j + 1) i).symm (T a j i (M a j i v)))
    (hsplit : ∀ a ∈ I, ∀ j < d, ∀ i, B a j i = N a j i + C a j i)
    (hmem : ∀ a ∈ I, ∀ j < d, ∀ i s,
      N a j i (factorChain (N a) (f a) j i) ∈ (G (j + 1)).level s)
    (hbound : ∀ a ∈ I, ∀ j < d, ∀ s, ∃ D : ℝ, 0 ≤ D ∧ ∀ i,
      (G (j + 1)).gradeNorm s (N a j i (factorChain (N a) (f a) j i)) ≤
        D * ∑ r ∈ range (s + 1), L i ^ (s - r) *
          (G j).gradeNorm r (factorChain (N a) (f a) j i))
    (hcost : ∀ a ∈ I, ∀ j < d,
      HasPolynomialSobolevCost (G j) (G (j + 1)) ρ (B a j))
    (hcomp : ∀ a ∈ I, ∀ j < d, ∀ s, RapidDecayAt (G (j + 1)) s ρ A
      (fun i ↦ C a j i (factorChain (N a) (f a) j i))) :
    HasEnvelopeProfile (G d)
      (fun i ↦ ∑ a ∈ I, (M a d i).symm
        (factorChain (T a) (fun k ↦ M a 0 k (f a k)) d i)) A K := by
  exact HasEnvelopeProfile.sum I (fun a ha ↦
    matching_factorChain_hasEnvelopeProfile G (T a) (B a) (N a) (C a) (M a)
      (f a) ρ L K A d hρ hA hK hL hLK (hf a ha) (hmatch a ha)
      (hsplit a ha) (hmem a ha) (hbound a ha) (hcost a ha) (hcomp a ha))

end JanetCartan.ResponseTransfer
