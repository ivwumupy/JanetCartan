module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.AugmentedDifferential
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.AugmentedFirstOrder
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.Assembly

/-!
# Elliptic bootstrap for the image-carrier-exterior normal

For `app:ch_background:prop:bg-inverse`, construct the first-order inverse by
difference quotients, the forward H¹ action from the actual commutator, and
the higher weak derivatives by self-adjointness and H⁻¹ uniqueness. Both
`hreg` and `hstep` of `ContinuumInverse.Bootstrap` are conclusions for the SAME
literal augmented normal and its original L² inverse.

The inputs are primitive coefficient and amplitude budgets, the supported
real carrier-normal identities and a positive gap. Their actual producers
are `HistoryImage`, `CanonicalBudgets`, `CarrierNormalRealization.SupportedShell`
and the continuum coercivity construction. The parent retains their common
geometry and same-history instantiation, including variable positive initial
scalars. This conditional analytic assembly does not complete that construction.
No total commutator, image-remainder PDO representation, inverse regularity or
Sobolev inverse estimate is an input. Existing matrix-only endpoints are retained.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential
open JanetCartan.PeriodicLocalL2 JanetCartan.ContinuumRow

namespace JanetCartan.ContinuumCommutator

open PeriodicSobolevSpace HigherRegularity

variable {n : ℕ} {ι : Type*} [Fintype ι]
local notation "S" => periodicSobolevScale n (Euclidean n)

private theorem fixedCutoff_first_jet_le (χ : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic χ) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ 1 (periodicLift χ) x‖ ≤
      cNorm (fundamentalCell n) 1 (periodicLift χ) := by
  apply norm_iteratedFDeriv_periodicLift_le χ 1 _ x
  intro y hy
  exact norm_iteratedFDeriv_le_cNorm (isCompact_fundamentalCell n)
    (hχ.2.of_le (by simp)) hy (le_refl 1)

/-- The proved `hreg` and recursive `hstep` required by the inverse consumer,
and the all-order bound on the SAME inverse (`app:ch_background:eq:bg-commutator`,
`app:ch_background:prop:bg-inverse`, `app:ch_background:eq:bg-r-inverse`).

The constants precede the varying coefficient arrays, carrier amplitudes,
operators and high profile, with a single shift `2 * (n + 1) + b₀`. The fixed
low image order is one and the low carrier order is `2 * (n + 1) + 1`.
The carrier identity already includes both quadratures and factor four.
The module documentation identifies the actual producers of every remaining
primitive hypothesis; the geometric/history construction is not asserted here. -/
theorem exists_uniform_augmentedNormal_elliptic_estimates
    (hn : 0 < n) (R : ℝ) (hR : R < 1 / 2)
    (M : ι → ℝ) (hM0 : ∀ a, 0 ≤ M a) {L : ℝ} (hL : 0 ≤ L)
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic χmeas) (hsrc : IsSmoothPeriodic χsrc)
    (hext : IsSmoothPeriodic (1 - ψ : C(Torus n, ℝ)))
    (P Q : ℕ → ℝ) (hP : ∀ s, 0 ≤ P s) (hQ : ∀ s, 0 ≤ Q s) (b₀ : ℕ)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (_hc : ∀ a, IsSmoothPeriodic (c a)) (H : ℕ → ℝ),
      (∀ s, 0 ≤ H s) → Monotone H →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ L) →
      (∀ a j x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
        P j * (1 + H (j + 2))) →
      ∀ (b : ι → Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
        (hb : ∀ a, ContDiff ℝ ∞ (Function.uncurry (b a)))
        (hs : ∀ a ξ i j, SupportedInCenteredBox R (fun z ↦ b a ξ z i j))
        (hM : ∀ a i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b a ξ z i j)
          (2 * (n + 1) + 1) (M a)),
      (∀ s a i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b a ξ z i j)
        (2 * (n + 1) + (s + 1))
        (Q s * (1 + H (s + 1 + (2 * (n + 1) + b₀))))) →
      ∀ (T : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ a, (carrierChannel (T a)).comp (carrierChannel (T a)).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator hn R (b a) (hb a) (hs a) (M a)
            (fun i j ξ is his ↦ hM a i j ξ is (Nat.le_succ_of_le his))))) →
      let E := augmentedNormal (imageChannel c χmeas χsrc) T ψ
      (∀ v, γ * ‖v‖ ^ 2 ≤ ⟪E v, v⟫) →
        (∀ s v, v ∈ (S).level s → E v ∈ (S).level (s + 1) → v ∈ (S).level (s + 1)) ∧
        (∀ s v, v ∈ (S).level (s + 1) → E v ∈ (S).level (s + 1) →
          (S).gradeNorm (s + 1) v ≤ C (s + 1) *
            ((S).gradeNorm (s + 1) (E v) + (S).gradeNorm s v +
              (1 + H (s + 1 + (2 * (n + 1) + b₀))) * ‖v‖)) ∧
        (∀ s e, e ∈ (S).level s → E.inverse e ∈ (S).level s ∧
          (S).gradeNorm s (E.inverse e) ≤ ContinuumInverse.bootstrapConstant γ C s *
            ((S).gradeNorm s e + (1 + H (s + (2 * (n + 1) + b₀))) * ‖e‖)) := by
  classical
  obtain ⟨D, hD, hcomm⟩ := exists_augmentedNormal_tame_commutators
    hn R hR M hL χmeas χsrc ψ hm hsrc hext P Q hP hQ b₀
  let C := fun t ↦ ellipticStepConstant n (t - 1) γ (D (t - 1))
  obtain ⟨B, _, h₀, _, _, hfirst⟩ :=
    AugmentedFirstOrder.exists_uniform_augmentedNormal_firstOrderInverse
      hn R hR M hM0 L L ‖χmeas‖ ‖χsrc‖
      (cNorm (fundamentalCell n) 1 (periodicLift χmeas))
      (cNorm (fundamentalCell n) 1 (periodicLift χsrc)) ‖1 - ψ‖
      (cNorm (fundamentalCell n) 1 (periodicLift (1 - ψ : C(Torus n, ℝ))))
      hL hL (norm_nonneg _) (norm_nonneg _) (cNorm_nonneg ..) (cNorm_nonneg ..)
      (norm_nonneg _) (cNorm_nonneg ..)
  refine ⟨C, fun t ↦ ellipticStepConstant_nonneg n (t - 1) hγ (hD (t - 1)), ?_⟩
  intro c hc H hH hmono hlow hhigh b hb hs hM hbudget T hT
  dsimp only
  intro hgap
  let E := augmentedNormal (imageChannel c χmeas χsrc) T ψ
  have hvalue : ∀ a x, |c a x| ≤ L := by
    intro a x
    simpa only [norm_iteratedFDeriv_zero, periodicLift, Function.comp_apply,
      torusQuotient_centeredTorusRepresentative, Real.norm_eq_abs] using
      hlow a 0 (by omega) (centeredTorusRepresentative x)
  obtain ⟨hself, _, hfirst'⟩ := hfirst c hc hvalue (fun a ↦ hlow a 1 (le_refl 1))
    χmeas χsrc ψ hm hsrc hext χmeas.norm_coe_le_norm χsrc.norm_coe_le_norm
    (fixedCutoff_first_jet_le χmeas hm) (fixedCutoff_first_jet_le χsrc hsrc)
    (1 - ψ : C(Torus n, ℝ)).norm_coe_le_norm
    (fixedCutoff_first_jet_le (1 - ψ) hext) b hb hs hM T hT
  obtain ⟨_, _, Q₁, hQ₁, _, _⟩ := hfirst' γ hγ hgap
  choose K hidentity hbound using hcomm c hc H hH hmono hlow hhigh b hb hs hM hbudget T hT
  obtain ⟨E₁, hE₁⟩ := exists_firstOrderRestriction_of_commutators E (K 0) (hidentity 0)
  have hreg : ∀ s v, v ∈ (S).level s → E v ∈ (S).level (s + 1) → v ∈ (S).level (s + 1) :=
    fun s ↦ mem_succ_of_commutators E E₁ Q₁ hself hE₁ hQ₁ hγ hgap s (K s) (hidentity s)
  have hstep : ∀ s v, v ∈ (S).level (s + 1) → E v ∈ (S).level (s + 1) →
      (S).gradeNorm (s + 1) v ≤ C (s + 1) *
        ((S).gradeNorm (s + 1) (E v) + (S).gradeNorm s v +
          (1 + H (s + 1 + (2 * (n + 1) + b₀))) * ‖v‖) := by
    intro s v hv hev
    simpa only [C, Nat.add_sub_cancel] using
      gradeNorm_succ_le_of_commutators E E₁ Q₁ hself hE₁ hQ₁ hγ hgap s (K s) (hidentity s)
        (hD s) (add_nonneg zero_le_one (hH _)) (hbound s) v
        (antitone_periodicSobolevLevel (Nat.le_succ s) hv) hev
  refine ⟨hreg, hstep, ?_⟩
  intro s e he
  exact ⟨ContinuumInverse.inverse_mem S E hγ hgap hreg s he,
    ContinuumInverse.inverse_gradeNorm_le S E hγ hgap
      (fun t ↦ ellipticStepConstant_nonneg n (t - 1) hγ (hD (t - 1)))
      hH hmono hreg hstep s he⟩

end JanetCartan.ContinuumCommutator
