module

public import JanetCartan.Analysis.Fourier.Periodic.Bernstein.Derivatives
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.UniformKernel
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Sobolev
public import JanetCartan.Analysis.Fourier.Periodic.Bernstein.Reduction

/-!
# Periodic Bernstein estimates between derivative sup norms

For paper.tex, `main:lem:history`, exact Fourier support below `L ≥ 1`
gives `cNorm_s f ≤ C L^(s-r) cNorm_r f` for `r ≤ s`. The constant depends
only on the dimension and orders, and is uniform over real Banach codomains.

The proof applies the fixed cutoff's uniform first-derivative estimate to the
band-limited periodic lifts of every iterated derivative, then sums the resulting
successive derivative bounds. Both analytic inputs are proved; the earlier
conditional reduction theorems are retained as reusable assembly lemmas.
-/

@[expose] public noncomputable section

universe u

namespace JanetCartan

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `main:lem:history`: the sharp `L ^ (s - r)` bound from a pointwise
one-derivative estimate on the iterated derivatives of the periodic lift.
The one-derivative estimates are explicit analytic inputs. -/
theorem periodic_cNorm_le_of_fderiv_bound {f : Torus n → F}
    {B L : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) {r s : ℕ} (hrs : r ≤ s)
    (hstep : ∀ j, r ≤ j → j < s → ∀ x ∈ fundamentalCell n,
      ‖fderiv ℝ (iteratedFDeriv ℝ j (periodicLift f)) x‖ ≤
        B * L * sSup ((fun y ↦ ‖iteratedFDeriv ℝ j (periodicLift f) y‖) ''
          fundamentalCell n)) :
    cNorm (fundamentalCell n) s (periodicLift f) ≤
      (1 + B) ^ (s - r) * L ^ (s - r) *
        cNorm (fundamentalCell n) r (periodicLift f) := by
  apply Bernstein.cNorm_le_of_fderiv_bound _ hB hL hrs hstep
  refine ⟨0, ?_⟩
  intro i
  simp

/-- `main:lem:history`: conditional assembly of Bernstein from two independent
analytic inputs: a uniform first-derivative bound, and band-limited periodic
lifts of all iterated derivatives. The constant is independent of `L` and `f`.
Neither analytic input is asserted by this theorem. -/
theorem periodic_cNorm_le_of_first_derivative_estimate {B : ℝ} (hB : 0 ≤ B)
    {r s : ℕ} (hrs : r ≤ s)
    (hfirst : ∀ j : ℕ, r ≤ j → j < s → ∀ L : ℝ, 1 ≤ L →
      ∀ g : Torus n → (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F,
        IsSmoothPeriodic g → HasFourierSupport L g →
        ∀ x ∈ fundamentalCell n, ‖fderiv ℝ (periodicLift g) x‖ ≤
          B * L * sSup ((fun y ↦ ‖periodicLift g y‖) '' fundamentalCell n))
    (hderivatives : ∀ (L : ℝ) (f : Torus n → F),
      IsSmoothPeriodic f → HasFourierSupport L f → ∀ j : ℕ,
        ∃ g : Torus n → (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F,
          IsSmoothPeriodic g ∧ HasFourierSupport L g ∧
            periodicLift g = iteratedFDeriv ℝ j (periodicLift f))
    {L : ℝ} (hL : 1 ≤ L) {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (hsupport : HasFourierSupport L f) :
    cNorm (fundamentalCell n) s (periodicLift f) ≤
      (1 + B) ^ (s - r) * L ^ (s - r) *
        cNorm (fundamentalCell n) r (periodicLift f) := by
  apply periodic_cNorm_le_of_fderiv_bound hB hL hrs
  intro j hrj hjs x hx
  obtain ⟨g, hg, hgsupport, hglift⟩ := hderivatives L f hf hsupport j
  simpa only [hglift] using hfirst j hrj hjs L hL g hg hgsupport x hx

/-- `main:lem:history`: a continuous field with exact Fourier support below `L ≥ 1`
has its first derivative bounded by `B L` times any uniform bound on the field.
The constant depends only on the dimension, uniformly over real Banach codomains. -/
theorem exists_periodic_fderiv_bernstein_bound (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
        {L : ℝ}, 1 ≤ L → ∀ {f : Torus n → F}, Continuous f →
        HasFourierSupport L f → ∀ {M : ℝ}, 0 ≤ M → (∀ y, ‖f y‖ ≤ M) →
        ∀ x : EuclideanSpace ℝ (Fin n),
          ‖fderiv ℝ (periodicLift f) x‖ ≤ B * L * M := by
  obtain ⟨B, hB, hbound⟩ := exists_periodicCutoff_derivative_bound.{u} n 1
  refine ⟨B, hB, ?_⟩
  intro F _ _ _ L hL f hf hs M hM hm x
  have h := hbound hL hf hM hm x
  rwa [periodicCutoff_eq_self hf (lt_of_lt_of_le zero_lt_one hL) hs,
    norm_iteratedFDeriv_one, pow_one] at h

/-- `main:lem:history`: a single dimension-dependent constant controls all
successive derivative norms with the sharp bandwidth power. The Fourier support
and smoothness hypotheses suffice; there are no unproved analytic premises. -/
theorem exists_periodic_cNorm_bernstein_constant (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
        {r s : ℕ}, r ≤ s → ∀ {L : ℝ}, 1 ≤ L →
        ∀ {f : Torus n → F}, IsSmoothPeriodic f → HasFourierSupport L f →
        cNorm (fundamentalCell n) s (periodicLift f) ≤
          (1 + B) ^ (s - r) * L ^ (s - r) *
            cNorm (fundamentalCell n) r (periodicLift f) := by
  obtain ⟨B, hB, hfirst⟩ := exists_periodic_fderiv_bernstein_bound.{u} n
  refine ⟨B, hB, ?_⟩
  intro F _ _ _ r s hrs L hL f hf hs
  apply periodic_cNorm_le_of_first_derivative_estimate hB hrs
  · intro j _ _ L hL g hg hgs x _
    have h := hfirst hL hg.1 hgs (cNorm_nonneg _ _ _) hg.norm_le_cNorm_zero x
    simpa only [cNorm, zero_add, Finset.sum_range_one, norm_iteratedFDeriv_zero] using h
  · intro L f hf hs j
    exact hf.exists_iteratedFDeriv hs j
  · exact hL
  · exact hf
  · exact hs

/-- `main:lem:history`: the periodic Bernstein estimate between derivative sup
norms, with constant independent of the bandwidth, field, and real Banach codomain.
The bandwidth power is exactly `s - r`, with no dimension loss. -/
theorem exists_periodic_cNorm_bernstein_bound (n r s : ℕ) (hrs : r ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
        {L : ℝ}, 1 ≤ L → ∀ {f : Torus n → F},
        IsSmoothPeriodic f → HasFourierSupport L f →
        cNorm (fundamentalCell n) s (periodicLift f) ≤
          C * L ^ (s - r) * cNorm (fundamentalCell n) r (periodicLift f) := by
  obtain ⟨B, hB, hbound⟩ := exists_periodic_cNorm_bernstein_constant.{u} n
  refine ⟨(1 + B) ^ (s - r), by positivity, ?_⟩
  intro F _ _ _ L hL f hf hs
  exact hbound hrs hL hf hs

/-- `main:eq:history-current`: the Bernstein profile at arbitrary natural orders.
When the target order is below the baseline, monotonicity gives the bound with
constant one and bandwidth exponent zero. -/
theorem exists_periodic_cNorm_bernstein_bound_all_orders (n r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
        {L : ℝ}, 1 ≤ L → ∀ {f : Torus n → F},
        IsSmoothPeriodic f → HasFourierSupport L f →
        cNorm (fundamentalCell n) s (periodicLift f) ≤
          C * L ^ (s - r) * cNorm (fundamentalCell n) r (periodicLift f) := by
  by_cases hrs : r ≤ s
  · exact exists_periodic_cNorm_bernstein_bound.{u} n r s hrs
  · have hsr : s ≤ r := Nat.le_of_not_ge hrs
    refine ⟨1, zero_le_one, ?_⟩
    intro F _ _ _ L _ f _ _
    simpa only [Nat.sub_eq_zero_of_le hsr, pow_zero, one_mul] using
      (cNorm_mono_order (s := fundamentalCell n) (f := periodicLift f) hsr)

end JanetCartan
