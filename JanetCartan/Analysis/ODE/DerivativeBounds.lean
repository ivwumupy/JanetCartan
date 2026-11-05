module

public import JanetCartan.Analysis.ContDiff.Norm.Defs
public import JanetCartan.Analysis.ODE.DerivativeBounds.Gronwall
public import JanetCartan.Analysis.ODE.DerivativeBounds.MatrixTransport

/-!
# Conditional derivative budgets for existing flows

The Gronwall step of `app:ch_regular_base:lem:buffered-interpolation` is proved
for actual iterated Fréchet derivatives. `HasJetEvolutionOn` states the supplied
variational equations, including continuity at the final time. The result bounds
the project's `cNorm`, uniformly in time and in the working coordinate domain.

For a flow, the positive-order coefficient is `DV(Ψ)` and the forcing consists
of the remaining derivative partitions. Order zero can use coefficient zero and
forcing `V(Ψ)` (under the canonical zero-linear-map identification). All external
parameters may be included in the domain `E`. The same theorem applies to an
existing inverse flow with its own variational equations.

These are conditional estimates: flow existence, the variational identities and
the one-high bounds for the partition forcing must be supplied. In particular,
we do not invoke the unfinished interpolation theorem in `ContDiff.Norm`.
-/

@[expose] public noncomputable section

open Set

namespace JanetCartan

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `app:ch_regular_base:lem:buffered-interpolation`: the temporal variational
equations for the actual spatial jets through order `n`. This record contains
equations and continuity only; it does not contain derivative bounds or assert
the existence of a flow. -/
structure HasJetEvolutionOn (Ψ : ℝ → E → F) (s : Set E) (n : ℕ) (a b : ℝ)
    (A : ℕ → ℝ → E → F →L[ℝ] F)
    (R : (j : ℕ) → ℝ → E → E [×j]→L[ℝ] F) : Prop where
  continuous : ∀ j ≤ n, ∀ x ∈ s,
    ContinuousOn (fun t ↦ iteratedFDeriv ℝ j (Ψ t) x) (Icc a b)
  hasDeriv : ∀ j ≤ n, ∀ x ∈ s, ∀ t ∈ Ico a b,
    HasDerivWithinAt (fun τ ↦ iteratedFDeriv ℝ j (Ψ τ) x)
      ((A j t x).compContinuousMultilinearMap (iteratedFDeriv ℝ j (Ψ t) x) + R j t x)
      (Ici t) t

/-- `app:ch_regular_base:lem:buffered-interpolation`: the top variational term
`A D^j Ψ` is controlled using only the low coefficient bound `K`. Given a
one-high forcing bound, Gronwall gives a one-high bound for `D^j Ψ`. -/
theorem HasJetEvolutionOn.norm_iteratedFDeriv_le_oneHigh
    {Ψ : ℝ → E → F} {s : Set E} {n j : ℕ} {a b δ K ε M : ℝ}
    {A : ℕ → ℝ → E → F →L[ℝ] F}
    {R : (j : ℕ) → ℝ → E → E [×j]→L[ℝ] F}
    (heq : HasJetEvolutionOn Ψ s n a b A R) (hj : j ≤ n)
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (ha : ∀ x ∈ s, ‖iteratedFDeriv ℝ j (Ψ a) x‖ ≤ δ * (1 + M))
    (hA : ∀ t ∈ Ico a b, ∀ x ∈ s, ‖A j t x‖ ≤ K)
    (hR : ∀ t ∈ Ico a b, ∀ x ∈ s, ‖R j t x‖ ≤ ε * (1 + M))
    {t : ℝ} (ht : t ∈ Icc a b) {x : E} (hx : x ∈ s) :
    ‖iteratedFDeriv ℝ j (Ψ t) x‖ ≤ gronwallBound δ K ε (b - a) * (1 + M) := by
  apply norm_le_oneHigh_of_deriv_bound hδ hK hε hM
    (heq.continuous j hj x hx) (heq.hasDeriv j hj x hx) (ha x hx) _ ht
  intro τ hτ
  calc
    ‖(A j τ x).compContinuousMultilinearMap (iteratedFDeriv ℝ j (Ψ τ) x) + R j τ x‖
        ≤ ‖(A j τ x).compContinuousMultilinearMap (iteratedFDeriv ℝ j (Ψ τ) x)‖ +
          ‖R j τ x‖ := norm_add_le _ _
    _ ≤ ‖A j τ x‖ * ‖iteratedFDeriv ℝ j (Ψ τ) x‖ + ε * (1 + M) :=
      add_le_add ((A j τ x).norm_compContinuousMultilinearMap_le _) (hR τ hτ x hx)
    _ ≤ K * ‖iteratedFDeriv ℝ j (Ψ τ) x‖ + ε * (1 + M) := by
      gcongr
      exact hA τ hτ x hx

/-- `app:ch_regular_base:lem:buffered-interpolation`: summing the fixed-time
derivative bounds gives the `C^n` budget with a single high coefficient norm `M`.
The explicit constant depends on the initial and forcing profiles, the low
coefficient bound and interval length. Empty working domains are also allowed. -/
theorem HasJetEvolutionOn.cNorm_le_oneHigh
    {Ψ : ℝ → E → F} {s : Set E} {n : ℕ} {a b K M : ℝ} {δ ε : ℕ → ℝ}
    {A : ℕ → ℝ → E → F →L[ℝ] F}
    {R : (j : ℕ) → ℝ → E → E [×j]→L[ℝ] F}
    (heq : HasJetEvolutionOn Ψ s n a b A R)
    (hδ : ∀ j ≤ n, 0 ≤ δ j) (hK : 0 ≤ K)
    (hε : ∀ j ≤ n, 0 ≤ ε j) (hM : 0 ≤ M)
    (ha : ∀ j ≤ n, ∀ x ∈ s, ‖iteratedFDeriv ℝ j (Ψ a) x‖ ≤ δ j * (1 + M))
    (hA : ∀ j ≤ n, ∀ t ∈ Ico a b, ∀ x ∈ s, ‖A j t x‖ ≤ K)
    (hR : ∀ j ≤ n, ∀ t ∈ Ico a b, ∀ x ∈ s, ‖R j t x‖ ≤ ε j * (1 + M))
    {t : ℝ} (ht : t ∈ Icc a b) :
    cNorm s n (Ψ t) ≤
      (∑ j ∈ Finset.range (n + 1), gronwallBound (δ j) K (ε j) (b - a)) * (1 + M) := by
  rw [cNorm, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst s
    simp only [image_empty, Real.sSup_empty]
    exact mul_nonneg
      (gronwallBound_nonneg (hδ j hjn) hK (hε j hjn) (sub_nonneg.mpr (ht.1.trans ht.2)))
      (by positivity)
  · apply csSup_le (hs.image _)
    rintro _ ⟨x, hx, rfl⟩
    exact heq.norm_iteratedFDeriv_le_oneHigh hjn (hδ j hjn) hK (hε j hjn) hM
      (ha j hjn) (hA j hjn) (hR j hjn) ht hx

/-- `app:ch_regular_base:lem:buffered-interpolation`: the same budget controls
the time derivative of each spatial jet via its variational equation. This
bounds the displayed right derivative even at the initial endpoint. -/
theorem HasJetEvolutionOn.norm_timeDeriv_le_oneHigh
    {Ψ : ℝ → E → F} {s : Set E} {n j : ℕ} {a b δ K ε M : ℝ}
    {A : ℕ → ℝ → E → F →L[ℝ] F}
    {R : (j : ℕ) → ℝ → E → E [×j]→L[ℝ] F}
    (heq : HasJetEvolutionOn Ψ s n a b A R) (hj : j ≤ n)
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (ha : ∀ x ∈ s, ‖iteratedFDeriv ℝ j (Ψ a) x‖ ≤ δ * (1 + M))
    (hA : ∀ t ∈ Ico a b, ∀ x ∈ s, ‖A j t x‖ ≤ K)
    (hR : ∀ t ∈ Ico a b, ∀ x ∈ s, ‖R j t x‖ ≤ ε * (1 + M))
    {t : ℝ} (ht : t ∈ Ico a b) {x : E} (hx : x ∈ s) :
    ‖(A j t x).compContinuousMultilinearMap (iteratedFDeriv ℝ j (Ψ t) x) + R j t x‖ ≤
      (K * gronwallBound δ K ε (b - a) + ε) * (1 + M) := by
  calc
    _ ≤ ‖A j t x‖ * ‖iteratedFDeriv ℝ j (Ψ t) x‖ + ε * (1 + M) :=
      (norm_add_le _ _).trans
        (add_le_add ((A j t x).norm_compContinuousMultilinearMap_le _) (hR t ht x hx))
    _ ≤ K * (gronwallBound δ K ε (b - a) * (1 + M)) + ε * (1 + M) := by
      apply add_le_add_left
      exact mul_le_mul (hA t ht x hx)
        (heq.norm_iteratedFDeriv_le_oneHigh hj hδ hK hε hM ha hA hR
          ⟨ht.1, ht.2.le⟩ hx) (norm_nonneg _) hK
    _ = _ := by ring

end JanetCartan
