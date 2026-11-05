module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.PhaseBounds

/-!
# Inverse estimates using the gap on the actual graph

The integration balls in `app:ch_seed:prop:seed-phase-charts` can be larger
than the injectivity domain. Apply the existing Hamilton pointwise inverse-jet
estimate at the inverse graph, where `BufferedPhaseInverse` supplies the gap.
The larger ball supplies only interpolation and forward phase estimates.
The concrete full/transverse instantiation consumes this local variant.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.FullPhaseCharts.ActualEstimates
open InverseEstimates

section Pointwise
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

private theorem exists_inverse_cNorm_bound_on_graph (a : X) {ρ : ℝ} (hρ : 0 < ρ)
    {W : Set X} (hW : IsOpen W) (hball : closedBall a ρ ⊆ W)
    {M J : ℝ} (hM : 0 ≤ M) (hJ : 0 ≤ J) (n : ℕ) :
    ∃ C > (0 : ℝ), ∀ (f g : X → X) (V K : Set X),
      IsOpen V → K ⊆ V → ContDiffOn ℝ ∞ f W → ContDiffOn ℝ ∞ g V →
      cNorm (closedBall a ρ) 1 f ≤ M → MapsTo g K (closedBall a ρ) →
      (∀ y ∈ K, ∀ v, ‖v‖ ≤ J * ‖fderiv ℝ f (g y) v‖) →
      EqOn (f ∘ g) id V →
      cNorm K n g ≤ C * (1 + cNorm (closedBall a ρ) n f) := by
  choose C hC hb using exists_inverse_jet_bound_of_lower_bound
    a hρ hW hball (ContinuousLinearMap.id ℝ X) hM hJ
  let D := ∑ j ∈ Finset.range (n + 1), C j
  have hD : 0 ≤ D := Finset.sum_nonneg fun j _ ↦ (hC j).le
  refine ⟨1 + D, by positivity, ?_⟩
  intro f g V K hV hKV hf hg hlow hrange hlower heq
  have hH : 0 ≤ 1 + cNorm (closedBall a ρ) n f := by
    linarith [cNorm_nonneg (closedBall a ρ) n f]
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), C j *
        (1 + cNorm (closedBall a ρ) n f) := by
      apply cNorm_le_sum_of_bounds (fun j _ ↦ mul_nonneg (hC j).le hH)
      intro j hj y hy
      apply (hb j f g y hf (hg.contDiffAt (hV.mem_nhds (hKV hy)))
        hlow (hrange hy) (hlower y hy)
        (Filter.eventuallyEq_of_mem (hV.mem_nhds (hKV hy)) (fun z hz ↦ heq hz))).trans
      exact mul_le_mul_of_nonneg_left
        (add_le_add (le_refl 1) (cNorm_mono_order hj)) (hC j).le
    _ = D * (1 + cNorm (closedBall a ρ) n f) := (Finset.sum_mul ..).symm
    _ ≤ (1 + D) * (1 + cNorm (closedBall a ρ) n f) := by nlinarith

end Pointwise

section Fiber
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ E]

private theorem exists_fiber_inverse_cNorm_bound_on_graph (a : P × E) {ρ : ℝ} (hρ : 0 < ρ)
    {W : Set (P × E)} (hW : IsOpen W) (hball : closedBall a ρ ⊆ W)
    (G : E ≃L[ℝ] E) {M : ℝ} (hM : 0 ≤ M) (n : ℕ) :
    ∃ C > (0 : ℝ), ∀ (f g : P × E → E) (V K : Set (P × E)),
      IsOpen V → IsCompact K → K ⊆ V →
      ContDiffOn ℝ ∞ f W → ContDiffOn ℝ ∞ g V →
      cNorm (closedBall a ρ) 1 f ≤ M →
      MapsTo (inverseGraph g) K (closedBall a ρ) →
      (∀ q ∈ K,
        ‖(G.symm : E →L[ℝ] E).comp (fderiv ℝ (fun u ↦ f (q.1, u)) (g q)) -
          ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) →
      (∀ q ∈ V, f (inverseGraph g q) = q.2) →
      cNorm K n g ≤ C * (1 + cNorm (closedBall a ρ) n f) := by
  let Q : (P × E) → P := Prod.fst
  let J := 1 + 2 * ‖(G.symm : E →L[ℝ] E)‖ * (1 + M)
  have hJ : 0 ≤ J := by positivity
  obtain ⟨D, hD, hb⟩ := exists_inverse_cNorm_bound_on_graph a hρ hW hball
    (add_nonneg (cNorm_nonneg (closedBall a ρ) 1 Q) hM) hJ n
  refine ⟨D * (1 + cNorm (closedBall a ρ) n Q), by
    have := cNorm_nonneg (closedBall a ρ) n Q; positivity, ?_⟩
  intro f g V K hV hK hKV hf hg hlow hrange hgap heq
  have hfl (j : ℕ) : ∀ x ∈ closedBall a ρ, ContDiffAt ℝ j f x :=
    fun x hx ↦ (hf.contDiffAt (hW.mem_nhds (hball hx))).of_le (by simp)
  have hpair (j : ℕ) := cNorm_prodMk_le_on (closedBall a ρ)
    (isCompact_closedBall a ρ) j (f := Q) (g := f)
    (fun _ _ ↦ contDiff_fst.contDiffAt) (hfl j)
  have hgraph : ContDiffOn ℝ ∞ (inverseGraph g) V := contDiffOn_fst.prodMk hg
  have hbound := hb (inverseGraph f) (inverseGraph g) V K hV hKV
    (contDiffOn_fst.prodMk hf) hgraph ((hpair 1).trans (add_le_add (le_refl _) hlow))
    hrange (by
      intro q hq v
      let x := inverseGraph g q
      have hx := hrange hq
      have hfd := (hfl 1 x hx).differentiableAt (by simp)
      have hd : fderiv ℝ (inverseGraph f) x =
          (ContinuousLinearMap.fst ℝ P E).prod (fderiv ℝ f x) :=
        (hasFDerivAt_fst.prodMk hfd.hasFDerivAt).fderiv
      rw [hd]
      apply norm_le_augmented_differential G _ hM
      · have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt
          (isCompact_closedBall a ρ) (hfl 1) hx (le_refl 1)
        simpa only [norm_iteratedFDeriv_one] using hh.trans hlow
      · have hi : fderiv ℝ (fun u ↦ f (x.1, u)) x.2 =
            (fderiv ℝ f x).comp (ContinuousLinearMap.inr ℝ P E) :=
          (hfd.hasFDerivAt.comp x.2
            (hasFDerivAt_prodMk_right (𝕜 := ℝ) x.1 x.2)).fderiv
        rw [← hi]
        exact hgap q hq) (by
      intro q hq
      exact Prod.ext rfl (heq q hq))
  have hgproj : cNorm K n g ≤ cNorm K n (inverseGraph g) := by
    have hh := cNorm_postLinear_le_on hK n (ContinuousLinearMap.snd ℝ P E)
      (fun x hx ↦ (hgraph.contDiffAt (hV.mem_nhds (hKV hx))).of_le (by simp))
    apply hh.trans
    exact mul_le_of_le_one_left (cNorm_nonneg K n (inverseGraph g))
      (by
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro v
        simpa using norm_snd_le v)
  apply hgproj.trans (hbound.trans _)
  have hq := cNorm_nonneg (closedBall a ρ) n Q
  have hf0 := cNorm_nonneg (closedBall a ρ) n f
  have hp := hpair n
  change cNorm (closedBall a ρ) n (inverseGraph f) ≤ _ at hp
  change D * (1 + cNorm (closedBall a ρ) n (inverseGraph f)) ≤ _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hD.le
  nlinarith [mul_nonneg hq hf0]

/-- The inverse and its literal first epsilon derivative obey the same
one-high bound with exactly one additional forward derivative, independently
of `r` (`app:ch_seed:prop:seed-phase-charts`). -/
theorem exists_fiber_inverse_epsilon_cNorm_bound_on_graph (a : (ℝ × P) × E)
    {ρ : ℝ} (hρ : 0 < ρ) {W : Set ((ℝ × P) × E)}
    (hW : IsOpen W) (hball : closedBall a ρ ⊆ W)
    (G : E ≃L[ℝ] E) {M : ℝ} (hM : 0 ≤ M) (r : ℕ) :
    ∃ C > (0 : ℝ), ∀ (f g : (ℝ × P) × E → E) (V K : Set ((ℝ × P) × E)),
      IsOpen V → IsCompact K → K ⊆ V →
      ContDiffOn ℝ ∞ f W → ContDiffOn ℝ ∞ g V →
      cNorm (closedBall a ρ) 1 f ≤ M →
      MapsTo (inverseGraph g) K (closedBall a ρ) →
      (∀ q ∈ K,
        ‖(G.symm : E →L[ℝ] E).comp (fderiv ℝ (fun u ↦ f (q.1, u)) (g q)) -
          ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) →
      (∀ q ∈ V, f (inverseGraph g q) = q.2) →
      cNorm K r g + cNorm K r (fun q : (ℝ × P) × E ↦
        deriv (fun ε ↦ g ((ε, q.1.2), q.2)) q.1.1) ≤
        C * (1 + cNorm (closedBall a ρ) (r + 1) f) := by
  obtain ⟨C, hC, hb⟩ := exists_fiber_inverse_cNorm_bound_on_graph a hρ hW hball G hM (r + 1)
  refine ⟨2 * C, by positivity, ?_⟩
  intro f g V K hV hK hKV hf hg hlow hrange hgap heq
  have hi := hb f g V K hV hK hKV hf hg hlow hrange hgap heq
  have he := cNorm_deriv_epsilon_le hV hg hK hKV r
  have hm := cNorm_mono_order (f := g) (s := K) (Nat.le_succ r)
  linarith

end Fiber

end JanetCartan.FullPhaseCharts.ActualEstimates
