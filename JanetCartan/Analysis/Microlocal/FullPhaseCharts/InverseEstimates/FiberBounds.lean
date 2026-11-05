module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.LowerBound
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.Epsilon
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.LocalNorms

/-!
# Joint tame bounds for a fixed family of data inverses

The final paragraph of `app:ch_seed:prop:seed-phase-charts` requires joint
physical, spectator, normalized data and epsilon derivatives. Augment the
forward map by the unchanged parameters. Its differential lower bound follows
from the data-Jacobian gap and the forward `C¹` bound, without requiring small
parameter derivatives. `LowerBound` then supplies the Hamilton partition
induction. The actual smooth inverse and buffered containments remain inputs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.FullPhaseCharts.InverseEstimates

/-- Linear output changes preserve one-high bounds for the full and transverse
charts in `app:ch_seed:prop:seed-phase-charts`. Smoothness is local to the
specified compact set. -/
theorem cNorm_postLinear_le_on
    {P F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set P} (hK : IsCompact K) (n : ℕ) (L : F →L[ℝ] G)
    {f : P → F} (hf : ∀ x ∈ K, ContDiffAt ℝ n f x) :
    cNorm K n (L ∘ f) ≤ ‖L‖ * cNorm K n f := by
  simp only [cNorm, Finset.mul_sum]
  apply cNorm_le_sum_of_bounds
    (fun k _ ↦ mul_nonneg (norm_nonneg _) (sSup_norm_iteratedFDeriv_nonneg K k f))
  intro k hk x hx
  apply (L.norm_iteratedFDeriv_comp_left (hf x hx) (by exact_mod_cast hk)).trans
  exact mul_le_mul_of_nonneg_left
    (le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hK hf hk)
      (mem_image_of_mem _ hx)) (norm_nonneg _)


variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The differential of the augmented forward map has a uniform lower bound
from the data gap and a low joint bound. This is the augmentation step in
`app:ch_seed:prop:seed-phase-charts`; it assumes no small parameter derivative. -/
theorem norm_le_augmented_differential (G : E ≃L[ℝ] E)
    (D : (P × E) →L[ℝ] E) {M : ℝ} (hM : 0 ≤ M) (hD : ‖D‖ ≤ M)
    (hgap : ‖(G.symm : E →L[ℝ] E).comp (D.comp (ContinuousLinearMap.inr ℝ P E)) -
      ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) (v : P × E) :
    ‖v‖ ≤ (1 + 2 * ‖(G.symm : E →L[ℝ] E)‖ * (1 + M)) * ‖(v.1, D v)‖ := by
  let J := 2 * ‖(G.symm : E →L[ℝ] E)‖
  have hJ : 0 ≤ J := by positivity
  have hsplit : D (0, v.2) = D v - D (v.1, 0) := by
    rw [← map_sub]; congr 1; ext <;> simp
  have hv := norm_le_twice_normalized_image G hgap v.2
  have hb : ‖v.2‖ ≤ J * (‖D v‖ + M * ‖v.1‖) := by
    apply hv.trans
    calc
      _ ≤ J * ‖D (0, v.2)‖ := by
        simpa [J, mul_assoc] using mul_le_mul_of_nonneg_left
          ((G.symm : E →L[ℝ] E).le_opNorm (D (0, v.2))) (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ J * (‖D v‖ + ‖D (v.1, 0)‖) := by rw [hsplit]; gcongr; exact norm_sub_le _ _
      _ ≤ J * (‖D v‖ + M * ‖v.1‖) := by
        gcongr
        exact (D.le_opNorm (v.1, 0)).trans (by
          simpa using mul_le_mul_of_nonneg_right hD (norm_nonneg v.1))
  have hp := norm_fst_le (v.1, D v)
  have hd := norm_snd_le (v.1, D v)
  rw [Prod.norm_def]
  apply max_le
  · nlinarith [norm_nonneg (v.1, D v), mul_nonneg hJ (add_nonneg zero_le_one hM)]
  · have hh := add_le_add hd (mul_le_mul_of_nonneg_left hp hM)
    have hh' := mul_le_mul_of_nonneg_left hh hJ
    dsimp [J] at *
    have hpos : 0 ≤ max ‖v.1‖ ‖D v‖ := le_trans (norm_nonneg _) (le_max_left _ _)
    nlinarith

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ E]

/-- Joint one-high inverse bound from the actual fixed inverse equation and
the data derivative gap (`app:ch_seed:prop:seed-phase-charts`). The constant
precedes the maps, and depends only on order, the source ball, a fixed low
forward bound and the central linear equivalence. No inverse jets are inputs. -/
theorem exists_fiber_inverse_cNorm_bound (a : P × E) {ρ : ℝ} (hρ : 0 < ρ)
    {W : Set (P × E)} (hW : IsOpen W) (hball : closedBall a ρ ⊆ W)
    (G : E ≃L[ℝ] E) {M : ℝ} (hM : 0 ≤ M) (n : ℕ) :
    ∃ C > (0 : ℝ), ∀ (f g : P × E → E) (V K : Set (P × E)),
      IsOpen V → IsCompact K → K ⊆ V →
      ContDiffOn ℝ ∞ f W → ContDiffOn ℝ ∞ g V →
      cNorm (closedBall a ρ) 1 f ≤ M →
      MapsTo (inverseGraph g) K (closedBall a ρ) →
      (∀ x ∈ closedBall a ρ,
        ‖(G.symm : E →L[ℝ] E).comp (fderiv ℝ (fun u ↦ f (x.1, u)) x.2) -
          ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) →
      (∀ q ∈ V, f (inverseGraph g q) = q.2) →
      cNorm K n g ≤ C * (1 + cNorm (closedBall a ρ) n f) := by
  let Q : (P × E) → P := Prod.fst
  let J := 1 + 2 * ‖(G.symm : E →L[ℝ] E)‖ * (1 + M)
  have hJ : 0 ≤ J := by positivity
  obtain ⟨D, hD, hb⟩ := exists_inverse_cNorm_bound_of_lower_bound a hρ hW hball
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
      intro x hx v
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
        exact hgap x hx) (by
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
theorem exists_fiber_inverse_epsilon_cNorm_bound (a : (ℝ × P) × E)
    {ρ : ℝ} (hρ : 0 < ρ) {W : Set ((ℝ × P) × E)}
    (hW : IsOpen W) (hball : closedBall a ρ ⊆ W)
    (G : E ≃L[ℝ] E) {M : ℝ} (hM : 0 ≤ M) (r : ℕ) :
    ∃ C > (0 : ℝ), ∀ (f g : (ℝ × P) × E → E) (V K : Set ((ℝ × P) × E)),
      IsOpen V → IsCompact K → K ⊆ V →
      ContDiffOn ℝ ∞ f W → ContDiffOn ℝ ∞ g V →
      cNorm (closedBall a ρ) 1 f ≤ M →
      MapsTo (inverseGraph g) K (closedBall a ρ) →
      (∀ x ∈ closedBall a ρ,
        ‖(G.symm : E →L[ℝ] E).comp (fderiv ℝ (fun u ↦ f (x.1, u)) x.2) -
          ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) →
      (∀ q ∈ V, f (inverseGraph g q) = q.2) →
      cNorm K r g + cNorm K r (fun q : (ℝ × P) × E ↦
        deriv (fun ε ↦ g ((ε, q.1.2), q.2)) q.1.1) ≤
        C * (1 + cNorm (closedBall a ρ) (r + 1) f) := by
  obtain ⟨C, hC, hb⟩ := exists_fiber_inverse_cNorm_bound a hρ hW hball G hM (r + 1)
  refine ⟨2 * C, by positivity, ?_⟩
  intro f g V K hV hK hKV hf hg hlow hrange hgap heq
  have hi := hb f g V K hV hK hKV hf hg hlow hrange hgap heq
  have he := cNorm_deriv_epsilon_le hV hg hK hKV r
  have hm := cNorm_mono_order (f := g) (s := K) (Nat.le_succ r)
  linarith

end JanetCartan.FullPhaseCharts.InverseEstimates
