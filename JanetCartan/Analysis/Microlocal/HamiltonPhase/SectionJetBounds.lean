module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.SymbolStability
public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.JetBounds
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Jet estimates for the initial energy section

For `app:lem:common-hamilton-phase` and
`app:ch_regular_base:lem:buffered-interpolation`, these estimates connect the
scalar symbol, its initial energy equation, and the actual initial section used
by `exists_autonomousFlow_joint_cNorm_bound`.

The equation and section insertion estimates have loss zero, with constants
chosen before the variable symbol and root. All root derivatives are derived
from the energy equation and transverse gap, using the implicit partition
recurrence and interpolation on the buffered cylinder. The resulting root
and state bounds have derivative loss zero. The final theorem applies them
at all orders to the existing common-cylinder construction in a fixed `C³`
neighborhood of the reference symbol.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- `app:lem:common-hamilton-phase`: pulling the symbol back to the fixed
transverse cylinder and subtracting its energy coordinate is linear in the
symbol's norm of the same order. This supplies the equation norm for the
implicit-root estimate consumed by the initial-section flow budget. -/
theorem exists_sectionEnergy_cNorm_bound_all
    (j : U →ₗᵢ[ℝ] E) (ν : E) {K : Set (InitialData U × ℝ)}
    (hK : IsCompact K) (n : ℕ) :
    ∃ B > (0 : ℝ), ∀ (H : HomogeneousSymbol E) (D L : Set (E × E)),
      IsOpen D → ContDiffOn ℝ ∞ H.h D → IsCompact L → L ⊆ D →
      MapsTo (transverseSectionState j ν) K L →
      cNorm K n (sectionEnergyEquation H j ν) ≤ B * (1 + cNorm L n H.h) := by
  let A := compositionMultiplicity n * (1 + cNorm K n (transverseSectionState j ν)) ^ n
  let e : InitialData U × ℝ → ℝ := fun w ↦ w.1.2.1
  let N := cNorm K n e
  have hN : 0 ≤ N := cNorm_nonneg K n e
  refine ⟨1 + |A| + N, by positivity, ?_⟩
  intro H D L hD hH hL hLD hmap
  have hs : ContDiff ℝ n (transverseSectionState j ν) :=
    (contDiff_transverseSectionState j ν).of_le (by simp)
  have he : ContDiff ℝ n e := contDiff_fst.snd.fst
  have hh : ∀ w ∈ K, ContDiffAt ℝ n H.h (transverseSectionState j ν w) :=
    fun w hw ↦ (hH.contDiffAt (hD.mem_nhds (hLD (hmap hw)))).of_le (by simp)
  have hb := cNorm_comp_le_polynomial (s := K) (r := n)
    (fun _ _ ↦ hs.contDiffAt) hh
    (fun _ hn ↦ bddAbove_norm_iteratedFDeriv hK hs hn)
    (cNorm_nonneg L n H.h) (fun k hk w hw ↦
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
        (fun z hz ↦ (hH.contDiffAt (hD.mem_nhds (hLD hz))).of_le (by simp))
        (hmap hw) hk)
  have hb' : cNorm K n (H.h ∘ transverseSectionState j ν) ≤ A * cNorm L n H.h := by
    calc
      _ ≤ _ := hb
      _ = _ := by dsimp [A]; ring
  have hadd := cNorm_add_le_of_contDiffAt hK
    (fun w hw ↦ (hh w hw).comp w hs.contDiffAt)
    (fun _ _ ↦ he.contDiffAt.neg)
  change cNorm K n (sectionEnergyEquation H j ν) ≤
    cNorm K n (H.h ∘ transverseSectionState j ν) + cNorm K n (-e) at hadd
  rw [cNorm_neg] at hadd
  have hA := le_abs_self A
  have hHnorm := cNorm_nonneg L n H.h
  calc
    _ ≤ A * cNorm L n H.h + N := hadd.trans (add_le_add hb' le_rfl)
    _ ≤ (1 + |A| + N) * (1 + cNorm L n H.h) := by
      nlinarith [mul_nonneg hHnorm (sub_nonneg.mpr hA), abs_nonneg A,
        mul_nonneg hN hHnorm]

private theorem cNorm_postLinear_of_contDiffAt
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

/-- `app:ch_regular_base:lem:buffered-interpolation`: the actual initial state
depends affinely on the scalar root, so its high norm occurs only linearly, with
loss zero. The constant precedes the root. The root estimate must be supplied
separately before this closes the section input of
`exists_autonomousFlow_joint_cNorm_bound`. -/
theorem exists_sectionRootState_cNorm_bound
    (j : U →ₗᵢ[ℝ] E) (ν : E) {K : Set (InitialData U)} (hK : IsCompact K) (n : ℕ) :
    ∃ C > (0 : ℝ), ∀ g : InitialData U → ℝ,
      (∀ s ∈ K, ContDiffAt ℝ n g s) →
      cNorm K n (fun s ↦ transverseSectionState j ν (s, g s)) ≤
        C * (1 + cNorm K n g) := by
  let b : InitialData U → E × E := fun s ↦ (j s.1, j s.2.2)
  let L : ℝ →L[ℝ] E × E := (ContinuousLinearMap.id ℝ ℝ).smulRight (0, ν)
  let N := cNorm K n b
  have hN : 0 ≤ N := cNorm_nonneg K n b
  refine ⟨1 + N + ‖L‖, by positivity, ?_⟩
  intro g hg
  have hb : ContDiff ℝ n b := (j.contDiff.comp contDiff_fst).prodMk
    (j.contDiff.comp contDiff_snd.snd)
  have heq : (fun s ↦ transverseSectionState j ν (s, g s)) = b + L ∘ g := by
    funext s
    simp [transverseSectionState, b, L, add_comm]
  rw [heq]
  have hadd := cNorm_add_le_of_contDiffAt hK (fun _ _ ↦ hb.contDiffAt)
    (fun s hs ↦ L.contDiff.contDiffAt.comp s (hg s hs))
  have hlin := cNorm_postLinear_of_contDiffAt hK n L hg
  have hgN := cNorm_nonneg K n g
  calc
    _ ≤ N + ‖L‖ * cNorm K n g := hadd.trans (add_le_add le_rfl hlin)
    _ ≤ (1 + N + ‖L‖) * (1 + cNorm K n g) := by nlinarith [norm_nonneg L]

/-- `app:lem:common-hamilton-phase`: the differentiated exact section equation.
The coefficient is the actual normal Hamilton velocity, rather than a chosen
root-jet budget. This is the base identity for implicit differentiation. -/
theorem normalVelocity_smul_fderiv_sectionRoot
    (H : HomogeneousSymbol E) (j : U →ₗᵢ[ℝ] E) (ν : E)
    {g : InitialData U → ℝ} {s : InitialData U}
    (hg : DifferentiableAt ℝ g s)
    (hstate : transverseSectionState j ν (s, g s) ∈ H.domain)
    (heq : ∀ᶠ q in 𝓝 s, H.h (transverseSectionState j ν (q, g q)) = q.2.1) :
    ⟪H.hp (transverseSectionState j ν (s, g s)), ν⟫_ℝ • fderiv ℝ g s =
      -(fderiv ℝ (sectionEnergyEquation H j ν) (s, g s) ∘L
        ContinuousLinearMap.inl ℝ (InitialData U) ℝ) := by
  have hf : DifferentiableAt ℝ (sectionEnergyEquation H j ν) (s, g s) :=
    ((H.hasFDerivAt_h _ hstate).differentiableAt.comp _
      ((contDiff_transverseSectionState j ν).differentiable (by simp)).differentiableAt).sub
      ((show ContDiff ℝ ∞ (fun w : InitialData U × ℝ ↦ w.1.2.1) from
        contDiff_fst.snd.fst).contDiffAt.differentiableAt (by simp))
  rw [← scalarDerivative_sectionEnergyEquation H j ν hstate]
  exact CharacteristicRoot.scalarDerivative_smul_fderiv_root hf hg
    (heq.mono fun q hq ↦ sub_eq_zero.mpr hq)

/-- `app:lem:common-hamilton-phase`: the actual root has a uniform first-order
budget on the inner parameter ball. Its value bound comes from the root cylinder
and its derivative bound from the equation divided by the transverse gap.
The constant is fixed before the symbol and root; no root-jet bound is assumed.
This supplies the low-order input to the higher implicit-root induction. -/
theorem exists_sectionRoot_cNorm_one_bound [FiniteDimensional ℝ U]
    (j : U →ₗᵢ[ℝ] E) (ν : E) (s₀ : InitialData U) (τ₀ : ℝ)
    {r a c : ℝ} (hr : 0 < r) (ha : 0 < a) (hc : 0 < c) :
    let K := closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)
    ∃ C > (0 : ℝ), ∀ (H : HomogeneousSymbol E) (D L : Set (E × E))
      (g : InitialData U → ℝ),
      IsOpen D → D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
      IsCompact L → L ⊆ D → MapsTo (transverseSectionState j ν) K L →
      ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) →
      (∀ s ∈ ball s₀ (2 * r), g s ∈ Icc (τ₀ - a) (τ₀ + a) ∧
        H.h (transverseSectionState j ν (s, g s)) = s.2.1 ∧
        c ≤ |⟪H.hp (transverseSectionState j ν (s, g s)), ν⟫_ℝ|) →
      cNorm (closedBall s₀ r) 1 g ≤ C * (1 + cNorm L 1 H.h) := by
  let K := closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  obtain ⟨B, hB, hbound⟩ := exists_sectionEnergy_cNorm_bound_all j ν hK 1
  let G := |τ₀| + a
  have hG : 0 ≤ G := by dsimp [G]; positivity
  refine ⟨1 + G + B / c, by positivity, ?_⟩
  intro H D L g hD hDH hH hL hLD hmap hg hroot
  have hsub : closedBall s₀ r ⊆ ball s₀ (2 * r) :=
    closedBall_subset_ball (by linarith)
  have hf : ∀ w ∈ K, ContDiffAt ℝ 1 (sectionEnergyEquation H j ν) w := by
    intro w hw
    exact (((hH.contDiffAt (hD.mem_nhds (hLD (hmap hw)))).comp w
      (contDiff_transverseSectionState j ν).contDiffAt).sub
        (show ContDiffAt ℝ ∞ (fun v : InitialData U × ℝ ↦ v.1.2.1) w from
          contDiff_fst.snd.fst.contDiffAt)).of_le (by simp)
  have hb := hbound H D L hD hH hL hLD hmap
  have hjet : ∀ s ∈ closedBall s₀ r, ‖fderiv ℝ g s‖ ≤
      (B * (1 + cNorm L 1 H.h)) / c := by
    intro s hs
    have hs' := hsub hs
    have hsk : (s, g s) ∈ K := ⟨ball_subset_closedBall hs', (hroot s hs').1⟩
    apply CharacteristicRoot.norm_fderiv_root_le hc
      ((hf _ hsk).differentiableAt one_ne_zero)
      ((hg.contDiffAt (isOpen_ball.mem_nhds hs')).differentiableAt (by simp))
    · filter_upwards [isOpen_ball.mem_nhds hs'] with q hq
      exact sub_eq_zero.mpr (hroot q hq).2.1
    · rw [scalarDerivative_sectionEnergyEquation H j ν (hDH (hLD (hmap hsk)))]
      exact (hroot s hs').2.2
    · rw [← norm_iteratedFDeriv_one]
      exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hf hsk (le_refl 1)).trans hb
  have hval : ∀ s ∈ closedBall s₀ r, ‖g s‖ ≤ G := by
    intro s hs
    rw [Real.norm_eq_abs]
    have ht := (hroot s (hsub hs)).1
    exact abs_le.mpr ⟨by dsimp [G]; linarith [neg_abs_le τ₀, ht.1],
      by dsimp [G]; linarith [le_abs_self τ₀, ht.2]⟩
  have hHnorm := cNorm_nonneg L 1 H.h
  have hb' := cNorm_le_sum_of_bounds (s := closedBall s₀ r) (r := 1) (f := g)
    (C := fun k ↦ if k = 0 then G else (B * (1 + cNorm L 1 H.h)) / c)
    (by intro k _; split_ifs <;> positivity) (by
      intro k hk s hs
      interval_cases k
      · simpa only [norm_iteratedFDeriv_zero, ↓reduceIte] using hval s hs
      · simpa only [norm_iteratedFDeriv_one, Nat.one_ne_zero, ↓reduceIte] using hjet s hs)
  have hb'' : cNorm (closedBall s₀ r) 1 g ≤ G + (B / c) * (1 + cNorm L 1 H.h) := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      ↓reduceIte, Nat.one_ne_zero, mul_div_right_comm] using hb'
  exact hb''.trans (by nlinarith [div_nonneg hB.le hc.le, mul_nonneg hG hHnorm])

/-- `app:lem:common-hamilton-phase`: the existing common-cylinder construction
provides actual energy roots and initial states with a fixed low-order budget.
The radii, transverse gap, perturbation threshold and budget are all chosen
before the varying symbol. This establishes applicability of the low-order
estimate on the very cylinder produced by `exists_uniform_C1_stable_sectionRoot`;
it does not yet assert the arbitrary-order root estimate. -/
theorem exists_uniform_sectionRoot_low_budget [FiniteDimensional ℝ U]
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) {s₀ : InitialData U} {τ₀ : ℝ}
    (hbase : transverseSectionState j ν (s₀, τ₀) ∈ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    ∃ r a c δ N : ℝ, 0 < r ∧ 0 < a ∧ 0 < c ∧ 0 < δ ∧ 0 < N ∧
      let K := closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)
      let L := transverseSectionState j ν '' K
      IsCompact K ∧ IsCompact L ∧ L ⊆ D ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        cNorm L 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ g : InitialData U → ℝ, ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) ∧
          (∀ s ∈ ball s₀ (2 * r), g s ∈ Ioo (τ₀ - a) (τ₀ + a) ∧
            transverseSectionState j ν (s, g s) ∈ L ∧
            H.h (transverseSectionState j ν (s, g s)) = s.2.1 ∧
            c ≤ |⟪H.hp (transverseSectionState j ν (s, g s)), ν⟫_ℝ|) ∧
          cNorm (closedBall s₀ r) 1 g +
            cNorm (closedBall s₀ r) 1 (fun s ↦ transverseSectionState j ν (s, g s)) ≤ N := by
  obtain ⟨r, a, c, C, δ, g₀, hr, ha, hc, _, hδ, hK, hL, hLD,
      _, _, _, hpert⟩ :=
    exists_uniform_C1_stable_sectionRoot H₀ hD hDH₀ hH₀ j ν hbase henergy htrans
  let K := closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)
  let L := transverseSectionState j ν '' K
  obtain ⟨A, hA, hrootbound⟩ := exists_sectionRoot_cNorm_one_bound j ν s₀ τ₀ hr ha hc
  obtain ⟨B, hB, hstatebound⟩ :=
    exists_sectionRootState_cNorm_bound j ν (isCompact_closedBall s₀ r) 1
  let M := A * (1 + δ + cNorm L 1 H₀.h)
  have hM : 0 ≤ M := by
    have := cNorm_nonneg L 1 H₀.h
    dsimp [M]
    positivity
  refine ⟨r, a, c, δ, 1 + M + B * (1 + M), hr, ha, hc, hδ,
    by positivity, hK, hL, hLD, ?_⟩
  intro H hDH hH hsmall
  obtain ⟨g, hg, hroot, _, _⟩ := hpert H hDH hH hsmall
  have hHnorm : cNorm L 1 H.h ≤ δ + cNorm L 1 H₀.h := by
    have hadd := cNorm_add_le_of_contDiffAt (r := 1) hL
      (fun z hz ↦ ((hH.sub hH₀).contDiffAt (hD.mem_nhds (hLD hz))).of_le (by simp))
      (fun z hz ↦ (hH₀.contDiffAt (hD.mem_nhds (hLD hz))).of_le (by simp))
    simp only [Pi.add_def, sub_add_cancel] at hadd
    apply hadd.trans
    exact add_le_add ((cNorm_mono_order (by norm_num : 1 ≤ 3)).trans hsmall) le_rfl
  have hgb : cNorm (closedBall s₀ r) 1 g ≤ M := by
    apply (hrootbound H D L g hD hDH hH hL hLD
      (fun _ hw ↦ mem_image_of_mem _ hw) hg (fun s hs ↦
        ⟨Ioo_subset_Icc_self (hroot s hs).1, (hroot s hs).2.2⟩)).trans
    exact mul_le_mul_of_nonneg_left (by linarith) hA.le
  have hsb := hstatebound g (fun s hs ↦
    (hg.contDiffAt (isOpen_ball.mem_nhds
      (closedBall_subset_ball (by linarith : r < 2 * r) hs))).of_le (by simp))
  refine ⟨g, hg, hroot, ?_⟩
  have hsb' := hsb.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hgb) hB.le)
  linarith

/-- `app:lem:common-hamilton-phase`: at every order at least two, the exact
energy equation isolates the highest root jet with coefficient equal to the
normal Hamilton velocity. The remainder contains only lower root jets; the
implicit-root induction used below estimates these without additional premises. -/
theorem normalVelocity_smul_iteratedFDeriv_sectionRoot
    (H : HomogeneousSymbol E) (j : U →ₗᵢ[ℝ] E) (ν : E)
    {n : ℕ} (hn : 2 ≤ n) {g : InitialData U → ℝ} {s : InitialData U}
    (hf : ContDiffAt ℝ n (sectionEnergyEquation H j ν) (s, g s))
    (hg : ContDiffAt ℝ n g s)
    (hstate : transverseSectionState j ν (s, g s) ∈ H.domain)
    (heq : ∀ᶠ q in 𝓝 s, H.h (transverseSectionState j ν (q, g q)) = q.2.1) :
    ⟪H.hp (transverseSectionState j ν (s, g s)), ν⟫_ℝ • iteratedFDeriv ℝ n g s =
      -CharacteristicRoot.rootJetPartitionRemainder n (sectionEnergyEquation H j ν) g s := by
  rw [← scalarDerivative_sectionEnergyEquation H j ν hstate]
  exact CharacteristicRoot.scalarDerivative_smul_iteratedFDeriv_root hn hf hg
    (heq.mono fun q hq ↦ sub_eq_zero.mpr hq)

/-- `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`: the actual energy root has a one-high bound
with loss zero. Constants depend on the fixed geometry, transverse gap and
first symbol norm, and precede the varying symbol and root. Cylinder
interpolation and the implicit partition induction discharge all higher and
lower root-jet premises. This supplies the root bound for the initial state
in `exists_autonomousFlow_joint_cNorm_bound`. -/
theorem exists_sectionRoot_cNorm_bound_all [FiniteDimensional ℝ U]
    (j : U →ₗᵢ[ℝ] E) (ν : E) (s₀ : InitialData U) (τ₀ : ℝ)
    {r a c M : ℝ} (hr : 0 < r) (ha : 0 < a) (hc : 0 < c) (hM : 0 ≤ M)
    {D L : Set (E × E)} (hD : IsOpen D) (hL : IsCompact L) (hLD : L ⊆ D)
    (hmap : MapsTo (transverseSectionState j ν)
      (closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)) L) (n : ℕ) :
    ∃ C > (0 : ℝ), ∀ (H : HomogeneousSymbol E) (g : InitialData U → ℝ),
      D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D → cNorm L 1 H.h ≤ M →
      ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) →
      (∀ s ∈ ball s₀ (2 * r), g s ∈ Icc (τ₀ - a) (τ₀ + a) ∧
        H.h (transverseSectionState j ν (s, g s)) = s.2.1 ∧
        c ≤ |⟪H.hp (transverseSectionState j ν (s, g s)), ν⟫_ℝ|) →
      cNorm (closedBall s₀ r) n g ≤ C * (1 + cNorm L n H.h) := by
  let K := closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)
  let W := transverseSectionState j ν ⁻¹' D
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hW : IsOpen W := hD.preimage (contDiff_transverseSectionState j ν).continuous
  have hKW : K ⊆ W := fun _ hw ↦ hLD (hmap hw)
  obtain ⟨B₁, hB₁, hlow⟩ := exists_sectionEnergy_cNorm_bound_all j ν hK 1
  obtain ⟨B, hB, hhigh⟩ := exists_sectionEnergy_cNorm_bound_all j ν hK n
  obtain ⟨A, hA, hbound⟩ := CharacteristicRoot.exists_root_cNorm_bound_cylinder_on
    s₀ τ₀ hr ha hc (show 0 ≤ B₁ * (1 + M) by positivity) n hW hKW
  refine ⟨A * (1 + B), by positivity, ?_⟩
  intro H g hDH hH hHM hg hroot
  have hf : ContDiffOn ℝ ∞ (sectionEnergyEquation H j ν) W :=
    (hH.comp (contDiff_transverseSectionState j ν).contDiffOn
      (fun _ hw ↦ hw)).sub contDiff_fst.snd.fst.contDiffOn
  have hfM : cNorm K 1 (sectionEnergyEquation H j ν) ≤ B₁ * (1 + M) :=
    (hlow H D L hD hH hL hLD hmap).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hHM) hB₁.le)
  have hb := hbound (sectionEnergyEquation H j ν) g hf hg hfM (by
    intro s hs
    have hsK : (s, g s) ∈ K := ⟨ball_subset_closedBall hs, (hroot s hs).1⟩
    refine ⟨(hroot s hs).1, sub_eq_zero.mpr (hroot s hs).2.1, ?_⟩
    rw [scalarDerivative_sectionEnergyEquation H j ν (hDH (hLD (hmap hsK)))]
    exact (hroot s hs).2.2)
  calc
    _ ≤ A * (1 + cNorm K n (sectionEnergyEquation H j ν)) := hb
    _ ≤ A * (1 + B * (1 + cNorm L n H.h)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hhigh H D L hD hH hL hLD hmap)) hA.le
    _ ≤ (A * (1 + B)) * (1 + cNorm L n H.h) := by
      nlinarith [mul_nonneg hA.le (cNorm_nonneg L n H.h)]

/-- `app:lem:common-hamilton-phase`: the actual energy root and initial state
obey a joint one-high bound at symbol order `n`, with no derivative loss and
no assumed root-jet budgets. The state term is the initial-section input to
`exists_autonomousFlow_joint_cNorm_bound`. -/
theorem exists_sectionRoot_and_state_cNorm_bound_all [FiniteDimensional ℝ U]
    (j : U →ₗᵢ[ℝ] E) (ν : E) (s₀ : InitialData U) (τ₀ : ℝ)
    {r a c M : ℝ} (hr : 0 < r) (ha : 0 < a) (hc : 0 < c) (hM : 0 ≤ M)
    {D L : Set (E × E)} (hD : IsOpen D) (hL : IsCompact L) (hLD : L ⊆ D)
    (hmap : MapsTo (transverseSectionState j ν)
      (closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)) L) (n : ℕ) :
    ∃ C > (0 : ℝ), ∀ (H : HomogeneousSymbol E) (g : InitialData U → ℝ),
      D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D → cNorm L 1 H.h ≤ M →
      ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) →
      (∀ s ∈ ball s₀ (2 * r), g s ∈ Icc (τ₀ - a) (τ₀ + a) ∧
        H.h (transverseSectionState j ν (s, g s)) = s.2.1 ∧
        c ≤ |⟪H.hp (transverseSectionState j ν (s, g s)), ν⟫_ℝ|) →
      cNorm (closedBall s₀ r) n g +
        cNorm (closedBall s₀ r) n (fun s ↦ transverseSectionState j ν (s, g s)) ≤
          C * (1 + cNorm L n H.h) := by
  obtain ⟨A, hA, hrootbound⟩ :=
    exists_sectionRoot_cNorm_bound_all j ν s₀ τ₀ hr ha hc hM hD hL hLD hmap n
  obtain ⟨B, hB, hstatebound⟩ :=
    exists_sectionRootState_cNorm_bound j ν (isCompact_closedBall s₀ r) n
  refine ⟨A + B * (1 + A), by positivity, ?_⟩
  intro H g hDH hH hHM hg hroot
  have hgb := hrootbound H g hDH hH hHM hg hroot
  have hsb := hstatebound g (fun s hs ↦
    (hg.contDiffAt (isOpen_ball.mem_nhds
      (closedBall_subset_ball (by linarith : r < 2 * r) hs))).of_le (by simp))
  have hsb' := hsb.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hgb) hB.le)
  nlinarith [mul_nonneg hB.le (cNorm_nonneg L n H.h)]

/-- `app:lem:common-hamilton-phase`: the existing common-cylinder construction
produces actual smooth energy roots and initial sections with one-high bounds
at every order on common domains. The radii, transverse gap, `C³` perturbation
threshold, first-order budget and all high-order constants precede the varying
symbol. Only the fixed first symbol norm is used to control the higher-order
constants, and the high symbol norm occurs linearly at the same order.
This discharges the initial-section estimates for
`exists_autonomousFlow_joint_cNorm_bound`; the Hamilton-field budget and the
flow/phase assembly are separate consumers. -/
theorem exists_uniform_sectionRoot_jet_bounds [FiniteDimensional ℝ U]
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) {s₀ : InitialData U} {τ₀ : ℝ}
    (hbase : transverseSectionState j ν (s₀, τ₀) ∈ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    ∃ r a c δ N : ℝ, 0 < r ∧ 0 < a ∧ 0 < c ∧ 0 < δ ∧ 0 < N ∧
      let K := closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)
      let L := transverseSectionState j ν '' K
      IsCompact K ∧ IsCompact L ∧ L ⊆ D ∧
      ∃ C : ℕ → ℝ, (∀ n, 0 < C n) ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        cNorm L 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ g : InitialData U → ℝ, ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) ∧
          (∀ s ∈ ball s₀ (2 * r), g s ∈ Ioo (τ₀ - a) (τ₀ + a) ∧
            transverseSectionState j ν (s, g s) ∈ L ∧
            H.h (transverseSectionState j ν (s, g s)) = s.2.1 ∧
            c ≤ |⟪H.hp (transverseSectionState j ν (s, g s)), ν⟫_ℝ|) ∧
          (cNorm (closedBall s₀ r) 1 g +
            cNorm (closedBall s₀ r) 1 (fun s ↦ transverseSectionState j ν (s, g s)) ≤ N) ∧
          ∀ n, cNorm (closedBall s₀ r) n g +
            cNorm (closedBall s₀ r) n (fun s ↦ transverseSectionState j ν (s, g s)) ≤
              C n * (1 + cNorm L n H.h) := by
  obtain ⟨r, a, c, δ, N, hr, ha, hc, hδ, hN, hK, hL, hLD, hpert⟩ :=
    exists_uniform_sectionRoot_low_budget H₀ hD hDH₀ hH₀ j ν hbase henergy htrans
  let K := closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)
  let L := transverseSectionState j ν '' K
  let M := δ + cNorm L 1 H₀.h
  have hM : 0 ≤ M := add_nonneg hδ.le (cNorm_nonneg L 1 H₀.h)
  have hb := fun n ↦ exists_sectionRoot_and_state_cNorm_bound_all
    j ν s₀ τ₀ hr ha hc hM hD hL hLD (fun _ hw ↦ mem_image_of_mem _ hw) n
  choose C hC hbound using hb
  refine ⟨r, a, c, δ, N, hr, ha, hc, hδ, hN, hK, hL, hLD, C, hC, ?_⟩
  intro H hDH hH hsmall
  obtain ⟨g, hg, hroot, hlow⟩ := hpert H hDH hH hsmall
  have hHM : cNorm L 1 H.h ≤ M := by
    have hadd := cNorm_add_le_of_contDiffAt (r := 1) hL
      (fun z hz ↦ ((hH.sub hH₀).contDiffAt (hD.mem_nhds (hLD hz))).of_le (by simp))
      (fun z hz ↦ (hH₀.contDiffAt (hD.mem_nhds (hLD hz))).of_le (by simp))
    simp only [Pi.add_def, sub_add_cancel] at hadd
    exact hadd.trans (add_le_add
      ((cNorm_mono_order (by norm_num : 1 ≤ 3)).trans hsmall) le_rfl)
  refine ⟨g, hg, hroot, hlow, fun n ↦ hbound n H g hDH hH hHM hg ?_⟩
  intro s hs
  exact ⟨Ioo_subset_Icc_self (hroot s hs).1, (hroot s hs).2.2⟩

end JanetCartan.HamiltonPhase
