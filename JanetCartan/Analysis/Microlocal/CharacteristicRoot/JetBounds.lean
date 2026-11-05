module

public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.Stability
public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.CylinderInterpolation
public import JanetCartan.Analysis.ODE.HigherVariational.Partitions
public import JanetCartan.Analysis.ContDiff.Norm.Composition.FlowForcing.Partitions

/-!
# Higher derivatives of scalar implicit roots

The implicit differentiation step of `app:ch_regular_base:lem:buffered-interpolation`
and `app:lem:common-hamilton-phase`. The consumer is the arbitrary-order initial
section estimate in `HamiltonPhase/SectionJetBounds.lean`.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace JanetCartan.CharacteristicRoot

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

private lemma iteratedFDeriv_id_high {n : ℕ} (hn : 2 ≤ n) (p : P) :
    iteratedFDeriv ℝ n (id : P → P) p = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + k = (k + 1) + 1 by omega]
  ext v
  rw [iteratedFDeriv_succ_apply_right]
  simp only [fderiv_id, iteratedFDeriv_succ_const, Pi.zero_apply,
    zero_apply]

/-- `app:ch_regular_base:lem:buffered-interpolation`: above order one, the
parameter component of a root graph has zero derivative. This identifies the
single-block term in the differentiated implicit equation. -/
theorem iteratedFDeriv_rootGraph_high {n : ℕ} (hn : 2 ≤ n)
    {g : P → ℝ} {p : P} (hg : ContDiffAt ℝ n g p) :
    iteratedFDeriv ℝ n (fun q ↦ (q, g q)) p =
      (0 : P [×n]→L[ℝ] P).prod (iteratedFDeriv ℝ n g p) := by
  have h := iteratedFDeriv_prodMk contDiffAt_id hg le_rfl
  simp only [id_eq, iteratedFDeriv_id_high hn] at h
  exact h

/-- `app:ch_regular_base:lem:buffered-interpolation`: the actual lower-root-jet
remainder, indexed by partitions with at least two blocks. Every inner derivative
has order strictly below `n`, by `ODE.partSize_lt_of_two_le_length`. -/
def rootJetPartitionRemainder (n : ℕ) (f : P × ℝ → ℝ) (g : P → ℝ) (p : P) :
    P [×n]→L[ℝ] ℝ :=
  ∑ s : OrderedFinpartition n with 2 ≤ s.length,
    s.compAlongOrderedFinpartition (iteratedFDeriv ℝ s.length f (p, g p))
      (fun i ↦ iteratedFDeriv ℝ (s.partSize i) (fun q ↦ (q, g q)) p)

/-- `app:lem:common-hamilton-phase`: differentiating the actual root equation at
order at least two isolates the transverse derivative times the highest root
jet. No partition identity or bound on the root is assumed. -/
theorem scalarDerivative_smul_iteratedFDeriv_root {n : ℕ} (hn : 2 ≤ n)
    {f : P × ℝ → ℝ} {g : P → ℝ} {p : P}
    (hf : ContDiffAt ℝ n f (p, g p)) (hg : ContDiffAt ℝ n g p)
    (heq : ∀ᶠ q in 𝓝 p, f (q, g q) = 0) :
    scalarDerivative f (p, g p) • iteratedFDeriv ℝ n g p =
      -rootJetPartitionRemainder n f g p := by
  classical
  let G : P → P × ℝ := fun q ↦ (q, g q)
  let T := fun s : OrderedFinpartition n ↦
    s.compAlongOrderedFinpartition (iteratedFDeriv ℝ s.length f (G p))
      (fun i ↦ iteratedFDeriv ℝ (s.partSize i) G p)
  have hnpos : 0 < n := by omega
  have hzero : iteratedFDeriv ℝ n (f ∘ G) p = 0 := by
    have heq' : (f ∘ G) =ᶠ[𝓝 p] (fun _ ↦ 0) := heq
    have h := (heq'.iteratedFDeriv ℝ n).eq_of_nhds
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using h
  have hchain := iteratedFDeriv_comp (f := G) (g := f) hf
    (contDiffAt_id.prodMk hg) le_rfl
  rw [FormalMultilinearSeries.taylorComp] at hchain
  change iteratedFDeriv ℝ n (f ∘ G) p = ∑ s, T s at hchain
  have hfilter : Finset.univ.filter (fun s : OrderedFinpartition n ↦ ¬ 2 ≤ s.length) =
      {ODE.singleBlockPartition n hnpos} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact ODE.eq_singleBlockPartition_of_length_eq_one hnpos s
        (by have := s.length_pos hnpos; omega)
    · rintro rfl
      simp [ODE.singleBlockPartition]
  have hsum := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (OrderedFinpartition n)) (fun s ↦ 2 ≤ s.length) T
  rw [hfilter, Finset.sum_singleton] at hsum
  have htop : T (ODE.singleBlockPartition n hnpos) =
      scalarDerivative f (p, g p) • iteratedFDeriv ℝ n g p := by
    ext v
    simp only [T, OrderedFinpartition.compAlongOrderFinpartition_apply,
      OrderedFinpartition.applyOrderedFinpartition_apply, ODE.singleBlockPartition,
      iteratedFDeriv_one_apply]
    change fderiv ℝ f (p, g p) (iteratedFDeriv ℝ n (fun q ↦ (q, g q)) p v) = _
    rw [iteratedFDeriv_rootGraph_high hn hg]
    simp only [ContinuousMultilinearMap.prod_apply, zero_apply,
      smul_apply, smul_eq_mul]
    have hv : ((0, iteratedFDeriv ℝ n g p v) : P × ℝ) =
        (iteratedFDeriv ℝ n g p v) • ((0, 1) : P × ℝ) := by simp
    rw [hv, map_smul]
    simp only [smul_eq_mul, scalarDerivative, mul_comm]
  rw [htop, ← hchain, hzero] at hsum
  apply eq_neg_of_add_eq_zero_left
  rw [add_comm]
  exact hsum

/-- `app:ch_regular_base:lem:buffered-interpolation`: the actual highest root jet
is bounded by the lower-jet partition sum divided by the transverse gap. This is
the recurrence used to derive, rather than assume, all root-jet budgets. -/
theorem norm_iteratedFDeriv_root_le_partition_sum {n : ℕ} (hn : 2 ≤ n)
    {f : P × ℝ → ℝ} {g : P → ℝ} {p : P} {c : ℝ} (hc : 0 < c)
    (hf : ContDiffAt ℝ n f (p, g p)) (hg : ContDiffAt ℝ n g p)
    (heq : ∀ᶠ q in 𝓝 p, f (q, g q) = 0)
    (hgap : c ≤ |scalarDerivative f (p, g p)|) :
    ‖iteratedFDeriv ℝ n g p‖ ≤
      (∑ s : OrderedFinpartition n with 2 ≤ s.length,
        ‖iteratedFDeriv ℝ s.length f (p, g p)‖ *
          ∏ i, ‖iteratedFDeriv ℝ (s.partSize i) (fun q ↦ (q, g q)) p‖) / c := by
  have hid := congrArg norm (scalarDerivative_smul_iteratedFDeriv_root hn hf hg heq)
  rw [norm_smul, Real.norm_eq_abs, norm_neg] at hid
  apply (le_div_iff₀ hc).mpr
  calc
    _ ≤ |scalarDerivative f (p, g p)| * ‖iteratedFDeriv ℝ n g p‖ := by
      nlinarith [norm_nonneg (iteratedFDeriv ℝ n g p)]
    _ = _ := hid
    _ ≤ _ := (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ ↦
      s.norm_compAlongOrderedFinpartition_le _ _)

private lemma partition_nat_power_product {n : ℕ} (s : OrderedFinpartition n)
    (hs : 1 ≤ s.length) (M R : ℝ) (B : ℕ → ℝ) :
    (M * R ^ (s.length - 1)) * (∏ i, B (s.partSize i) * R ^ (s.partSize i - 1)) =
      (M * ∏ i, B (s.partSize i)) * R ^ (n - 1) := by
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_mul_mul_comm,
    ← pow_add, FlowForcing.partition_excess_identity s hs]

/-- `app:ch_regular_base:lem:buffered-interpolation`: the equation's baseline-one
power profile implies the same profile for every positive root-graph jet.
Strong induction discharges all lower-root-jet bounds. The constant is chosen
before the equation, root, point and scale. This will be instantiated using
interpolation on the fixed cylinder in the section-root estimate. -/
theorem exists_rootGraph_jet_bound_of_equation_profile {M c : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (R : ℝ), 0 ≤ R → ∀ (f : P × ℝ → ℝ) (g : P → ℝ) (p : P),
      ContDiffAt ℝ n f (p, g p) → ContDiffAt ℝ n g p →
      (∀ᶠ q in 𝓝 p, f (q, g q) = 0) → c ≤ |scalarDerivative f (p, g p)| →
      (∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j f (p, g p)‖ ≤ M * R ^ (j - 1)) →
      ‖iteratedFDeriv ℝ n (fun q ↦ (q, g q)) p‖ ≤ C * R ^ (n - 1) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n = 1
    · subst n
      refine ⟨1 + M / c, by linarith [div_nonneg hM hc.le], ?_⟩
      intro R hR f g p hf hg heq hgap hprofile
      have hbound : ‖fderiv ℝ g p‖ ≤ M / c :=
        norm_fderiv_root_le hc (hf.differentiableAt one_ne_zero)
          (hg.differentiableAt one_ne_zero) heq hgap
          (by simpa only [norm_iteratedFDeriv_one, Nat.sub_self, pow_zero, mul_one]
              using hprofile 1 le_rfl le_rfl)
      have hid : ‖iteratedFDeriv ℝ 1 (id : P → P) p‖ ≤ 1 := by
        rw [norm_iteratedFDeriv_one, fderiv_id]
        exact ContinuousLinearMap.norm_id_le
      have hprod := iteratedFDeriv_prodMk contDiffAt_id hg le_rfl
      simp only [id_eq] at hprod
      rw [hprod, ContinuousMultilinearMap.opNorm_prod]
      simp only [norm_iteratedFDeriv_one] at hid ⊢
      simpa only [Nat.sub_self, pow_zero, mul_one] using
        max_le (hid.trans (by linarith [div_nonneg hM hc.le])) (by linarith :
          ‖fderiv ℝ g p‖ ≤ 1 + M / c)
    · have hn2 : 2 ≤ n := by omega
      let B : ℕ → ℝ := fun j ↦ if hj : 1 ≤ j ∧ j < n then (ih j hj.2 hj.1).choose else 1
      have hB (j : ℕ) : 1 ≤ B j := by
        dsimp [B]
        split_ifs with hj
        · exact (ih j hj.2 hj.1).choose_spec.1
        · exact le_rfl
      let S : ℝ := ∑ s : OrderedFinpartition n with 2 ≤ s.length,
        M * ∏ i, B (s.partSize i)
      have hS : 0 ≤ S := Finset.sum_nonneg fun s _ ↦
        mul_nonneg hM (Finset.prod_nonneg fun i _ ↦ zero_le_one.trans (hB _))
      refine ⟨1 + S / c, by linarith [div_nonneg hS hc.le], ?_⟩
      intro R hR f g p hf hg heq hgap hprofile
      have hlower (j : ℕ) (hj : 1 ≤ j) (hjn : j < n) :
          ‖iteratedFDeriv ℝ j (fun q ↦ (q, g q)) p‖ ≤ B j * R ^ (j - 1) := by
        dsimp [B]
        rw [dite_eq_left ⟨hj, hjn⟩]
        exact (ih j hjn hj).choose_spec.2 R hR f g p
          (hf.of_le (by exact_mod_cast hjn.le)) (hg.of_le (by exact_mod_cast hjn.le))
          heq hgap (fun k hk hkj ↦ hprofile k hk (hkj.trans hjn.le))
      have hsum : (∑ s : OrderedFinpartition n with 2 ≤ s.length,
          ‖iteratedFDeriv ℝ s.length f (p, g p)‖ *
            ∏ i, ‖iteratedFDeriv ℝ (s.partSize i) (fun q ↦ (q, g q)) p‖) ≤
          S * R ^ (n - 1) := by
        dsimp only [S]
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro s hs
        have hs2 := (Finset.mem_filter.mp hs).2
        rw [← partition_nat_power_product s (by omega) M R B]
        apply mul_le_mul (hprofile _ (by omega) s.length_le) ?_
          (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) (mul_nonneg hM (pow_nonneg hR _))
        exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦
          hlower _ (s.partSize_pos i) (ODE.partSize_lt_of_two_le_length s hs2 i))
      rw [iteratedFDeriv_rootGraph_high hn2 hg, ContinuousMultilinearMap.opNorm_prod,
        norm_zero, max_eq_right (norm_nonneg _)]
      calc
        _ ≤ _ := norm_iteratedFDeriv_root_le_partition_sum hn2 hc hf hg heq hgap
        _ ≤ (S * R ^ (n - 1)) / c := div_le_div_of_nonneg_right hsum hc.le
        _ ≤ (1 + S / c) * R ^ (n - 1) := by
          rw [mul_div_right_comm]
          exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hR _)

/-- `app:ch_regular_base:lem:buffered-interpolation`: summing the derived root
jets gives a seminorm estimate from a baseline-one profile of the equation.
The constant is fixed before the scale, domains, equation and root. The remaining
analytic input for the buffered-cylinder theorem is the equation's interpolation
profile, not a bound on any derivative of the root. -/
theorem exists_root_cNorm_bound_of_equation_profile {M c G : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hG : 0 ≤ G) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (s U : Set P),
      IsOpen U → s ⊆ U → ∀ (f : P × ℝ → ℝ) (g : P → ℝ),
      (∀ p ∈ s, ContDiffAt ℝ n f (p, g p)) → ContDiffOn ℝ n g U →
      (∀ p ∈ U, f (p, g p) = 0) →
      (∀ p ∈ s, c ≤ |scalarDerivative f (p, g p)|) →
      (∀ p ∈ s, ‖g p‖ ≤ G) →
      (∀ p ∈ s, ∀ j, 1 ≤ j → j ≤ n →
        ‖iteratedFDeriv ℝ j f (p, g p)‖ ≤ M * R ^ (j - 1)) →
      cNorm s n g ≤ C * R ^ (n - 1) := by
  classical
  let B : ℕ → ℝ := fun j ↦ if hj : 1 ≤ j then
    (exists_rootGraph_jet_bound_of_equation_profile (P := P) hM hc j hj).choose else G
  have hB (j : ℕ) : 0 ≤ B j := by
    dsimp [B]
    split_ifs with hj
    · exact zero_le_one.trans
        (exists_rootGraph_jet_bound_of_equation_profile (P := P) hM hc j hj).choose_spec.1
    · exact hG
  let C := 1 + ∑ j ∈ Finset.range (n + 1), B j
  have hC : 0 < C := by
    dsimp [C]
    have := Finset.sum_nonneg (s := Finset.range (n + 1)) (fun j _ ↦ hB j)
    linarith
  refine ⟨C, hC, ?_⟩
  intro R hR s U hU hs f g hf hg heq hgap hval hprofile
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hjet : ∀ j ≤ n, ∀ p ∈ s, ‖iteratedFDeriv ℝ j g p‖ ≤ B j * R ^ (n - 1) := by
    intro j hjn p hp
    by_cases hj : 1 ≤ j
    · have hg' : ContDiffAt ℝ j g p :=
        (hg.contDiffAt (hU.mem_nhds (hs hp))).of_le (by exact_mod_cast hjn)
      have hb : ‖iteratedFDeriv ℝ j (fun q ↦ (q, g q)) p‖ ≤ B j * R ^ (j - 1) := by
        dsimp only [B]
        rw [dite_eq_left hj]
        apply (exists_rootGraph_jet_bound_of_equation_profile hM hc j hj).choose_spec.2
          R hR0 f g p ((hf p hp).of_le (by exact_mod_cast hjn)) hg' _ (hgap p hp)
          (fun k hk hkj ↦ hprofile p hp k hk (hkj.trans hjn))
        filter_upwards [hU.mem_nhds (hs hp)] with q hq
        exact heq q hq
      have hprod := iteratedFDeriv_prodMk contDiffAt_id hg' le_rfl
      simp only [id_eq] at hprod
      have hnorm : ‖iteratedFDeriv ℝ j g p‖ ≤
          ‖iteratedFDeriv ℝ j (fun q ↦ (q, g q)) p‖ := by
        rw [hprod, ContinuousMultilinearMap.opNorm_prod]
        exact le_max_right _ _
      exact (hnorm.trans hb).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hR (by omega : j - 1 ≤ n - 1)) (hB j))
    · have hj0 : j = 0 := by omega
      subst j
      simp only [norm_iteratedFDeriv_zero, B, show ¬ 1 ≤ (0 : ℕ) by omega]
      exact (hval p hp).trans (le_mul_of_one_le_right hG (one_le_pow₀ hR))
  have hb := cNorm_le_sum_of_bounds (s := s) (r := n) (f := g)
    (C := fun j ↦ B j * R ^ (n - 1)) (fun j _ ↦ mul_nonneg (hB j) (pow_nonneg hR0 _)) hjet
  rw [← Finset.sum_mul] at hb
  apply hb.trans
  exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (pow_nonneg hR0 _)

/-- `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase`: the scalar implicit root on the buffered
characteristic cylinder has a one-high seminorm bound, with no derivative loss.
The constant is chosen before both the equation and its root. The equation's
first seminorm and transverse gap are the only derivative budgets assumed;
interpolation and the implicit partition recurrence supply every higher bound.
The consumer is the arbitrary-order section-root estimate in
`HamiltonPhase/SectionJetBounds.lean`. -/
theorem exists_root_cNorm_bound_cylinder_on [FiniteDimensional ℝ P]
    (p₀ : P) (τ₀ : ℝ) {r a c M : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hc : 0 < c) (hM : 0 ≤ M)
    (n : ℕ) {W : Set (P × ℝ)} (hW : IsOpen W)
    (hKW : Metric.closedBall p₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a) ⊆ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : P × ℝ → ℝ) (g : P → ℝ),
      ContDiffOn ℝ ∞ f W → ContDiffOn ℝ ∞ g (Metric.ball p₀ (2 * r)) →
      cNorm (Metric.closedBall p₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)) 1 f ≤ M →
      (∀ p ∈ Metric.ball p₀ (2 * r),
        g p ∈ Icc (τ₀ - a) (τ₀ + a) ∧ f (p, g p) = 0 ∧
          c ≤ |scalarDerivative f (p, g p)|) →
      cNorm (Metric.closedBall p₀ r) n g ≤
        C * (1 + cNorm (Metric.closedBall p₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)) n f) := by
  let K := Metric.closedBall p₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hprofiles : ∃ B : ℝ, 0 ≤ B ∧ ∀ f : P × ℝ → ℝ,
      ContDiffOn ℝ ∞ f W → cNorm K 1 f ≤ M →
      ∃ R : ℝ, 1 ≤ R ∧ R ^ (n - 1) ≤ 1 + cNorm K n f ∧
        ∀ j, 1 ≤ j → j ≤ n → cNorm K j f ≤ B * R ^ (j - 1) := by
    by_cases hn : 2 ≤ n
    · obtain ⟨B, hB, hinterp⟩ := exists_uniform_cNorm_baseline_one_profile_cylinder_on
        p₀ τ₀ hr ha hW hKW hn hM
      refine ⟨B, zero_le_one.trans hB, ?_⟩
      intro f hf hfM
      let H := 1 + cNorm K n f
      have hH : 1 ≤ H := by dsimp [H]; linarith [cNorm_nonneg K n f]
      have hn' : 0 < (n : ℝ) - 1 := by
        have : (2 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      let R := H ^ (1 / ((n : ℝ) - 1))
      have hR : 1 ≤ R := Real.one_le_rpow hH (by positivity)
      have hpow (j : ℕ) (hj : 1 ≤ j) :
          R ^ (j - 1) = H ^ (((j : ℝ) - 1) / ((n : ℝ) - 1)) := by
        dsimp only [R]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hH),
          Nat.cast_sub hj, Nat.cast_one]
        congr 1
        ring
      refine ⟨R, hR, ?_, ?_⟩
      · rw [hpow n (by omega), div_self hn'.ne', Real.rpow_one]
      · intro j hj hjn
        rw [hpow j hj]
        exact hinterp f hf hfM j hj hjn
    · refine ⟨M, hM, ?_⟩
      intro f _ hfM
      refine ⟨1, le_rfl, ?_, ?_⟩
      · simpa only [one_pow] using (show 1 ≤ 1 + cNorm K n f by
          linarith [cNorm_nonneg K n f])
      · intro j _ hjn
        simpa only [one_pow, mul_one] using
          (cNorm_mono_order (s := K) (f := f) (show j ≤ 1 by omega)).trans hfM
  obtain ⟨B, hB, hprofile⟩ := hprofiles
  have hG : 0 ≤ |τ₀| + a := by positivity
  obtain ⟨C, hC, hrootBound⟩ :=
    exists_root_cNorm_bound_of_equation_profile (P := P) hB hc hG n
  refine ⟨C, hC, ?_⟩
  intro f g hf hg hfM hroot
  obtain ⟨R, hR, hhigh, hjet⟩ := hprofile f hf hfM
  have hsub : Metric.closedBall p₀ r ⊆ Metric.ball p₀ (2 * r) :=
    Metric.closedBall_subset_ball (by linarith)
  have hgraph (p : P) (hp : p ∈ Metric.closedBall p₀ r) : (p, g p) ∈ K :=
    ⟨Metric.ball_subset_closedBall (hsub hp), (hroot p (hsub hp)).1⟩
  have hfAt (j : ℕ) : ∀ x ∈ K, ContDiffAt ℝ j f x := by
    intro x hx
    exact (hf.contDiffAt (hW.mem_nhds (hKW hx))).of_le (by simp)
  have hb : cNorm (Metric.closedBall p₀ r) n g ≤ C * R ^ (n - 1) := by
    apply hrootBound R hR (Metric.closedBall p₀ r) (Metric.ball p₀ (2 * r))
      Metric.isOpen_ball hsub f g (fun p hp ↦ hfAt n _ (hgraph p hp))
      (hg.of_le (by simp)) (fun p hp ↦ (hroot p hp).2.1)
      (fun p hp ↦ (hroot p (hsub hp)).2.2)
    · intro p hp
      rw [Real.norm_eq_abs]
      have ht := (hroot p (hsub hp)).1
      exact abs_le.mpr ⟨by linarith [neg_abs_le τ₀, ht.1],
        by linarith [le_abs_self τ₀, ht.2]⟩
    · intro p hp j hj hjn
      exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK (hfAt j)
        (hgraph p hp) le_rfl).trans (hjet j hj hjn)
  exact hb.trans (mul_le_mul_of_nonneg_left hhigh hC.le)

end JanetCartan.CharacteristicRoot
