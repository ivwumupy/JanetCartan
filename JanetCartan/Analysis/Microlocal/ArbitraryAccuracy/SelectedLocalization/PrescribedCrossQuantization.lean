module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.CrossRestriction

/-!
# Cross quantization for the supplied terminal-protected masks

Apply the primitive cross-quantization bound to the exact input/output symbols.
Their support, derivative profile and closed plateau are direct outputs of the
terminal-protection construction. Both literal orientations are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FourierIntegral.LowBounds Pseudodifferential FiniteChain.Graph
open RegularSector.FiniteMasks.ActualFamily RegularSector.Characteristic
open LocalSobolev RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.RetardedLocalization ResidualLocalization
variable {d : ℕ}
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- The exact prescribed pair supplies cross quantization in both literal
orientations. Constants precede the masks. Its primitive support, jet and
closed-plateau inputs are supplied by the original terminal mask producer
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_prescribed_cross_quantization_fourier_constants
    (b Rbase : ℝ) (Hmask : ℕ → ℝ) (hHmask : ∀ k, 0 ≤ Hmask k)
    {buffer : ℝ} (hbuffer : 0 < buffer) :
    ∃ C : ℕ → ℕ → ℝ, (∀ order N, 0 ≤ C order N) ∧
      ∀ mi mo : LocalizerSymbol (d+1),
      ContDiff ℝ ∞ mi → HasCompactSupport mi →
      ContDiff ℝ ∞ mo → HasCompactSupport mo →
      tsupport mi ⊆ closedBall (0 : E) Rbase ×ˢ closedBall (0 : E) b →
      (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Hmask k) →
      (∀ k p, ‖iteratedFDeriv ℝ k mo p‖ ≤ Hmask k) →
      (∀ p ∈ tsupport mi, closedBall p buffer ⊆ interior {z | mo z = 1}) →
      ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ → ∀ Li Ro : H →L[ℂ] H,
      (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Li u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (leftLocalizer ρ mi (fun z ↦ (u z).ofLp) y)) →
      (∀ u, Ro u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (rightLocalizer ρ mo (fun z ↦ (u z).ofLp) y)) →
      ∀ (order N : ℕ) (backward : Bool) (u : H),
        let S := (1 - Ro).comp Li
        MemVectorFourierSobolev (order : ℝ) ((if backward then S.adjoint else S) u) ∧
        vectorFourierSobolevNorm (order : ℝ) ((if backward then S.adjoint else S) u) ≤
          C order N * ρ ^ order * L ^ (order + (d+1+1)) * (L/ρ)^N * ‖u‖ := by
  obtain ⟨C, hC, hcross⟩ :=
    FiniteChains.CrossQuantization.exists_crossQuantization_twoSided_sobolev_bounds
      (r := d+1) (closedBall (0 : E) Rbase) (isCompact_closedBall _ _)
      Hmask Hmask hHmask hHmask 0 0 hbuffer (le_max_left 0 b)
  refine ⟨C, hC, ?_⟩
  intro mi mo hmi hmic hmo hmoc hsupp hmiJets hmoJets hlink
    ρ L hL hLρ Li Ro hLi hRo order N backward u S
  have hbase : Prod.fst '' tsupport mi ⊆ closedBall (0 : E) Rbase := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hsupp hp).1
  have hann : ∀ p ∈ tsupport mi, ‖p.2‖ ≤ max 0 b := by
    intro p hp
    have h := (hsupp hp).2
    simp only [mem_closedBall, dist_zero_right] at h
    exact h.trans (le_max_right _ _)
  have hdiag : ∀ p ∈ tsupport mi, ∀ z : E × E,
      dist z p ≤ buffer → mo z = 1 := by
    intro p hp z hz
    exact interior_subset (s := {z | mo z = 1}) (hlink p hp hz)
  have hi (l : ℕ) (p : E × E) :
      ‖iteratedFDeriv ℝ l mi p‖ ≤ Hmask l * L ^ (l+0) :=
    (hmiJets l p).trans (le_mul_of_one_le_right (hHmask l) (one_le_pow₀ hL))
  have ho (l : ℕ) (p : E × E) :
      ‖iteratedFDeriv ℝ l mo p‖ ≤ Hmask l * L ^ (l+0) :=
    (hmoJets l p).trans (le_mul_of_one_le_right (hHmask l) (one_le_pow₀ hL))
  have h := hcross mi mo hmi hmic hmo hmoc hbase hann hdiag
    ρ L hL hLρ hi ho Li Ro hLi hRo order N u
  cases backward
  · simpa only [Bool.false_eq_true, ite_false, Nat.zero_add, Nat.add_zero] using h.1
  · simpa only [ite_true, Nat.zero_add, Nat.add_zero] using h.2

/-- Transport the prescribed cross quantization to the whole-space
restriction scale used by the analytic chain. This retains both actual
operators, their literal adjoint and the same mask witnesses
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_prescribed_cross_quantization_restriction_constants
    (b Rbase : ℝ) (Hmask : ℕ → ℝ) (hHmask : ∀ k, 0 ≤ Hmask k)
    {buffer : ℝ} (hbuffer : 0 < buffer) :
    ∃ C : ℕ → ℕ → ℝ, (∀ order N, 0 ≤ C order N) ∧
      ∀ mi mo : LocalizerSymbol (d+1),
      ContDiff ℝ ∞ mi → HasCompactSupport mi →
      ContDiff ℝ ∞ mo → HasCompactSupport mo →
      tsupport mi ⊆ closedBall (0 : E) Rbase ×ˢ closedBall (0 : E) b →
      (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Hmask k) →
      (∀ k p, ‖iteratedFDeriv ℝ k mo p‖ ≤ Hmask k) →
      (∀ p ∈ tsupport mi, closedBall p buffer ⊆ interior {z | mo z = 1}) →
      ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ → ∀ Li Ro : H →L[ℂ] H,
      (∀ u, (∀ i, Integrable (fun y ↦ u y i)) → Li u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (leftLocalizer ρ mi (fun z ↦ (u z).ofLp) y)) →
      (∀ u, Ro u =ᵐ[volume] fun y ↦ WithLp.toLp 2
        (rightLocalizer ρ mo (fun z ↦ (u z).ofLp) y)) →
      ∀ (order N : ℕ) (backward : Bool)
        (u : LocalL2 (univ : Set E) (EuclideanSpace ℂ (Fin (d+1)))),
        let S := (1 - localRetardedOperator MeasurableSet.univ univ Ro).comp
          (localRetardedOperator MeasurableSet.univ univ Li)
        let G := restrictionSobolevScale univ (EuclideanSpace ℂ (Fin (d+1))) MeasurableSet.univ
        ((if backward then S.adjoint else S) u) ∈ G.level order ∧
        G.gradeNorm order ((if backward then S.adjoint else S) u) ≤
          C order N * ρ ^ order * L ^ (order + (d+1+1)) * (L/ρ)^N * ‖u‖ := by
  obtain ⟨C, hC, hcross⟩ := exists_prescribed_cross_quantization_fourier_constants
    b Rbase Hmask hHmask hbuffer
  choose D hD hcompare using fun order ↦ exists_restrictionScale_fourier_comparison
    (d+1) (d+1) order
  refine ⟨fun order N ↦ D order*C order N,
    fun order N ↦ mul_nonneg (hD order).le (hC order N), ?_⟩
  intro mi mo hmi hmic hmo hmoc hsupp hmiJets hmoJets hlink
    ρ L hL hLρ Li Ro hLi hRo order N backward u S G
  have h := hcross mi mo hmi hmic hmo hmoc hsupp hmiJets hmoJets hlink
    ρ L hL hLρ Li Ro hLi hRo order N backward (SmallSupport.zeroExtend MeasurableSet.univ u)
  let radius := max 1 Rbase
  let ψ : ContDiffBump (0 : E) :=
    ⟨radius, radius+1, zero_lt_one.trans_le (le_max_left _ _), by linarith⟩
  have hbase : ∀ y ∈ Prod.fst '' tsupport mi, ψ y = 1 := by
    rintro y ⟨p, hp, rfl⟩
    apply ψ.one_of_mem_closedBall
    exact closedBall_subset_closedBall (le_max_right 1 Rbase) (hsupp hp).1
  have hψb (y : E) : ‖ψ y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (ψ.nonneg (x := y))]
    exact ψ.le_one (x := y)
  have he : S = localRetardedOperator MeasurableSet.univ univ ((1-Ro).comp Li) :=
    local_crossQuantization_eq ρ mi Li Ro hLi univ MeasurableSet.univ
      ψ ψ.continuous hψb (subset_univ _) hbase
  have heo : ((if backward then S.adjoint else S) u) =
      restrictL2 univ ((if backward then ((1-Ro).comp Li).adjoint else (1-Ro).comp Li)
        (SmallSupport.zeroExtend MeasurableSet.univ u)) := by
    cases backward
    · exact congrArg (fun A ↦ A u) he
    · rw [he, localRetardedOperator_adjoint MeasurableSet.univ MeasurableSet.univ]
      rfl
  rw [heo]
  obtain ⟨hm, hn⟩ := hcompare order univ MeasurableSet.univ _ _ h.1
    (restrictL2_coeFn univ _).symm
  refine ⟨hm, hn.trans ?_⟩
  have hb := mul_le_mul_of_nonneg_left h.2 (hD order).le
  simpa only [LinearIsometry.norm_map, mul_assoc] using hb

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
