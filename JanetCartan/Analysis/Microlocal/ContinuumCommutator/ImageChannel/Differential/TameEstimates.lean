module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.WeightedEstimates

/-!
# Tame higher commutators of the actual image normal

The constructed `imageNormalCommutator` obeys the single-high estimate in
`app:ch_background:eq:bg-commutator`, from primitive coefficient jets.
The source and measurement masks precede the constants and remain literal
factors in every identity. The low coefficient order is one. The geometric
producer's reserve is two, giving high map order `s+3` for an `s+1` derivative
commutator. No normal representation or commutator estimate is assumed.

`exists_imageNormal_tame_commutators` supplies the exact weak identity and
quantitative input to the elliptic parent's generic higher regularity proof.
The parent retains instantiation of the primitive jets on its same row and
construction of its first-order inverse from the separate translation theorem.
-/

public noncomputable section

open scoped BigOperators
namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential
open PeriodicSobolevSpace ContinuumRow ImageFactorExpression

private theorem jetOrderLe_imageForwardExpression (n : ℕ) :
    (imageForwardExpression n).jetOrderLe 0 := by
  simp [imageForwardExpression, jetOrderLe]

private theorem jetOrderLe_imageAdjointExpression (n : ℕ) :
    (imageAdjointExpression n).jetOrderLe 0 := by
  simp [imageAdjointExpression, jetOrderLe]

private theorem global_jet_le_cNorm {n : ℕ} (q : C(Torus n, ℝ))
    (hq : IsSmoothPeriodic q) {j m : ℕ} (hjm : j ≤ m) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ j (periodicLift q) x‖ ≤
      cNorm (fundamentalCell n) m (periodicLift q) := by
  apply norm_iteratedFDeriv_periodicLift_le q j _ x
  intro y hy
  exact norm_iteratedFDeriv_le_cNorm (isCompact_fundamentalCell n)
    (hq.2.of_le (by simp)) hy hjm

/-- The fixed masks are chosen before the tame constant. The constructed
commutator of the literal image normal has a single high coefficient budget
(`app:ch_background:eq:bg-commutator`). The low coefficient order is one,
the high coefficient order is `s+1`, and neither depends on accuracy. -/
theorem exists_imageNormal_commutator_bound {n : ℕ}
    (χmeas χsrc : C(Torus n, ℝ)) (hχmeas : IsSmoothPeriodic χmeas)
    (hχsrc : IsSmoothPeriodic χsrc) (s : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (hc : ∀ a, IsSmoothPeriodic (c a)) (H : ℝ), 0 ≤ H →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ M) →
      (∀ a j, j ≤ s+1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ H) →
      ∀ (is : List (Fin n)) (hlen : is.length ≤ s+1)
        (u : PeriodicSobolevSpace n (Euclidean n) s),
      ‖imageNormalCommutator c hc χmeas χsrc hχmeas hχsrc s is hlen u‖ ≤
        C * (‖u‖ + (1+H) * ‖toL2 s u‖) := by
  let L := cNorm (fundamentalCell n) 1 (periodicLift χmeas) +
    cNorm (fundamentalCell n) 1 (periodicLift χsrc)
  let Q := cNorm (fundamentalCell n) (s+1) (periodicLift χmeas) +
    cNorm (fundamentalCell n) (s+1) (periodicLift χsrc)
  have hL : 0 ≤ L := add_nonneg (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _)
  have hQ : 0 ≤ Q := add_nonneg (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _)
  let e := ImageFactorExpression.comp (imageForwardExpression n) (imageAdjointExpression n)
  have he : e.jetOrderLe 0 :=
    ⟨jetOrderLe_imageForwardExpression n, jetOrderLe_imageAdjointExpression n⟩
  obtain ⟨C, hC, hbound⟩ := e.exists_primitive_commutator_bound he s (add_nonneg hM hL)
  refine ⟨C * (1+Q), by positivity, ?_⟩
  intro c hc H hH hlow hhigh is hlen u
  have hlow' : ∀ a j, j ≤ 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (periodicLift (imageFactorCoefficients c χmeas χsrc a)) x‖ ≤ M+L := by
    intro a j hj x
    rcases a with a | b
    · exact (hlow a j hj x).trans (le_add_of_nonneg_right hL)
    · cases b
      · apply (global_jet_le_cNorm χmeas hχmeas hj x).trans
        dsimp [L]
        linarith [cNorm_nonneg (fundamentalCell n) 1 (periodicLift χsrc)]
      · apply (global_jet_le_cNorm χsrc hχsrc hj x).trans
        dsimp [L]
        linarith [cNorm_nonneg (fundamentalCell n) 1 (periodicLift χmeas)]
  have hhigh' : ∀ a j, j ≤ s+1 → ∀ x,
      ‖iteratedFDeriv ℝ j (periodicLift (imageFactorCoefficients c χmeas χsrc a)) x‖ ≤ H+Q := by
    intro a j hj x
    rcases a with a | b
    · exact (hhigh a j hj x).trans (le_add_of_nonneg_right hQ)
    · cases b
      · apply (global_jet_le_cNorm χmeas hχmeas hj x).trans
        dsimp [Q]
        linarith [cNorm_nonneg (fundamentalCell n) (s+1) (periodicLift χsrc)]
      · apply (global_jet_le_cNorm χsrc hχsrc hj x).trans
        dsimp [Q]
        linarith [cNorm_nonneg (fundamentalCell n) (s+1) (periodicLift χmeas)]
  have hout := hbound (imageFactorCoefficients c χmeas χsrc)
    (smooth_imageFactorCoefficients c hc χmeas χsrc hχmeas hχsrc)
    (H+Q) (add_nonneg hH hQ) hlow' hhigh' is hlen u
  change ‖imageNormalCommutator c hc χmeas χsrc hχmeas hχsrc s is hlen u‖ ≤ _ at hout
  apply hout.trans
  have hscale : ‖u‖ + (1+(H+Q)) * ‖toL2 s u‖ ≤
      (1+Q) * (‖u‖ + (1+H) * ‖toL2 s u‖) := by
    nlinarith [mul_nonneg hQ (norm_nonneg u),
      mul_nonneg (mul_nonneg hQ hH) (norm_nonneg (toL2 s u))]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale hC.le


/-- `app:ch_background:eq:bg-commutator` with the fixed reserve of the actual
geometric coefficient producer. `ImageGeometry.exists_reference_imageChannel`
and `HistoryImage.exists_imageChannel` supply the primitive jets
`P m * (1 + H (m+2))` for their SAME coefficients. The fixed low coefficient
order is one and the fixed map shift is two: the high map norm is `H (s+3)`.
The elliptic parent must instantiate these primitive budgets on that row;
no normal bound, Sobolev action, or commutator estimate is an input here.
The constants precede every varying coefficient and profile. -/
theorem exists_imageNormal_commutator_profile {n : ℕ}
    (χmeas χsrc : C(Torus n, ℝ)) (hχmeas : IsSmoothPeriodic χmeas)
    (hχsrc : IsSmoothPeriodic χsrc) {M : ℝ} (hM : 0 ≤ M)
    (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) :
    ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (hc : ∀ a, IsSmoothPeriodic (c a)) (H : ℕ → ℝ),
      (∀ m, 0 ≤ H m) → Monotone H →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ M) →
      (∀ a j x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
        P j * (1 + H (j+2))) →
      ∀ (s : ℕ) (is : List (Fin n)) (hlen : is.length ≤ s+1)
        (u : PeriodicSobolevSpace n (Euclidean n) s),
      ‖imageNormalCommutator c hc χmeas χsrc hχmeas hχsrc s is hlen u‖ ≤
        C s * (‖u‖ + (1+H (s+3)) * ‖toL2 s u‖) := by
  have hb (s : ℕ) := exists_imageNormal_commutator_bound χmeas χsrc hχmeas hχsrc s hM
  choose C hC hbound using hb
  let Q (s : ℕ) := ∑ j ∈ Finset.range (s+2), P j
  have hQ (s : ℕ) : 0 ≤ Q s := Finset.sum_nonneg fun j _ ↦ hP j
  refine ⟨fun s ↦ C s * (1+Q s), fun s ↦ mul_pos (hC s) (add_pos_of_pos_of_nonneg zero_lt_one (hQ s)), ?_⟩
  intro c hc H hH hmono hlow hhigh s is hlen u
  have hQs := hQ s
  have hHs := hH (s+3)
  have hjets : ∀ a j, j ≤ s+1 → ∀ x,
      ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ Q s * (1+H (s+3)) := by
    intro a j hj x
    apply (hhigh a j x).trans
    apply mul_le_mul
    · exact Finset.single_le_sum (fun k _ ↦ hP k) (Finset.mem_range.mpr (by omega))
    · exact add_le_add (le_refl 1) (hmono (show j+2 ≤ s+3 by omega))
    · exact add_nonneg zero_le_one (hH (j+2))
    · exact hQ s
  have hout := hbound s c hc (Q s * (1+H (s+3))) (by positivity) hlow hjets is hlen u
  apply hout.trans
  have hscale : ‖u‖ + (1 + Q s * (1+H (s+3))) * ‖toL2 s u‖ ≤
      (1+Q s) * (‖u‖ + (1+H (s+3)) * ‖toL2 s u‖) := by
    nlinarith [mul_nonneg (hQ s) (norm_nonneg u),
      mul_nonneg (hH (s+3)) (norm_nonneg (toL2 s u))]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale (hC s).le


/-- The exact `K/hK` interface for `HigherRegularity.mem_succ_of_commutators`
and `HigherRegularity.gradeNorm_succ_le_of_commutators`, together with its
proved tame bound (`app:ch_background:eq:bg-commutator`,
`app:ch_background:prop:bg-inverse`). The normal is literally `A.comp A.adjoint`
for the published image channel, with both unchanged masks. All additional
hypotheses are primitive coefficient jets, supplied by the same row's geometric
producer; the high map order is `s+1+B` with the fixed shift `B=2`. -/
theorem exists_imageNormal_tame_commutators {n : ℕ}
    (χmeas χsrc : C(Torus n, ℝ)) (hχmeas : IsSmoothPeriodic χmeas)
    (hχsrc : IsSmoothPeriodic χsrc) {M : ℝ} (hM : 0 ≤ M)
    (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) :
    ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (_hc : ∀ a, IsSmoothPeriodic (c a)) (H : ℕ → ℝ),
      (∀ m, 0 ≤ H m) → Monotone H →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ M) →
      (∀ a j x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
        P j * (1 + H (j+2))) →
      ∀ s : ℕ, ∃ K : (is : List (Fin n)) → is.length = s+1 →
          PeriodicSobolevSpace n (Euclidean n) s →L[ℝ] OutputL2 n,
      (∀ (is : List (Fin n)) (hlen : is.length = s+1)
          (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f),
        HasPeriodicWeakDerivativeList is
          ((imageChannel c χmeas χsrc ∘L (imageChannel c χmeas χsrc).adjoint)
            (toL2 s (ofSmooth s f hf)))
          ((imageChannel c χmeas χsrc ∘L (imageChannel c χmeas χsrc).adjoint)
            (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f) (hf.coordinateDerivList is))) +
              K is hlen (ofSmooth s f hf))) ∧
      (∀ (is : List (Fin n)) (hlen : is.length = s+1)
          (u : PeriodicSobolevSpace n (Euclidean n) s),
        ‖K is hlen u‖ ≤ C s * (‖u‖ + (1+H (s+3)) * ‖toL2 s u‖)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_imageNormal_commutator_profile χmeas χsrc hχmeas hχsrc hM P hP
  refine ⟨C, hC, ?_⟩
  intro c hc H hH hmono hlow hhigh s
  refine ⟨fun is hlen ↦ imageNormalCommutator c hc χmeas χsrc hχmeas hχsrc s is hlen.le, ?_, ?_⟩
  · intro is hlen f hf
    exact hasWeakDerivativeList_imageNormalCommutator c hc χmeas χsrc hχmeas hχsrc
      s is hlen.le f hf
  · intro is hlen u
    exact hbound c hc H hH hmono hlow hhigh s is hlen.le u

end JanetCartan.ContinuumCommutator.ImageChannel.Differential
