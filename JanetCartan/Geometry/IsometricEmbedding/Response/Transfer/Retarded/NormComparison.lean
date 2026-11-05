module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.NormComparison.MeasuredJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.NormComparison.CoordinateJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.NormComparison.SymmetricTensors

/-!
# Comparison with the actual restriction Sobolev scale

The whole-chart grade is identified with the classical Fréchet jet norm for
`app:ch_response:eq:fixed-factor-transfer`. Integrating the ordered mixed-jet
evaluations proves both comparisons with constants independent of the test
field. These are the norm adapters for `exists_demodulated_jet_norm_bounds`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.ResponseTransfer

open RetardedSobolev.Spaces LocalSobolev

/-- The actual completed retarded norm is bounded by the whole-chart local
Sobolev grade with constant one (`app:ch_osc:prop:osc-retarded-tube`). This is
the input-side comparison for `app:ch_response:eq:fixed-factor-transfer`. -/
theorem ofTest_norm_le_retardedTestToLocalL2_gradeNorm {d : ℕ} (s : ℕ) (f : Test d) :
    ‖ofTest s volume f‖ ≤
      (restrictionSobolevScale (univ : Set (Euclidean (d + 1))) ℂ
        MeasurableSet.univ).gradeNorm s (retardedTestToLocalL2 f) := by
  rw [retardedTestToLocalL2_gradeNorm_eq_jetL2Norm]
  apply (ofTest_norm_le_iff_retardedJet_l2Norm_le f (jetL2Norm_nonneg _ _ _)).mpr
  intro i
  have hJ := memLp_iteratedFDeriv_of_contDiff_hasCompactSupport
    (contDiff_retardedTestFunction f) (hasCompactSupport_retardedTestFunction f)
    (retardedJetOrder i)
  calc
    _ ≤ (eLpNorm (iteratedFDeriv ℝ (retardedJetOrder i)
        (retardedTestFunction f)) 2 volume).toReal := by
      apply ENNReal.toReal_mono hJ.eLpNorm_ne_top
      apply eLpNorm_mono (memLp_retardedJet_comp_coordinates f i).aestronglyMeasurable
      intro x
      rw [Function.comp_apply, Function.comp_apply,
        ← retardedJetEvaluation_iteratedFDeriv f i x]
      exact norm_retardedJetEvaluation_le _ i
    _ ≤ _ := by
      simp only [jetL2Norm, Measure.restrict_univ]
      exact Finset.single_le_sum
        (f := fun j ↦ (eLpNorm (iteratedFDeriv ℝ j (retardedTestFunction f)) 2 volume).toReal)
        (fun _ _ ↦ ENNReal.toReal_nonneg)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (retardedJetOrder_le i)))

/-- Integrating the symmetric tensor bound controls every Euclidean jet by
the completed retarded norm, with ordered multiplicities retained. This is
the L² step of `app:ch_osc:prop:osc-retarded-tube`, consumed by the reverse
whole-chart grade comparison below. -/
private theorem exists_retardedTest_iteratedFDeriv_l2Norm_bound (d s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Test d) (j : ℕ), j ≤ s →
      (eLpNorm (iteratedFDeriv ℝ j (retardedTestFunction f)) 2 volume).toReal ≤
        C * ‖ofTest s volume f‖ := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_norm_le_sum_retardedJetEvaluation_of_symmetric d s
  refine ⟨C * Fintype.card (JetIndex d s), mul_nonneg hC (by positivity), ?_⟩
  intro f j hj
  let g : JetIndex d s → Euclidean (d + 1) → ℂ :=
    fun i ↦ jet i f ∘ (Prod.swap ∘ retardedCoordinates d)
  have hg (i : JetIndex d s) : MemLp (g i) 2 volume :=
    memLp_retardedJet_comp_coordinates f i
  let H : Euclidean (d + 1) → ℝ := ∑ i : JetIndex d s, fun x ↦ ‖g i x‖
  have hH : MemLp H 2 volume := by
    convert memLp_finsetSum Finset.univ (fun i _ ↦ (hg i).norm) using 1
    funext x
    simp only [H, Finset.sum_apply]
  have hJ := memLp_iteratedFDeriv_of_contDiff_hasCompactSupport
    (contDiff_retardedTestFunction f) (hasCompactSupport_retardedTestFunction f) j
  have hpoint (x : Euclidean (d + 1)) :
      ‖iteratedFDeriv ℝ j (retardedTestFunction f) x‖ ≤ C * H x := by
    have h := hbound (fun k ↦ iteratedFDeriv ℝ k (retardedTestFunction f) x)
      (fun k _ v σ ↦ by
        simpa only [iteratedFDerivWithin_univ] using
          BallExtension.iteratedFDerivWithin_comp_perm_of_contDiffOn isOpen_univ
            (contDiff_retardedTestFunction f).contDiffOn (mem_univ x) k v σ) j hj
    simpa only [retardedJetEvaluation_iteratedFDeriv, H, g, Finset.sum_apply,
      Function.comp_apply] using h
  have hsum : (eLpNorm H 2 volume).toReal ≤
      ∑ i : JetIndex d s, (eLpNorm (g i) 2 volume).toReal := by
    have hfinite : (∑ i : JetIndex d s, eLpNorm (fun x ↦ ‖g i x‖) 2 volume) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun i _ ↦ (hg i).norm.eLpNorm_ne_top)
    calc
      _ ≤ (∑ i : JetIndex d s, eLpNorm (fun x ↦ ‖g i x‖) 2 volume).toReal :=
        ENNReal.toReal_mono hfinite (eLpNorm_sum_le (by norm_num))
      _ = _ := by
        rw [ENNReal.toReal_sum (fun i _ ↦ (hg i).norm.eLpNorm_ne_top)]
        simp_rw [eLpNorm_norm _ (hg _).aestronglyMeasurable]
  calc
    _ ≤ (eLpNorm (C • H) 2 volume).toReal := by
      apply ENNReal.toReal_mono (hH.const_smul C).eLpNorm_ne_top
      exact eLpNorm_mono_real hJ.aestronglyMeasurable hpoint
    _ = C * (eLpNorm H 2 volume).toReal := by
      rw [eLpNorm_const_smul, ENNReal.toReal_mul]
      simp [Real.norm_eq_abs, abs_of_nonneg hC]
    _ ≤ C * ∑ i : JetIndex d s, (eLpNorm (g i) 2 volume).toReal :=
      mul_le_mul_of_nonneg_left hsum hC
    _ ≤ C * ∑ _i : JetIndex d s, ‖ofTest s volume f‖ := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum (fun i _ ↦ retardedJet_l2Norm_le_ofTest f i)
    _ = _ := by simp [mul_assoc]

/-- The local Sobolev grade is bounded by a finite, nonnegative multiple of
the completed retarded norm. The constant precedes the input field and depends
only on dimension and grade. This is the output-side norm adapter from
`app:ch_osc:prop:osc-retarded-tube` to
`app:ch_response:eq:fixed-factor-transfer`. -/
theorem exists_retardedTestToLocalL2_gradeNorm_le_mul_ofTest_norm (d s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Test d,
      (restrictionSobolevScale (univ : Set (Euclidean (d + 1))) ℂ
        MeasurableSet.univ).gradeNorm s (retardedTestToLocalL2 f) ≤
          C * ‖ofTest s volume f‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_retardedTest_iteratedFDeriv_l2Norm_bound d s
  refine ⟨(s + 1) * C, mul_nonneg (by positivity) hC, fun f ↦ ?_⟩
  rw [retardedTestToLocalL2_gradeNorm_eq_jetL2Norm]
  simp only [jetL2Norm, Measure.restrict_univ]
  calc
    _ ≤ ∑ _j ∈ Finset.range (s + 1), C * ‖ofTest s volume f‖ :=
      Finset.sum_le_sum (fun j hj ↦ hbound f j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    _ = _ := by simp [mul_assoc]

/-- Input-independent two-sided comparison of the actual completed retarded
norm and the actual local restriction Sobolev grade. It applies to every
dimension and grade, including `d = 0` and `s = 0`, with no assumed profile
bound or comparison. This supplies both norm adapters for the parent's
`HasEnvelopeProfile` assembly in `app:ch_response:eq:fixed-factor-transfer`. -/
theorem exists_retarded_norm_comparison (d s : ℕ) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ f : Test d,
      ‖ofTest s volume f‖ ≤ C₁ *
        (restrictionSobolevScale (univ : Set (Euclidean (d + 1))) ℂ
          MeasurableSet.univ).gradeNorm s (retardedTestToLocalL2 f) ∧
      (restrictionSobolevScale (univ : Set (Euclidean (d + 1))) ℂ
        MeasurableSet.univ).gradeNorm s (retardedTestToLocalL2 f) ≤
          C₂ * ‖ofTest s volume f‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_retardedTestToLocalL2_gradeNorm_le_mul_ofTest_norm d s
  refine ⟨1, C, zero_le_one, hC, fun f ↦ ⟨?_, hbound f⟩⟩
  simpa only [one_mul] using ofTest_norm_le_retardedTestToLocalL2_gradeNorm s f

end JanetCartan.ResponseTransfer
