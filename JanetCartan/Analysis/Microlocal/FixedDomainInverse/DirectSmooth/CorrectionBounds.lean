module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.Correction
public import JanetCartan.Analysis.Sobolev.Local.Cutoff
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Real
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.PdoRestriction

/-!
# Tame bounds for the same corrected source and physical solver

The source cutoff preserves the original additive tame estimate of the fixed
inverse. A supported corrected source then admits the physical solver's
restriction estimate, without replacing either operator or assuming a positive
order bound for arbitrary zero extension. `DirectSmooth` applies both deductions
to its actual protected constructor and its same Neumann correction.

Consumers: the fixed response and its joint parameter regularity, for
`app:ch_regular:thm:exact-correction` and `app:ch_regular:eq:inverse-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff NNReal ENNReal JanetCartan.RegularSector.Realization
namespace JanetCartan.FixedDomainInverse
open LocalSobolev SmallSupport RegularSector.Realization RegularSector.FiniteAssembly
open RegularSector.Characteristic.RetardedLocalization FourierIntegral.LowBounds Pseudodifferential
open ArbitraryAccuracy.ResidualLocalization CharacteristicTransport.CompleteResidual

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- A fixed source cutoff preserves the inverse's additive high coefficient
term (`app:ch_regular:eq:inverse-tame`). The constants depend only on the
cutoff and order and precede all coefficients and sources. The actual inverse
estimate is supplied by `exists_finite_direct_fixed_inverse`; this deduction
does not construct a second inverse. -/
theorem exists_sourceCut_composition_tame_constants
    {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {x : Euclidean n} (χ : ContDiffBump x) :
    ∃ D : ℕ → ℝ, (∀ s, 1 ≤ D s) ∧
      ∀ (W : Set (Euclidean n)) (_hW : MeasurableSet W),
      tsupport (χ : Euclidean n → ℝ) ⊆ W →
      ∀ (S : LocalL2 W F →L[ℝ] LocalL2 W F) (C a : ℕ → ℝ) (b : ℕ),
      (∀ s, 0 ≤ C s) → (∀ s, 0 ≤ a s) →
      (∀ s u, MemRestrictionSobolev W s u →
        MemRestrictionSobolev W s (S u) ∧
          restrictionSobolevNorm W s (S u) ≤ C s *
            (restrictionSobolevNorm W s u + (1 + a (s + b)) * ‖u‖)) →
      ∀ s u, MemRestrictionSobolev W s u →
        MemRestrictionSobolev W s (S (bumpL2 (p := 2) le_rfl χ u)) ∧
          restrictionSobolevNorm W s (S (bumpL2 (p := 2) le_rfl χ u)) ≤
            (D s * C s) * (restrictionSobolevNorm W s u + (1 + a (s + b)) * ‖u‖) := by
  choose D hD hcut using fun s ↦ exists_bumpL2_sobolev_bound (F := F) χ s
  refine ⟨D, hD, ?_⟩
  intro W hW hs S C a b hC ha hS s u hu
  obtain ⟨hm, hn⟩ := hcut s W hW hs u hu
  obtain ⟨hSm, hSn⟩ := hS s _ hm
  have hlow : ‖bumpL2 (p := 2) le_rfl χ u‖ ≤ ‖u‖ := by
    simpa only [one_mul] using
      (bumpL2 (F := F) (μ := volume.restrict W) (p := 2) le_rfl χ).le_of_opNorm_le
        (norm_bumpL2_two_le_one (F := F) (μ := volume.restrict W) χ) u
  have hhigh : 0 ≤ 1 + a (s + b) := add_nonneg zero_le_one (ha _)
  refine ⟨hSm, hSn.trans ?_⟩
  calc
    _ ≤ C s * (D s * restrictionSobolevNorm W s u + (1 + a (s + b)) * ‖u‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hn (mul_le_mul_of_nonneg_left hlow hhigh)) (hC s)
    _ ≤ C s * (D s * restrictionSobolevNorm W s u +
        D s * ((1 + a (s + b)) * ‖u‖)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (le_mul_of_one_le_left (mul_nonneg hhigh (norm_nonneg u)) (hD s))) (hC s)
    _ = _ := by ring

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "RF" => EuclideanSpace ℝ (Fin q)
local notation "CF" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp CF 2 (volume : Measure E)

/-- The original Fourier bound gives a restriction bound for the SAME real
physical solver on a source fixed by its existing support cutoff
(`app:ch_regular_base:eq:sector-theorem-solution`). The correction constructor
supplies this cutoff identity. No replacement measurement mask is introduced,
and the output may be measured on any domain. -/
theorem exists_supported_real_solver_restriction_constants
    {x : E} (χ : ContDiffBump x) :
    ∃ D : ℕ → ℝ, (∀ s, 1 ≤ D s) ∧
      ∀ (T : H →L[ℂ] H) (s : ℕ) (A high : ℝ), 0 ≤ A → 0 ≤ high →
      (∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (T u) ∧
          vectorFourierSobolevNorm (s : ℝ) (T u) ≤
            A * (vectorFourierSobolevNorm (s : ℝ) u + high * ‖u‖)) →
      ∀ (W V : Set E) (hW : MeasurableSet W), tsupport (χ : E → ℝ) ⊆ W →
      ∀ u : LocalL2 W RF, MemRestrictionSobolev W s u →
      bumpL2 (p := 2) le_rfl χ u = u →
        MemRestrictionSobolev V s
          (localRealCompression hW V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) u) ∧
        restrictionSobolevNorm V s
          (localRealCompression hW V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) u) ≤
            (D s * A) * (restrictionSobolevNorm W s u + high * ‖u‖) := by
  choose Ci hCi hin using fun s ↦ exists_sourceCut_zeroExtension_fourier_bound
    (q := q) χ χ.contDiff χ.hasCompactSupport (bump_norm_le_one χ) s
  choose Cr hCr hout using fun s ↦ vector_restrictionSobolev_nat_bounds (d + 1) q s
  refine ⟨fun s ↦ 8 * ((1 + Cr s) * Ci s), fun s ↦ ?_, ?_⟩
  · have hprod : 1 ≤ (1 + Cr s) * Ci s :=
      one_le_mul_of_one_le_of_one_le (by linarith [hCr s]) (hCi s)
    linarith
  intro T s A high hA hhigh hT W V hW hs u hu hfixed
  let cut : H →L[ℂ] H := sourceCutMultiplier χ χ.continuous (bump_norm_le_one χ)
  let S := T.comp cut
  have hS (v : LocalL2 W CF) (hv : MemRestrictionSobolev W s v) :
      MemRestrictionSobolev V s (localRetardedOperator hW V S v) ∧
        restrictionSobolevNorm V s (localRetardedOperator hW V S v) ≤
          (((1 + Cr s) * Ci s) * A) * (restrictionSobolevNorm W s v + high * ‖v‖) := by
    let z := cut (zeroExtend hW v)
    obtain ⟨hz, hnz⟩ := hin s W hW hs v hv
    have hlz : ‖z‖ ≤ ‖v‖ :=
      norm_sourceCutMultiplier_zeroExtend_le hW χ χ.continuous (bump_norm_le_one χ) v
    obtain ⟨ht, hnt⟩ := hT z hz
    obtain ⟨hm, hn⟩ := hout s (T z) ht V (localRetardedOperator hW V S v)
      (restrictL2_coeFn V _).symm
    refine ⟨hm, hn.trans ((mul_le_mul_of_nonneg_left hnt (hCr s).le).trans ?_)⟩
    have hlow : high * ‖z‖ ≤ Ci s * (high * ‖v‖) :=
      (mul_le_mul_of_nonneg_left hlz hhigh).trans
        (le_mul_of_one_le_left (mul_nonneg hhigh (norm_nonneg v)) (hCi s))
    calc
      _ ≤ Cr s * (A * (Ci s * restrictionSobolevNorm W s v + Ci s * (high * ‖v‖))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (add_le_add hnz hlow) hA) (hCr s).le
      _ = (Cr s * Ci s * A) * (restrictionSobolevNorm W s v + high * ‖v‖) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _
          (add_nonneg restrictionSobolevNorm_nonneg (mul_nonneg hhigh (norm_nonneg v)))
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans (hCi s))) hA
  have hreal := localRealCompression_physicalPair_restriction_tame_bound hW S s s
    (((1 + Cr s) * Ci s) * A) high
    (mul_nonneg (mul_nonneg (by linarith [hCr s]) (zero_le_one.trans (hCi s))) hA)
    hhigh hS u hu
  have hi : bumpL2 (p := 2) le_rfl χ (l2ComplexInclusion (volume.restrict W) u) =
      l2ComplexInclusion (volume.restrict W) u := by
    apply Lp.ext
    have hfu := bumpL2_coeFn (p := 2) le_rfl χ u
    rw [hfixed] at hfu
    filter_upwards [bumpL2_coeFn (p := 2) le_rfl χ
      (l2ComplexInclusion (volume.restrict W) u),
      euclideanComplexInclusion.coeFn_compLpL u, hfu] with y hy hiy hfy
    have hiy' : l2ComplexInclusion (volume.restrict W) u y =
        euclideanComplexInclusion (u y) := hiy
    rw [hy, hiy', ← map_smul, ← hfy]
  have he : localRealCompression hW V (physicalPairedSectorSum {()} (fun _ : Unit ↦ S)) u =
      localRealCompression hW V (physicalPairedSectorSum {()} (fun _ : Unit ↦ T)) u := by
    rw [localRealCompression_physicalPair, localRealCompression_physicalPair]
    congr 1
    change l2RealPart (volume.restrict V)
      (restrictL2 V (T (cut (zeroExtend hW (l2ComplexInclusion (volume.restrict W) u))))) = _
    dsimp only [cut]
    rw [sourceCutMultiplier_zeroExtend_bump, hi]
    rfl
  rw [he] at hreal
  simpa only [mul_assoc] using hreal

end JanetCartan.FixedDomainInverse
