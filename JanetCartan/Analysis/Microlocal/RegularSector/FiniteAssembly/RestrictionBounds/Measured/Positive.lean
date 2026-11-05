module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Support
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Real

/-!
# Positive restriction estimates for the literal measured operator

Cut off the zero-extended input, apply the constructor's Fourier estimate,
then apply the output mask. The high quantity multiplies only the original
local L² norm (`sector-theorem-residual`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.RegularSector.FiniteAssembly
open LocalSobolev Pseudodifferential FourierIntegral.LowBounds
open Characteristic.RetardedLocalization
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

/-- Fixed measured masks transfer a positive Fourier estimate to the original
restriction spaces, retaining its additive low-data term. This is consumed
at `a=s-1`, `b=s` in `sector-theorem-residual`. The analytic premise is the
positive Fourier output of `Construction.exists_finite_direct_operator_bounds`. -/
theorem exists_measuredOperator_restriction_tame_constant
    (χout χin : E → ℝ) (ho : ContDiff ℝ ∞ χout) (hi : ContDiff ℝ ∞ χin)
    (hoc : HasCompactSupport χout) (hic : HasCompactSupport χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1) (a b : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (T : H →L[ℂ] H) (A high : ℝ), 0 ≤ A → 0 ≤ high →
      (∀ u : H, MemVectorFourierSobolev (a : ℝ) u →
        MemVectorFourierSobolev (b : ℝ) (T u) ∧
          vectorFourierSobolevNorm (b : ℝ) (T u) ≤
            A*(vectorFourierSobolevNorm (a : ℝ) u+high*‖u‖)) →
      ∀ (U V : Set E) (hU : MeasurableSet U), tsupport χin ⊆ U →
      ∀ u : LocalL2 U F, MemRestrictionSobolev U a u →
        MemRestrictionSobolev V b
          (localRetardedOperator hU V (measuredOperator χout χin ho.continuous hi.continuous hob hib T) u) ∧
        restrictionSobolevNorm V b
          (localRetardedOperator hU V (measuredOperator χout χin ho.continuous hi.continuous hob hib T) u) ≤
          (D*A)*(restrictionSobolevNorm U a u+high*‖u‖) := by
  obtain ⟨Ci, hCi, hin⟩ := exists_sourceCut_zeroExtension_fourier_bound (q := q) χin hi hic hib a
  obtain ⟨Co, hCo, hout⟩ := exists_sourceCutMultiplier_fourierSobolev_bound (r := q) χout ho hoc hob b
  obtain ⟨Cr, hCr, hres⟩ := vector_restrictionSobolev_nat_bounds (d+1) q b
  refine ⟨(1+Cr)*(1+Co)*Ci, by
    apply one_le_mul_of_one_le_of_one_le _ hCi
    exact one_le_mul_of_one_le_of_one_le (by linarith) (by linarith), ?_⟩
  intro T A high hA hhigh hT U V hU hs u hu
  let z := sourceCutMultiplier χin hi.continuous hib (SmallSupport.zeroExtend hU u)
  obtain ⟨hz, hnz⟩ := hin U hU hs u hu
  have hlz : ‖z‖ ≤ ‖u‖ := norm_sourceCutMultiplier_zeroExtend_le hU χin hi.continuous hib u
  obtain ⟨ht, hnt⟩ := hT z hz
  obtain ⟨hm, hnm⟩ := hout (T z) ht
  obtain ⟨hr, hnr⟩ := hres _ hm V
    (localRetardedOperator hU V (measuredOperator χout χin ho.continuous hi.continuous hob hib T) u)
    (restrictL2_coeFn V _).symm
  refine ⟨hr, hnr.trans ((mul_le_mul_of_nonneg_left hnm hCr.le).trans
    ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnt hCo) hCr.le).trans ?_))⟩
  have hl : high*‖z‖ ≤ Ci*(high*‖u‖) :=
    (mul_le_mul_of_nonneg_left hlz hhigh).trans
      (le_mul_of_one_le_left (mul_nonneg hhigh (norm_nonneg u)) hCi)
  have hp : Cr*Co ≤ (1+Cr)*(1+Co) := by nlinarith
  calc
    Cr*(Co*(A*(vectorFourierSobolevNorm (a : ℝ) z+high*‖z‖)))
        ≤ Cr*(Co*(A*(Ci*restrictionSobolevNorm U a u+Ci*(high*‖u‖)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add hnz hl) hA) hCo) hCr.le
    _ = (Cr*Co)*((Ci*A)*(restrictionSobolevNorm U a u+high*‖u‖)) := by ring
    _ ≤ ((1+Cr)*(1+Co))*((Ci*A)*(restrictionSobolevNorm U a u+high*‖u‖)) :=
      mul_le_mul_of_nonneg_right hp (mul_nonneg
        (mul_nonneg (zero_le_one.trans hCi) hA)
        (add_nonneg restrictionSobolevNorm_nonneg (mul_nonneg hhigh (norm_nonneg u))))
    _ = _ := by ring

/-- Both literal measured orientations satisfy the exact constructor profile:
input order `s-1` and high quantity `high s`, without an extra order shift.
The parent instantiates T with its SAME selected finite direct residual and
`high s = 1+cNorm K (s-1+sectorLowOrder d) Q+cNorm K (s-1+sectorLowOrder d) B`.
Sources: `measured-adjoint`, `sector-theorem-residual`. -/
theorem exists_measuredOperator_paired_restriction_constants
    (χout χin : E → ℝ) (ho : ContDiff ℝ ∞ χout) (hi : ContDiff ℝ ∞ χin)
    (hoc : HasCompactSupport χout) (hic : HasCompactSupport χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1) :
    ∃ D : ℕ → ℝ, (∀ s, 1 ≤ D s) ∧
      ∀ (T : H →L[ℂ] H) (cost high : ℕ → ℝ),
      (∀ s, 0 ≤ cost s) → (∀ s, 0 ≤ high s) →
      (∀ s, ∀ W : H →L[ℂ] H, (W = T ∨ W = T.adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-1 : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W u) ∧
          vectorFourierSobolevNorm (s : ℝ) (W u) ≤
            cost s*(vectorFourierSobolevNorm ((s-1 : ℕ) : ℝ) u+high s*‖u‖)) →
      ∀ (U V : Set E) (hU : MeasurableSet U) (_hV : MeasurableSet V),
      tsupport χin ⊆ U → tsupport χout ⊆ V →
      let L := localRetardedOperator hU V
        (measuredOperator χout χin ho.continuous hi.continuous hob hib T)
      ∀ s,
      (∀ u : LocalL2 U F, MemRestrictionSobolev U (s-1) u →
        MemRestrictionSobolev V s (L u) ∧ restrictionSobolevNorm V s (L u) ≤
          (D s*cost s)*(restrictionSobolevNorm U (s-1) u+high s*‖u‖)) ∧
      (∀ v : LocalL2 V F, MemRestrictionSobolev V (s-1) v →
        MemRestrictionSobolev U s (L.adjoint v) ∧ restrictionSobolevNorm U s (L.adjoint v) ≤
          (D s*cost s)*(restrictionSobolevNorm V (s-1) v+high s*‖v‖)) := by
  choose Di hDi hfi using fun s ↦ exists_measuredOperator_restriction_tame_constant
    (q := q) χout χin ho hi hoc hic hob hib (s-1) s
  choose Do hDo hfo using fun s ↦ exists_measuredOperator_restriction_tame_constant
    (q := q) χin χout hi ho hic hoc hib hob (s-1) s
  refine ⟨fun s ↦ max (Di s) (Do s), fun s ↦ (hDi s).trans (le_max_left _ _), ?_⟩
  intro T cost high hc hh hT U V hU hV hsi hso L s
  constructor
  · intro u hu
    obtain ⟨hm, hn⟩ := hfi s T (cost s) (high s) (hc s) (hh s)
      (hT s _ (Or.inl rfl)) U V hU hsi u hu
    exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hc s))
      (add_nonneg restrictionSobolevNorm_nonneg (mul_nonneg (hh s) (norm_nonneg u))))⟩
  · intro v hv
    dsimp only [L]
    rw [local_measuredOperator_adjoint hU hV]
    obtain ⟨hm, hn⟩ := hfo s T.adjoint (cost s) (high s) (hc s) (hh s)
      (hT s _ (Or.inr rfl)) V U hV hso v hv
    exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (hc s))
      (add_nonneg restrictionSobolevNorm_nonneg (mul_nonneg (hh s) (norm_nonneg v))))⟩

end JanetCartan.RegularSector.FiniteAssembly
