module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.LocalComplex
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.Remainder
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedRestriction
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Scale

/-!
# Ordinary all-order regularity of the same complete complex solver

Compose the original real inverse's positive estimate with the two fixed
bumps and the actual full solver. Both quadratures are recombined on the
same complex inverse. This gives the ordinary Fourier bounds needed to
construct joint smooth representatives; it is not the uniform demodulated
envelope estimate. Its constants may depend on the fixed history's high
coefficient norms, as permitted for this qualitative regularity step.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff NNReal ENNReal JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse

open LocalSobolev SmallSupport Pseudodifferential RegularSector RegularSector.Realization
open RegularSector.Characteristic.RetardedLocalization
open ArbitraryAccuracy.ResidualLocalization
open ResponseTransfer ResponseTransfer.Complement

variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "CF" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp CF 2 (volume : Measure E)

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- For the original source that already contains its inner bump, the
SAME complete inverse has an ordinary all-order Fourier bound without any
additional recut. The original real positive estimate is applied to both
quadratures and recombined before the fixed full solver. This constructs
the graph bound needed by `contDiffOn_recut_full_solver_joint_solution`
(`app:ch_response:thm:response-literal-transfer`). -/
theorem complex_recut_full_solver_fourier_bound_of_real_positive_estimates
    (W : Set E) (hW : MeasurableSet W) {center : E} (χ₃ : ContDiffBump center)
    (hs₃ : tsupport (χ₃ : E → ℝ) ⊆ W)
    (R : LocalL2 W CF →L[ℂ] LocalL2 W CF)
    (hreal : conjugateOperator R.toLinearMap = R.toLinearMap) (hR : ‖R‖ < 1)
    (S : H →L[ℂ] H) (s : ℕ)
    (CI highI CS highS : ℝ) (hCI : 0 ≤ CI) (hhighI : 0 ≤ highI)
    (hCS : 0 ≤ CS) (hhighS : 0 ≤ highS)
    (hInv : ∀ u : LocalL2 W E, MemRestrictionSobolev W s u →
      MemRestrictionSobolev W s (neumannInverse (realOutputCompression R) u) ∧
        restrictionSobolevNorm W s (neumannInverse (realOutputCompression R) u) ≤
          CI * (restrictionSobolevNorm W s u + highI * ‖u‖))
    (hS : ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
      MemVectorFourierSobolev (s : ℝ) (S u) ∧
        vectorFourierSobolevNorm (s : ℝ) (S u) ≤
          CS * (vectorFourierSobolevNorm (s : ℝ) u + highS * ‖u‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
      MemVectorFourierSobolev (s : ℝ)
        (complexLocalSolverObservation hW χ₃ S (complexNeumannInverse R hR) u) ∧
      vectorFourierSobolevNorm (s : ℝ)
        (complexLocalSolverObservation hW χ₃ S (complexNeumannInverse R hR) u) ≤
          C * vectorFourierSobolevNorm (s : ℝ) u := by
  obtain ⟨Cq, hCq, hquad⟩ := SignedProductEstimates.exists_source_quadrature_restriction_comparison
    (d := d) s
  obtain ⟨Co, hCo, hout⟩ := exists_bump_zeroExtension_fourier_constant (r := d+1) χ₃ s
  let Cinv := CI * (1+highI)
  have hCinv : 0 ≤ Cinv := mul_nonneg hCI (by positivity)
  let Cstep := Cinv * Cq
  have hCstep : 0 ≤ Cstep := mul_nonneg hCinv hCq
  let C := CS * (1+highS) * Co * (6*Cstep)
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (mul_nonneg hCS (by positivity)) hCo.le) (mul_nonneg (by norm_num) hCstep)
  refine ⟨C, hC, ?_⟩
  intro u hu
  have hquadrature (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
      let v := l2RealPart (volume.restrict W) (ζ • restrictL2 W u)
      MemRestrictionSobolev W s (neumannInverse (realOutputCompression R) v) ∧
        restrictionSobolevNorm W s (neumannInverse (realOutputCompression R) v) ≤
          Cstep * vectorFourierSobolevNorm (s : ℝ) u := by
    intro v
    obtain ⟨hq, hbq⟩ := hquad u hu W ζ hζ
    obtain ⟨hi, hbi⟩ := hInv v hq
    refine ⟨hi, hbi.trans ?_⟩
    calc
      _ ≤ CI * (restrictionSobolevNorm W s v + highI * restrictionSobolevNorm W s v) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_le_restrictionSobolevNorm hq) hhighI)) hCI
      _ = Cinv * restrictionSobolevNorm W s v := by dsimp only [Cinv]; ring
      _ ≤ Cinv * (Cq*vectorFourierSobolevNorm (s : ℝ) u) :=
        mul_le_mul_of_nonneg_left hbq hCinv
      _ = _ := by dsimp only [Cstep]; simp only [mul_assoc]
  let ur := l2RealPart (volume.restrict W) (restrictL2 W u)
  let ui := l2RealPart (volume.restrict W) (-Complex.I • restrictL2 W u)
  have hr := hquadrature 1 (by simp)
  simp only [one_smul] at hr
  have hi := hquadrature (-Complex.I) (by simp)
  have hb := complex_inverse_power_remainder_of_real_quadratures R hreal hR s 0 ur ui
    hr.1 hi.1 hr.2 hi.2
  dsimp only at hb
  have he := congrArg (complexNeumannInverse R hR) (quadrature_decomposition (restrictL2 W u))
  let v := complexNeumannInverse R hR (restrictL2 W u)
  have hvm : MemRestrictionSobolev W s v :=
    (congrArg (MemRestrictionSobolev W s) he).mp hb.1
  have hvb : restrictionSobolevNorm W s v ≤ (6*Cstep)*vectorFourierSobolevNorm (s : ℝ) u :=
    ((congrArg (restrictionSobolevNorm W s) he).symm.le.trans hb.2).trans_eq
      (by simp only [mul_assoc])
  obtain ⟨hzm, hzb⟩ := hout W hW hs₃ v hvm
  let z := zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ v)
  have hz : vectorFourierSobolevNorm (s : ℝ) z ≤ Co*(6*Cstep)*vectorFourierSobolevNorm (s : ℝ) u :=
    hzb.trans ((mul_le_mul_of_nonneg_left hvb hCo.le).trans_eq (mul_assoc _ _ _).symm)
  have hzL2 : ‖z‖ ≤ vectorFourierSobolevNorm (s : ℝ) z := by
    simpa only [vectorFourierSobolevNorm_zero] using
      vectorFourierSobolevNorm_mono hzm (show (0:ℝ) ≤ s by positivity)
  obtain ⟨hSm, hSb⟩ := hS z hzm
  refine ⟨hSm, hSb.trans ?_⟩
  calc
    _ ≤ CS * (vectorFourierSobolevNorm (s : ℝ) z + highS * vectorFourierSobolevNorm (s : ℝ) z) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hzL2 hhighS)) hCS
    _ = CS*(1+highS)*vectorFourierSobolevNorm (s : ℝ) z := by ring
    _ ≤ CS*(1+highS)*(Co*(6*Cstep)*vectorFourierSobolevNorm (s : ℝ) u) :=
      mul_le_mul_of_nonneg_left hz (mul_nonneg hCS (by positivity))
    _ = _ := by dsimp only [C]; simp only [mul_assoc]

/-- The actual real inverse and full solver's positive estimates imply an
ordinary Fourier bound on their SAME complete complex composition, with no
loss of Sobolev order. This supplies `contDiff_joint_graph_realization` for
the literal fixed smooth solver. No joint smoothness or output Fourier
bound is assumed (`app:ch_response:thm:response-literal-transfer`). -/
theorem complex_full_solver_fourier_bound_of_real_positive_estimates
    (W : Set E) (hW : MeasurableSet W) {center : E} (χ₂ χ₃ : ContDiffBump center)
    (hs₂ : tsupport (χ₂ : E → ℝ) ⊆ W) (hs₃ : tsupport (χ₃ : E → ℝ) ⊆ W)
    (R : LocalL2 W CF →L[ℂ] LocalL2 W CF)
    (hreal : conjugateOperator R.toLinearMap = R.toLinearMap) (hR : ‖R‖ < 1)
    (S : H →L[ℂ] H) (s : ℕ)
    (CI highI CS highS : ℝ) (hCI : 0 ≤ CI) (hhighI : 0 ≤ highI)
    (hCS : 0 ≤ CS) (hhighS : 0 ≤ highS)
    (hInv : ∀ u : LocalL2 W E, MemRestrictionSobolev W s u →
      MemRestrictionSobolev W s (neumannInverse (realOutputCompression R) u) ∧
        restrictionSobolevNorm W s (neumannInverse (realOutputCompression R) u) ≤
          CI * (restrictionSobolevNorm W s u + highI * ‖u‖))
    (hS : ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
      MemVectorFourierSobolev (s : ℝ) (S u) ∧
        vectorFourierSobolevNorm (s : ℝ) (S u) ≤
          CS * (vectorFourierSobolevNorm (s : ℝ) u + highS * ‖u‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H, MemVectorFourierSobolev (s : ℝ) u →
      MemVectorFourierSobolev (s : ℝ)
        (complexBumpedLocalObservation hW χ₂ χ₃ S (complexNeumannInverse R hR) u) ∧
      vectorFourierSobolevNorm (s : ℝ)
        (complexBumpedLocalObservation hW χ₂ χ₃ S (complexNeumannInverse R hR) u) ≤
          C * vectorFourierSobolevNorm (s : ℝ) u := by
  obtain ⟨Cq, hCq, hquad⟩ := SignedProductEstimates.exists_source_quadrature_restriction_comparison
    (d := d) s
  obtain ⟨Ci, hCi, hin⟩ := exists_bumpL2_sobolev_bound (F := E) χ₂ s
  obtain ⟨Co, hCo, hout⟩ := exists_bump_zeroExtension_fourier_constant (r := d+1) χ₃ s
  let Cinv := CI * (1+highI)
  have hCinv : 0 ≤ Cinv := mul_nonneg hCI (by positivity)
  let Cstep := Cinv * Ci * Cq
  have hCstep : 0 ≤ Cstep := mul_nonneg (mul_nonneg hCinv (zero_le_one.trans hCi)) hCq
  let C := CS * (1+highS) * Co * (6*Cstep)
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (mul_nonneg hCS (by positivity)) hCo.le) (mul_nonneg (by norm_num) hCstep)
  refine ⟨C, hC, ?_⟩
  intro u hu
  have hquadrature (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
      let v := bumpL2 (p := 2) le_rfl χ₂
        (l2RealPart (volume.restrict W) (ζ • restrictL2 W u))
      MemRestrictionSobolev W s (neumannInverse (realOutputCompression R) v) ∧
        restrictionSobolevNorm W s (neumannInverse (realOutputCompression R) v) ≤
          Cstep * vectorFourierSobolevNorm (s : ℝ) u := by
    intro v
    obtain ⟨hq, hbq⟩ := hquad u hu W ζ hζ
    obtain ⟨hb, hbb⟩ := hin W hW hs₂ _ hq
    obtain ⟨hi, hbi⟩ := hInv v hb
    refine ⟨hi, hbi.trans ?_⟩
    have hv : restrictionSobolevNorm W s v ≤ Ci * Cq * vectorFourierSobolevNorm (s : ℝ) u :=
      hbb.trans ((mul_le_mul_of_nonneg_left hbq (zero_le_one.trans hCi)).trans_eq
        (mul_assoc _ _ _).symm)
    calc
      _ ≤ CI * (restrictionSobolevNorm W s v + highI * restrictionSobolevNorm W s v) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_le_restrictionSobolevNorm hb) hhighI)) hCI
      _ = Cinv * restrictionSobolevNorm W s v := by dsimp only [Cinv]; ring
      _ ≤ Cinv * (Ci*Cq*vectorFourierSobolevNorm (s : ℝ) u) :=
        mul_le_mul_of_nonneg_left hv hCinv
      _ = _ := by dsimp only [Cstep]; simp only [mul_assoc]
  let ur := l2RealPart (volume.restrict W) (restrictL2 W u)
  let ui := l2RealPart (volume.restrict W) (-Complex.I • restrictL2 W u)
  have hr := hquadrature 1 (by simp)
  simp only [one_smul] at hr
  have hi := hquadrature (-Complex.I) (by simp)
  have hb := complex_inverse_power_remainder_of_real_quadratures R hreal hR s 0
    (bumpL2 (p := 2) le_rfl χ₂ ur) (bumpL2 (p := 2) le_rfl χ₂ ui)
    hr.1 hi.1 hr.2 hi.2
  dsimp only at hb
  have heSource :
      l2ComplexInclusion (volume.restrict W) (bumpL2 (p := 2) le_rfl χ₂ ur) +
        Complex.I • l2ComplexInclusion (volume.restrict W) (bumpL2 (p := 2) le_rfl χ₂ ui) =
      bumpL2 (p := 2) le_rfl χ₂ (restrictL2 W u) :=
    (bumpL2_complex_quadratures χ₂ ur ui).symm.trans
      (congrArg (bumpL2 (p := 2) le_rfl χ₂) (quadrature_decomposition (restrictL2 W u)))
  have he := congrArg (complexNeumannInverse R hR) heSource
  let v := complexNeumannInverse R hR (bumpL2 (p := 2) le_rfl χ₂ (restrictL2 W u))
  have hvm : MemRestrictionSobolev W s v :=
    (congrArg (MemRestrictionSobolev W s) he).mp hb.1
  have hvb : restrictionSobolevNorm W s v ≤ (6*Cstep)*vectorFourierSobolevNorm (s : ℝ) u :=
    ((congrArg (restrictionSobolevNorm W s) he).symm.le.trans hb.2).trans_eq
      (by simp only [mul_assoc])
  obtain ⟨hzm, hzb⟩ := hout W hW hs₃ v hvm
  let z := zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ v)
  have hz : vectorFourierSobolevNorm (s : ℝ) z ≤ Co*(6*Cstep)*vectorFourierSobolevNorm (s : ℝ) u :=
    hzb.trans ((mul_le_mul_of_nonneg_left hvb hCo.le).trans_eq (mul_assoc _ _ _).symm)
  have hzL2 : ‖z‖ ≤ vectorFourierSobolevNorm (s : ℝ) z := by
    simpa only [vectorFourierSobolevNorm_zero] using
      vectorFourierSobolevNorm_mono hzm (show (0:ℝ) ≤ s by positivity)
  obtain ⟨hSm, hSb⟩ := hS z hzm
  refine ⟨hSm, hSb.trans ?_⟩
  calc
    _ ≤ CS * (vectorFourierSobolevNorm (s : ℝ) z + highS * vectorFourierSobolevNorm (s : ℝ) z) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hzL2 hhighS)) hCS
    _ = CS*(1+highS)*vectorFourierSobolevNorm (s : ℝ) z := by ring
    _ ≤ CS*(1+highS)*(Co*(6*Cstep)*vectorFourierSobolevNorm (s : ℝ) u) :=
      mul_le_mul_of_nonneg_left hz (mul_nonneg hCS (by positivity))
    _ = _ := by dsimp only [C]; simp only [mul_assoc]

end JanetCartan.FixedDomainInverse
