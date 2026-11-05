module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.MixedDatumProfiles
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.Algebra
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.Interpolation

/-!
# Algebra of constructed spatial datum jets

The parameter commutation step in `app:ch_response:eq:direct-envelope-profile`
applies spatial jets to Taylor remainders. These identities follow from
uniqueness of actual weak derivatives, on their finite Sobolev domains.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap LineDeriv
open JanetCartan.Pseudodifferential

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier

variable {d : ℕ}
local notation "L2" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

private theorem datumWeightedFourier_smul (s c : ℝ) (f : L2) :
    weightedL2Fourier s (c • f) =ᵐ[volume] c • weightedL2Fourier s f := by
  have h : 𝓕 (c • f) = c • 𝓕 f := ((fourierCLM ℂ L2).restrictScalars ℝ).map_smul c f
  filter_upwards [Lp.coeFn_smul c (𝓕 f)] with x hx
  simp only [weightedL2Fourier, h, hx, Pi.smul_apply]
  exact smul_comm _ _ _

/-- Real scalar multiplication preserves the finite source Sobolev domain used
for Taylor remainders in `app:ch_response:eq:direct-envelope-profile`. -/
theorem datum_memFourierSobolev_smul {s : ℝ} {f : L2}
    (hf : MemFourierSobolev s f) (c : ℝ) : MemFourierSobolev s (c • f) :=
  (hf.const_smul c).ae_eq (datumWeightedFourier_smul s c f).symm

/-- Homogeneity of the source norm for the parameter Taylor remainder in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem datum_fourierSobolevNorm_smul (s c : ℝ) (f : L2) :
    fourierSobolevNorm s (c • f) = ‖c‖ * fourierSobolevNorm s f := by
  unfold fourierSobolevNorm
  rw [eLpNorm_congr_ae (datumWeightedFourier_smul s c f), eLpNorm_const_smul,
    ENNReal.toReal_mul, enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm]

/-- Subtraction bound for the source norms in the parameter commutation step
of `app:ch_response:eq:direct-envelope-profile`. -/
theorem datum_fourierSobolevNorm_sub_le {s : ℝ} {f g : L2}
    (hf : MemFourierSobolev s f) (hg : MemFourierSobolev s g) :
    fourierSobolevNorm s (f - g) ≤ fourierSobolevNorm s f + fourierSobolevNorm s g := by
  rw [fourierSobolevNorm_sub_eq_norm hf hg]
  simpa only [Lp.norm_toLp _ hf, Lp.norm_toLp _ hg, fourierSobolevNorm] using norm_sub_le
    (hf.toLp (weightedL2Fourier s f)) (hg.toLp (weightedL2Fourier s g))

private theorem datum_coordinateDerivative_sub {i : Fin d} {f g df dg : L2}
    (hf : HasEuclideanL2CoordinateDerivative i f df)
    (hg : HasEuclideanL2CoordinateDerivative i g dg) :
    HasEuclideanL2CoordinateDerivative i (f - g) (df - dg) := by
  let T := Lp.toTemperedDistributionCLM ℂ (volume : Measure (EuclideanSpace ℝ (Fin d))) 2
  change (lineDerivOpCLM ℂ _ (EuclideanSpace.basisFun (Fin d) ℝ i)) (T (f - g)) = T (df - dg)
  rw [map_sub, map_sub, map_sub]
  exact congrArg₂ (· - ·) hf hg

private theorem datum_coordinateDerivative_smul {i : Fin d} {f df : L2}
    (hf : HasEuclideanL2CoordinateDerivative i f df) (c : ℝ) :
    HasEuclideanL2CoordinateDerivative i (c • f) (c • df) := by
  let T := (Lp.toTemperedDistributionCLM ℂ (volume : Measure (EuclideanSpace ℝ (Fin d))) 2).restrictScalars ℝ
  let D := (lineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin d), ℂ) (EuclideanSpace.basisFun (Fin d) ℝ i)).restrictScalars ℝ
  change D (T (c • f)) = T (c • df)
  rw [map_smul, map_smul, map_smul]
  exact congrArg (c • ·) hf

/-- The constructed spatial jet respects differences on its actual Sobolev
 domain, for `app:ch_response:eq:direct-envelope-profile`. -/
theorem datumSpatialJet_sub (z : List (Fin d)) {f g : L2}
    (hf : MemFourierSobolev (z.length : ℝ) f)
    (hg : MemFourierSobolev (z.length : ℝ) g) :
    datumSpatialJet z (f - g) = datumSpatialJet z f - datumSpatialJet z g := by
  induction z with
  | nil => rfl
  | cons i z ih =>
    have hf' : MemFourierSobolev ((1 + z.length : ℕ) : ℝ) f := by simpa [Nat.add_comm] using hf
    have hg' : MemFourierSobolev ((1 + z.length : ℕ) : ℝ) g := by simpa [Nat.add_comm] using hg
    have heq := ih (hf.mono (by simp)) (hg.mono (by simp))
    have h := datum_coordinateDerivative_sub
      (datumSpatialJet_hasDerivative i z f hf') (datumSpatialJet_hasDerivative i z g hg')
    rw [← heq] at h
    exact (datumSpatialJet_hasDerivative i z (f - g) (hf'.sub hg')).unique h

/-- Real scalar linearity of the spatial jet on its Sobolev domain, for the
parameter Taylor remainder in `app:ch_response:eq:direct-envelope-profile`. -/
theorem datumSpatialJet_smul (z : List (Fin d)) {f : L2}
    (hf : MemFourierSobolev (z.length : ℝ) f) (c : ℝ) :
    datumSpatialJet z (c • f) = c • datumSpatialJet z f := by
  induction z with
  | nil => rfl
  | cons i z ih =>
    have hf' : MemFourierSobolev ((1 + z.length : ℕ) : ℝ) f := by simpa [Nat.add_comm] using hf
    have heq := ih (hf.mono (by simp))
    have h := datum_coordinateDerivative_smul (datumSpatialJet_hasDerivative i z f hf') c
    rw [← heq] at h
    exact (datumSpatialJet_hasDerivative i z (c • f) (datum_memFourierSobolev_smul hf' c)).unique h

/-- Interpolation estimate for a spatial jet of a datum error, consumed by
parameter commutation in `app:ch_response:eq:direct-envelope-profile`. -/
theorem datumSpatialJet_norm_interpolate (z : List (Fin d)) {s : ℝ}
    (hs : (z.length : ℝ) ≤ s) {f : L2} (hf : MemFourierSobolev s f) :
    ‖datumSpatialJet z f‖ ≤ (2 * Real.pi) ^ z.length *
      (‖f‖ ^ (1 - z.length / s) * fourierSobolevNorm s f ^ (z.length / s)) := by
  have h := (datumSpatialJet_mem_and_norm 0 z f (by simpa using hf.mono hs)).2
  simp only [Nat.cast_zero, Nat.zero_add, fourierSobolevNorm_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (by simpa only [fourierSobolevNorm_zero] using
      fourierSobolevNorm_interpolate (by positivity) hs hf) (by positivity))

end JanetCartan.IsometricEmbedding.Response.NearCarrier
