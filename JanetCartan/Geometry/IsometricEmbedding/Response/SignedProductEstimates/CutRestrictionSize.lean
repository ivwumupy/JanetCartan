module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.PhysicalSize
public import JanetCartan.Analysis.Sobolev.Local.Cutoff.AllOrders
public import JanetCartan.Analysis.Sobolev.Local.Comparison.SmoothBounds.NormComparison
public import JanetCartan.Analysis.Sobolev.Local.Comparison.WeakUniqueness
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.RestrictionPairing

/-!
# Sharp cutoff transfer for the physical signed response

The physical cutoff in `app:ch_pairs:eq:pairs-lag-sum-size` sends the actual
local Sobolev class of a smooth response to its literal periodization at the
same order. Weak-jet uniqueness identifies the cut extension with this
physical field. The already proved Cartesian periodization identity then
preserves the carrier power. No classical Sobolev embedding or choice of
another representative is needed.

Consumer: the physical output of the normalized response reconstruction in
`UniformStep.ProductProfiles`. Its analytic local size bound is separate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.SignedProductEstimates
open LocalSobolev UniformStep.Periodization
variable {n N : ℕ}

/-- The original physical cutoff preserves Sobolev order when passing from
the local response to its actual torus field
(`app:ch_pairs:eq:pairs-lag-sum-size`). The constant precedes the response,
measurement domain and local class. All derivative norms are proved from
genuine extensions and weak-jet uniqueness, with no size hypothesis on the
periodized field. -/
theorem exists_cutToTorus_restriction_sobolev_constants
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {b : ℝ} (hb : b < 1/2) (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ b}) :
    ∃ C : ℕ → ℝ, (∀ r, 0 ≤ C r) ∧
      ∀ (U : Set (Euclidean n)) (_hU : MeasurableSet U), tsupport χ ⊆ U →
      ∀ (f : Euclidean n → Euclidean N), ContDiff ℝ ∞ f →
      ∀ (u : LocalL2 U (Euclidean N)), u =ᵐ[volume.restrict U] f →
      ∀ r : ℕ, MemRestrictionSobolev U r u →
        periodicSobolevNorm r (cutToTorus χ f) ≤ C r * restrictionSobolevNorm U r u := by
  choose B hB hcut using fun r ↦ exists_cutoffAllJet_bound (F := Euclidean N) χ hχ hc r
  let C := fun r ↦ Real.sqrt (r.factorial : ℝ) *
    Real.sqrt (BallExtension.cartesianEnergyComparisonConstant n r) * B r
  have hC r : 0 ≤ C r := mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (zero_le_one.trans (hB r))
  refine ⟨C, hC, ?_⟩
  intro U hU hsU f hf u hrep r hu
  apply le_mul_restrictionSobolevNorm_of_extensions hu (hC r)
  intro e
  have heq : (fun y ↦ χ y • e.toFun y) =ᵐ[volume] cutField χ f := by
    have he := (ae_restrict_iff' hU).mp (e.restrict_eq.trans hrep)
    filter_upwards [he] with y hy
    by_cases hyU : y ∈ U
    · exact congrArg (fun z ↦ χ y • z) (hy hyU)
    · have hz : χ y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hyU (hsU h))
      simp only [cutField, hz, zero_smul]
  have hw := hasWeakJetOn_cutoffAllJet e.weakJet e.memLp_jet hχ hc
  have hfcut : ContDiff ℝ ∞ (cutField χ f) := contDiff_cutField hχ hf
  have hclass := Mollification.hasWeakJetOn_of_contDiff volume
    (hfcut.of_le (show (r : WithTop ℕ∞) ≤ ∞ by simp)) univ
  have hejet (j : ℕ) (hj : j ≤ r) :
      cutoffAllJet χ hχ hc e.jet j =ᵐ[volume] iteratedFDeriv ℝ j (cutField χ f) := by
    simpa only [Measure.restrict_univ] using
      hw.ae_eq hclass isOpen_univ (ae_restrict_of_ae heq) j hj
  have hjmem (j : ℕ) (hj : j ≤ r) :
      MemLp (iteratedFDeriv ℝ j (cutField χ f)) 2 volume :=
    (memLp_cutoffAllJet e.memLp_jet hχ hc hj).ae_eq (hejet j hj)
  have hjet : jetL2Norm univ r (fun j ↦ iteratedFDeriv ℝ j (cutField χ f)) ≤ B r * e.jetNorm := by
    unfold jetL2Norm SobolevExtension.jetNorm
    simp only [Measure.restrict_univ]
    have hn := hcut r e.jet e.memLp_jet
    convert hn using 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [eLpNorm_congr_ae (hejet j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))]
  have hcart := cartesianJetNorm_le_mul_jetL2Norm univ r
    (fun j ↦ iteratedFDeriv ℝ j (cutField χ f))
    (fun j hj ↦ by simpa only [Measure.restrict_univ] using hjmem j hj)
  calc
    _ ≤ Real.sqrt (r.factorial : ℝ) *
        cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j (cutField χ f)) :=
      periodicSobolevNorm_cutToTorus_le hb hs hχ hf r
    _ ≤ Real.sqrt (r.factorial : ℝ) *
        (Real.sqrt (BallExtension.cartesianEnergyComparisonConstant n r) *
          jetL2Norm univ r (fun j ↦ iteratedFDeriv ℝ j (cutField χ f))) :=
      mul_le_mul_of_nonneg_left hcart (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (r.factorial : ℝ) *
        (Real.sqrt (BallExtension.cartesianEnergyComparisonConstant n r) * (B r * e.jetNorm)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hjet (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ = C r * e.jetNorm := by dsimp only [C]; ring

end JanetCartan.SignedProductEstimates
