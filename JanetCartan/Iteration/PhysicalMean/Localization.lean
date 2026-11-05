module

public import JanetCartan.Iteration.PhysicalMean.CanonicalSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.LocalComparison.Cutoff
public import JanetCartan.Analysis.Sobolev.Local.Comparison.WeakUniqueness
public import JanetCartan.Analysis.PhysicalSobolev.Interpolation
public import JanetCartan.Analysis.Fourier.Periodic.Interpolation

/-!
# Real localization of the same auxiliary source residual

The original complete source operator is realized on a localized auxiliary
torus.  For `app:ch_mean_pairs:prop:mean-iteration`, this file constructs the
literal physical cutoff of that SAME smooth source representative and proves
its actual Lebesgue jet bounds.  The cutoff is fixed before the source/order.
No global physical history is asserted to be periodic and no Sobolev norms
on different spaces are identified.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory FourierTransform
open scoped ContDiff Topology

namespace JanetCartan.PhysicalMean

open CurrentMean SmoothPeriodicFamily AuxiliaryRawBand LocalSobolev PeriodicLocalL2

variable {n : ℕ}

/-- The literal real localized representative of the SAME smooth source. -/
def cutSmoothResidual (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (f : SmoothResidual n) :
    SchwartzMap (Euclidean n) (Euclidean n) :=
  (hc.smul_right (f' := periodicLift (fun x ↦ f.val x ()))).toSchwartzMap
    (hχ.smul (smooth f ()).2)

@[simp] theorem cutSmoothResidual_apply (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (f : SmoothResidual n) (x : Euclidean n) :
    cutSmoothResidual χ hχ hc f x = χ x • periodicLift (fun y ↦ f.val y ()) x := rfl

/-- Every core value is unchanged on the original fixed plateau. -/
theorem cutSmoothResidual_eqOn (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) {K : Set (Euclidean n)}
    (hK : EqOn χ (fun _ ↦ 1) K) (f : SmoothResidual n) :
    EqOn (cutSmoothResidual χ hχ hc f) (periodicLift (fun y ↦ f.val y ())) K := by
  intro x hx
  simp only [cutSmoothResidual_apply, hK hx, one_smul]

/-- The ACTUAL full physical jets of the same localized source have the
fixed-cutoff Sobolev bound.  Weak-jet uniqueness upgrades the existing literal
extension theorem to the actual Fréchet jets; no extension is chosen as a
replacement source (`app:ch_mean_pairs:prop:mean-iteration`, Step 5). -/
theorem cutSmoothResidual_jetL2_le (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ halfOpenCell n)
    (f : SmoothResidual n) (s : ℕ) :
    ∑ j ∈ Finset.range (s + 1),
      (eLpNorm (iteratedFDeriv ℝ j (cutSmoothResidual χ hχ hc f)) 2 volume).toReal ≤
        localCutoffConstant s χ * periodicSobolevNorm s (fun x ↦ f.val x ()) := by
  obtain ⟨e, he, hb⟩ := exists_cutoff_sobolevExtension_of_eqOn
    (W := (∅ : Set (Euclidean n))) isOpen_empty hχ hc hs
    (by intro x hx; exact False.elim hx)
    (smooth f ()) (g := periodicLift (fun x ↦ f.val x ())) (by intro x _; rfl)
    (0 : LocalL2 (∅ : Set (Euclidean n)) (Euclidean n))
    (by simp only [Measure.restrict_empty, ae_zero]; exact Filter.eventually_bot) s
  have hw := Mollification.hasWeakJetOn_of_contDiff volume
    ((cutSmoothResidual χ hχ hc f).smooth s) univ
  have heq : (cutSmoothResidual χ hχ hc f : Euclidean n → Euclidean n) =ᵐ[volume.restrict univ] e.toFun := by
    apply Filter.Eventually.of_forall
    intro x
    rw [he]
    rfl
  have hjets := hw.ae_eq e.weakJet isOpen_univ heq
  calc
    _ = e.jetNorm := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjet : iteratedFDeriv ℝ j (cutSmoothResidual χ hχ hc f) =ᵐ[volume] e.jet j := by
        simpa only [Measure.restrict_univ] using
          hjets j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      rw [eLpNorm_congr_ae hjet]
    _ ≤ _ := hb

/-- The same localized source has the true physical radian Bessel norm at
exactly the same order. Constants depend only on the fixed cutoff and order,
never on Picard count, source, sample, or accuracy. -/
theorem exists_cutSmoothResidual_physicalSobolev_bound
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ halfOpenCell n) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SmoothResidual n,
      (eLpNorm (fun ξ ↦ Pseudodifferential.euclideanSobolevWeight (s : ℝ)
        ((2 * Real.pi) • ξ) • 𝓕 (PhysicalCutoff.complexify (cutSmoothResidual χ hχ hc f)) ξ)
        2 volume).toReal ≤ C * periodicSobolevNorm s (fun x ↦ f.val x ()) := by
  obtain ⟨C, hC, hphys⟩ := PhysicalSobolev.exists_physicalWeightedNorm_le_jetL2 n n s
  refine ⟨C * localCutoffConstant s χ, mul_nonneg hC.le (localCutoffConstant_nonneg s χ), ?_⟩
  intro f
  exact (hphys _).trans ((mul_le_mul_of_nonneg_left
    (cutSmoothResidual_jetL2_le χ hχ hc hs f s) hC.le).trans_eq (mul_assoc _ _ _).symm)

/-- The low physical endpoint is controlled by the SAME source L² class,
not a substitute high norm. This is essential for the final small residual. -/
theorem cutSmoothResidual_l2_le (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ halfOpenCell n)
    (f : SmoothResidual n) :
    (eLpNorm (cutSmoothResidual χ hχ hc f : Euclidean n → Euclidean n) 2 volume).toReal ≤
      localCutoffConstant 0 χ * ‖smoothResidualToL2 n f‖ := by
  have hb := cutSmoothResidual_jetL2_le χ hχ hc hs f 0
  simp only [Nat.zero_add, Finset.sum_range_one] at hb
  have he : eLpNorm (iteratedFDeriv ℝ 0 (cutSmoothResidual χ hχ hc f)) 2 volume =
      eLpNorm (cutSmoothResidual χ hχ hc f : Euclidean n → Euclidean n) 2 volume :=
    eLpNorm_congr_norm_ae
      (((cutSmoothResidual χ hχ hc f).smooth ⊤).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
      (cutSmoothResidual χ hχ hc f).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ ↦ norm_iteratedFDeriv_zero)
  rw [he, Nat.cast_zero, periodicSobolevNorm_zero_eq_periodicL2Norm (memLp f ()),
    ← norm_componentL2 () f] at hb
  exact hb

/-- Apply the genuine physical interpolation to the SAME localized source
and return to its original plateau.  The auxiliary L² and Sobolev norms are
used only through the proved real norm transfer, never identified with global
physical history norms (`new:lem:interpolation`). -/
theorem exists_source_plateau_interpolation
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ halfOpenCell n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SmoothResidual n, ∀ x : Euclidean n, χ x = 1 →
      ‖periodicLift (fun y ↦ f.val y ()) x‖ ≤ C * Real.sqrt ‖smoothResidualToL2 n f‖ *
        Real.sqrt (periodicSobolevNorm (RevisedScales.sourceOrder n) (fun y ↦ f.val y ())) := by
  obtain ⟨A, hA, hhi⟩ := exists_cutSmoothResidual_physicalSobolev_bound
    χ hχ hc hs (RevisedScales.sourceOrder n)
  let L := localCutoffConstant 0 χ
  let B := PhysicalSobolev.embeddingConstant n
  have hL : 0 ≤ L := localCutoffConstant_nonneg 0 χ
  have hB : 0 ≤ B := PhysicalSobolev.embeddingConstant_nonneg n
  refine ⟨B * Real.sqrt L * Real.sqrt A, by positivity, ?_⟩
  intro f x hx
  let u := cutSmoothResidual χ hχ hc f
  have hlow := cutSmoothResidual_l2_le χ hχ hc hs f
  have hi := PhysicalSobolev.physicalWeightedNorm_interpolate_half (RevisedScales.baselineOrder n : ℝ) u
  have horder : (RevisedScales.sourceOrder n : ℝ) = 2 * (RevisedScales.baselineOrder n : ℝ) := by
    simp only [RevisedScales.sourceOrder, Nat.cast_mul, Nat.cast_ofNat]
  rw [← horder] at hi
  have he : u x = periodicLift (fun y ↦ f.val y ()) x := by
    simp only [u, cutSmoothResidual_apply, hx, one_smul]
  calc
    _ = ‖u x‖ := congrArg norm he.symm
    _ ≤ B * (eLpNorm (fun ξ ↦ Pseudodifferential.euclideanSobolevWeight (RevisedScales.baselineOrder n : ℝ)
        ((2 * Real.pi) • ξ) • 𝓕 (PhysicalCutoff.complexify u) ξ) 2 volume).toReal :=
      PhysicalSobolev.norm_le u x
    _ ≤ B * (Real.sqrt ((eLpNorm (u : Euclidean n → Euclidean n) 2 volume).toReal) *
        Real.sqrt ((eLpNorm (fun ξ ↦ Pseudodifferential.euclideanSobolevWeight (RevisedScales.sourceOrder n : ℝ)
          ((2 * Real.pi) • ξ) • 𝓕 (PhysicalCutoff.complexify u) ξ) 2 volume).toReal)) :=
      mul_le_mul_of_nonneg_left hi hB
    _ ≤ B * (Real.sqrt (L * ‖smoothResidualToL2 n f‖) *
        Real.sqrt (A * periodicSobolevNorm (RevisedScales.sourceOrder n) (fun y ↦ f.val y ()))) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact mul_le_mul (Real.sqrt_le_sqrt hlow) (Real.sqrt_le_sqrt (hhi f))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul hL, Real.sqrt_mul hA]; ring

/-- The low finite-run residual and its unchanged source-order profile give
the physical core precision, with one constant before every run and accuracy.
The analytic Picard producer must prove the two estimates for its actual run. -/
theorem exists_source_plateau_bound_of_profiles
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ halfOpenCell n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SmoothResidual n, ∀ A ε : ℝ, 0 ≤ A →
      ‖smoothResidualToL2 n f‖ ≤ A * ε →
      periodicSobolevNorm (RevisedScales.sourceOrder n) (fun y ↦ f.val y ()) ≤ A →
      ∀ x : Euclidean n, χ x = 1 → ‖periodicLift (fun y ↦ f.val y ()) x‖ ≤ C * A * Real.sqrt ε := by
  obtain ⟨C, hC, hb⟩ := exists_source_plateau_interpolation χ hχ hc hs
  refine ⟨C, hC, ?_⟩
  intro f A ε hA hlo hhi x hx
  calc
    _ ≤ C * Real.sqrt ‖smoothResidualToL2 n f‖ *
        Real.sqrt (periodicSobolevNorm (RevisedScales.sourceOrder n) (fun y ↦ f.val y ())) := hb f x hx
    _ ≤ C * Real.sqrt (A * ε) * Real.sqrt A :=
      mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlo) hC)
        (Real.sqrt_le_sqrt hhi) (Real.sqrt_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))
    _ = _ := by
      rw [Real.sqrt_mul hA]
      calc
        _ = C * (Real.sqrt A * Real.sqrt A) * Real.sqrt ε := by ring
        _ = _ := by rw [Real.mul_self_sqrt hA]

end JanetCartan.PhysicalMean
