module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.InputEstimates
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AuxiliaryAdjoints.Exterior
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Assembly

/-!
# Raw adjoints with the constructed inner exterior

The measured selector proves the physical-slot bounds with its outer cutoff.
The source gap instead supplies an inner exterior. Replacing just the exterior
Sobolev lift retains every image and carrier operator and its original measure.
The application is the same-row source inverse in `MeasuredSourceRaw`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ContinuumInverse
open ContinuumRow CarrierSobolev PeriodicSobolevSpace
open ContinuumCommutator.ImageChannel.Differential
open ContinuumAdjoint.Canonical ContinuumAdjoint.Canonical.AuxiliaryAdjoints

/-- Transfer the measured raw-adjoint bound to a supplied smooth exterior,
retaining the literal physical adjoint. The new constants precede every image
and carrier operator. `NormalizedSelection` supplies the original bound; the
constructed inner cutoff supplies `hψ` (`app:ch_background:prop:bg-adjoint`). -/
theorem exists_augmented_raw_bounds_with_supplied_exterior
    {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : C(Torus n, ℝ)) (hψ : IsSmoothPeriodic ψ)
    (K : ℕ → ℝ) (hK : ∀ s, 0 ≤ K s) :
    ∃ Kinner : ℕ → ℝ, (∀ s, 0 ≤ Kinner s) ∧
      ∀ (image : OutputL2 n →L[ℝ] OutputL2 n)
        (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψouter : C(Torus n, ℝ)),
        (∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
          (augmentedRow image U ψouter).adjoint w ∈ augmentedInputLevel n ι s ∧
          (augmentedInputSobolevScale n ι).gradeNorm s
              ((augmentedRow image U ψouter).adjoint w) ≤
            K s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + ‖w‖)) →
        ∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
          (augmentedRow image U ψ).adjoint w ∈ augmentedInputLevel n ι s ∧
          (augmentedInputSobolevScale n ι).gradeNorm s
              ((augmentedRow image U ψ).adjoint w) ≤
            Kinner s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + ‖w‖) := by
  obtain ⟨Cext, hCext, hext⟩ := exists_exteriorAdjoint_bound ψ hψ
  refine ⟨fun s ↦ K s + Cext s, fun s ↦ add_nonneg (hK s) (hCext s).le, ?_⟩
  intro image U ψouter hraw s
  have hlift : ∀ v : PeriodicSobolevSpace n (Euclidean n) s,
      ∃ u : AugmentedInputSobolevSpace n ι s,
        augmentedInputToL2 s u = (augmentedRow image U ψ).adjoint (toL2 s v) ∧
        ‖u‖ ≤ (K s + Cext s) * (‖v‖ + 1 * ‖toL2 s v‖) := by
    intro v
    obtain ⟨⟨u, hu⟩, hb⟩ := hraw s (toL2 s v) (toL2_mem s v)
    change augmentedInputToL2 s u = _ at hu
    rw [← hu] at hb
    rw [augmentedInputSobolevScale_gradeNorm] at hb
    have hv : (periodicSobolevScale n (Euclidean n)).gradeNorm s (toL2 s v) = ‖v‖ := by
      have hi : inclusion (Nat.le_refl s) v = v := by
        apply toL2_injective s
        exact multiplier_toL2_inclusion _ _
      simpa only [hi] using (multiplier_norm_inclusion_eq_gradeNorm (Nat.le_refl s) v).symm
    rw [hv] at hb
    let ve := exteriorAdjointSobolev ψ hψ s v
    let uinner : AugmentedInputSobolevSpace n ι s := WithLp.toLp 2 (u.fst, ve)
    refine ⟨uinner, ?_, ?_⟩
    · have hphysical := congrArg WithLp.fst hu
      simp only [augmentedInputToL2_apply, augmentedRow_adjoint_apply] at hphysical
      rw [augmentedInputToL2_apply, augmentedRow_adjoint_apply]
      apply congrArg (WithLp.toLp 2)
      change physicalInputToL2 s u.fst = (physicalRow image U).adjoint (toL2 s v) at hphysical
      change (physicalInputToL2 s u.fst, toL2 s ve) = _
      refine Prod.ext hphysical ?_
      exact (toL2_exteriorAdjointSobolev ψ hψ s v).trans
        (congrArg (fun T ↦ T (toL2 s v)) (exteriorChannel_adjoint ψ))
    · have hs : ‖uinner‖ ^ 2 = ‖u.fst‖ ^ 2 + ‖ve‖ ^ 2 :=
        WithLp.prod_norm_sq_eq_of_L2 uinner
      have hle : ‖uinner‖ ≤ ‖u.fst‖ + ‖ve‖ := by
        nlinarith [norm_nonneg uinner, norm_nonneg u.fst, norm_nonneg ve,
          mul_nonneg (norm_nonneg u.fst) (norm_nonneg ve)]
      calc
        ‖uinner‖ ≤ ‖u.fst‖ + ‖ve‖ := hle
        _ ≤ ‖u‖ + Cext s * ‖v‖ := add_le_add (WithLp.norm_fst_le _ u) (hext s v)
        _ ≤ K s * (‖v‖ + ‖toL2 s v‖) + Cext s * ‖v‖ := add_le_add hb le_rfl
        _ ≤ (K s + Cext s) * (‖v‖ + 1 * ‖toL2 s v‖) := by
          nlinarith [mul_nonneg (hCext s).le (norm_nonneg (toL2 s v))]
  intro w hw
  obtain ⟨hm, hb⟩ := augmentedAdjoint_gradeNorm_of_lifts
    (augmentedRow image U ψ) s (K s + Cext s) 1 hlift w hw
  exact ⟨hm, by simpa only [one_mul] using hb⟩

end JanetCartan.ContinuumInverse
