module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.OriginalKernels

/-!
# Auxiliary output-time cutoff from the original physical mask

The compact output carrier inside the selected transport interval constructs
all time-cutoff inputs of `completeResidual_of_selected_physical_chart`.
Source: `app:ch_regular_base:lem:characteristic-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
variable {d : ℕ}
/-- The ORIGINAL compact physical output mask constructs the auxiliary time
plateau used in `completeResidual_of_selected_physical_chart`. Its support
stays inside the same transport interval, and its germ is one on every
output point. Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem exists_outputTime_plateau
    (χout : Euclidean (d + 1) → ℂ) (hc : HasCompactSupport χout)
    {I : Set ℝ} (hI : IsOpen I) (hχI : ∀ x ∈ tsupport χout, x 0 ∈ I) :
    ∃ κ : ℝ → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧ tsupport κ ⊆ I ∧
      ∀ x ∈ tsupport χout, κ =ᶠ[𝓝 (x 0)] fun _ ↦ 1 := by
  let K := (fun x : Euclidean (d + 1) ↦ x 0) '' tsupport χout
  have hK : IsCompact K := hc.isCompact.image (EuclideanSpace.proj 0).continuous
  have hKI : K ⊆ I := by
    rintro t ⟨x, hx, rfl⟩
    exact hχI x hx
  obtain ⟨O, hO, hKO, hOI, hcO⟩ := exists_open_between_and_isCompact_closure hK hI hKI
  obtain ⟨V, hV, hKV, hVO⟩ := normal_exists_closure_subset hK.isClosed hO hKO
  obtain ⟨κ, hκ, _, hsκ, hκone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hO isClosed_closure hVO
  have ht : tsupport κ = closure O := by simp only [tsupport, hsκ]
  refine ⟨κ, hκ, ?_, ?_, ?_⟩
  · change IsCompact (tsupport κ)
    rw [ht]
    exact hcO
  · exact ht.symm ▸ hOI
  · intro x hx
    filter_upwards [hV.mem_nhds (hKV (mem_image_of_mem _ hx))] with t ht
    exact (hκone t).mp (subset_closure ht)

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
