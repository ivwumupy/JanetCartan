module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.ShellGeometry
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.DilatedShellCover

/-!
# Actual nested masks on the retained angular section

The finite angular-cover owner supplies a smooth spacetime angular mask whose
unit carrier lies in the indicated open cone. This leaf constructs its spatial
amplitude mask and one radial threshold. The SAME right multiplier has the
closed frequency margin needed by the signed retarded constructor, and the
spatial mask is one as a germ on its entire closed support.

Consumer: `app:ch_regular_base:lem:retarded-kernel` and the literal upper
endpoint of `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.Characteristic.UniformEvolution
open ConicPhase EvolutionIntegral FiniteMasks
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Z" => RootState (Euclidean d)

/-- Positive dilation of the actual right multiplier retains its angular
carrier, including all cutoff shoulders (`retarded-kernel`). -/
theorem dilatedConicMask_tsupport_subset_fullAngularCone
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) (ε T : ℝ) (b : E → ℝ)
    (hcarrier : tsupport b ∩ sphere (0 : E) 1 ⊆ fullAngularCone ℓ z.2.2 ε T)
    {L : ℝ} (hL : 0 < L) :
    tsupport (dilatedConicMask b L) ⊆ fullAngularCone ℓ z.2.2 ε T := by
  intro ξ hξ
  have hc := dilatedConicMask_tsupport_subset b hL hξ
  have hn : 0 < ‖ξ‖ := hL.trans_le hc.1
  have hd := hcarrier ⟨hc.2, by
    simpa only [mem_sphere, dist_zero_right] using
      NormedSpace.norm_normalize (norm_pos_iff.mp hn)⟩
  simpa only [NormedSpace.norm_smul_normalize] using
    smul_mem_fullAngularCone hn hd

/-- Construct the actual spatial plateau and the right multiplier's closed
frequency inclusion together. The threshold can subsequently be increased
to a common finite-family threshold without changing the spatial mask.
The angular carrier is the fixed geometric input from the finite mask cover;
no nesting or multiplier budget is assumed (`energy-complete-residual`). -/
theorem exists_retained_nested_conicMask
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) {ε T : ℝ} (hε : 0 < ε)
    (b : E → ℝ) (hb : ContDiff ℝ ∞ b)
    (hcarrier : tsupport b ∩ sphere (0 : E) 1 ⊆
      fullAngularCone ℓ z.2.2 (ε / 4) (T / 2)) :
    ∃ (angular : Euclidean d → ℝ) (L : ℝ), 1 ≤ L ∧
      ContDiff ℝ ∞ angular ∧ (∀ η, angular η ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport angular ∧ tsupport angular ⊆ angularCone ℓ z.2.2 (ε / 2) ∧
      (∀ η ∈ tsupport angular, 0 < ℓ η) ∧
      ∀ L' ≥ L,
        ContDiff ℝ ∞ (fun ξ ↦ (dilatedConicMask b L' ξ : ℂ)) ∧
        (0 : E) ∉ tsupport (fun ξ ↦ (dilatedConicMask b L' ξ : ℂ)) ∧
        tsupport (fun ξ ↦ (dilatedConicMask b L' ξ : ℂ)) ⊆
          retainedFrequencyDomain ℓ z ε T (1 / 2) ∧
        ∀ ξ ∈ tsupport (fun ξ ↦ (dilatedConicMask b L' ξ : ℂ)),
          conicMask angular =ᶠ[𝓝 (spatialPart ξ)] (fun _ ↦ 1) := by
  have hc : ∀ ξ ∈ tsupport b ∩ sphere (0 : E) 1,
      spatialPart ξ ∈ angularCone ℓ z.2.2 (ε / 2) := by
    intro ξ hξ
    exact ⟨(hcarrier hξ).1.1, ball_subset_ball (by linarith) (hcarrier hξ).1.2⟩
  obtain ⟨angular, L, hL, ha, har, hac, has, hp⟩ :=
    exists_nested_spatial_conicMask b (isOpen_angularCone ℓ z.2.2 (ε / 2))
      (fun h ↦ ne_zero_of_mem_angularCone h rfl)
      (fun _ hη _ ht ↦ smul_mem_angularCone hη ht) hc
  refine ⟨angular, L, hL, ha, har, hac, has, fun η hη ↦ (has hη).1, ?_⟩
  intro L' hLL
  have hLp : 0 < L' := zero_lt_one.trans_le (hL.trans hLL)
  have hs : tsupport (fun ξ ↦ (dilatedConicMask b L' ξ : ℂ)) ⊆
      tsupport (dilatedConicMask b L') :=
    tsupport_comp_subset Complex.ofReal_zero _
  have hcone := dilatedConicMask_tsupport_subset_fullAngularCone ℓ z
    (ε / 4) (T / 2) b hcarrier hLp
  refine ⟨Complex.ofRealCLM.contDiff.comp (contDiff_dilatedConicMask hb L'),
    fun hz ↦ ne_zero_of_mem_fullAngularCone (hcone (hs hz)) rfl, ?_,
    fun ξ hξ ↦ hp L' hLL ξ (hs hξ)⟩
  intro ξ hξ
  refine ⟨hcone (hs hξ), ?_⟩
  have hval := (hp L' hLL ξ (hs hξ)).eq_of_nhds
  have hnonzero : conicMask angular (spatialPart ξ) ≠ 0 := by rw [hval]; norm_num
  have hnorm := (conicMask_tsupport_subset angular (subset_tsupport _ hnonzero)).1
  change (1 / 2 : ℝ) < ‖spatialPart ξ‖
  linarith

end JanetCartan.RegularSector.Characteristic.UniformEvolution
