module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSignedFrames
public import JanetCartan.Iteration.PhysicalPairs.SampledMask
public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Sobolev.LocalJets
/-!
# Spatial profiles of the original ordinary phase

The consumer is the phase input of `PhysicalPairs.SampledMask.first_mask`,
used in the primary strain estimate (`main:eq:primary-strain`) of paper-v2.
A joint smooth representative supplies spatial derivatives of its original
phase germ, without changing the carrier or the source chart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles

/-- A joint representative supplies the unchanged ordinary carrier's spatial
jets on the whole source chart. No normalization or frequency change occurs
(`main:eq:primary-strain`, `app:ch_regular:eq:source-tail`). -/
theorem ordinary_phase_of_joint_germ {n : ℕ} {G : Type}
    (Z : G → Set (Euclidean 3)) (Φ : G → Euclidean n × Euclidean 3 → ℝ)
    (hΦ : ∀ g, ContDiff ℝ ∞ (Φ g) ∧ HasCompactSupport (Φ g))
    (raw : G → Euclidean 3 → Euclidean n → ℝ) {U S : Set (Euclidean n)}
    (hUS : U ⊆ S)
    (hg : ∀ g v, v ∈ S ×ˢ Z g → Φ g =ᶠ[𝓝 v] fun w ↦ raw g w.2 w.1)
    {T : ℝ} (hT : 1 ≤ T) (D : ℕ → ℝ) (hD : ∀ q, 0 ≤ D q)
    (hj : ∀ g v, v ∈ S ×ˢ Z g → ∀ q,
      ‖iteratedFDeriv ℝ q (Φ g) v‖ ≤ D q * T^(q-2))
    (g : G) (z : Z g) :
    ContDiffOn ℝ ∞ (raw g z) U ∧
      ∀ x ∈ U, ‖fderiv ℝ (raw g z) x‖ ≤ D 1 ∧
        ∀ q, ‖iteratedFDeriv ℝ (q+1) (raw g z) x‖ ≤ D (q+1)*T^q := by
  have hs : ContDiff ℝ ∞ (fun x : Euclidean n ↦ Φ g (x,z)) :=
    (hΦ g).1.comp (contDiff_id.prodMk contDiff_const)
  have he x (hx : x ∈ U) : (fun y : Euclidean n ↦ Φ g (y,z)) =ᶠ[𝓝 x] raw g z :=
    (hg g (x,z) ⟨hUS hx,z.property⟩).comp_tendsto
      (continuous_id.prodMk continuous_const).continuousAt
  refine ⟨hs.contDiffOn.congr (fun x hx ↦ (he x hx).eq_of_nhds.symm),?_⟩
  intro x hx
  have bound (q : ℕ) : ‖iteratedFDeriv ℝ (q+1) (raw g z) x‖ ≤ D (q+1)*T^q := by
    rw [← ((he x hx).iteratedFDeriv ℝ (q+1)).eq_of_nhds]
    exact ((ResponsePrimarySources.norm_iteratedFDeriv_primary_spatialSlice_le
      isOpen_univ isOpen_univ (hΦ g).1.contDiffOn (mem_univ x) (mem_univ (z : Euclidean 3))
      (q+1)).trans (hj g (x,z) ⟨hUS hx,z.property⟩ (q+1))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by omega)) (hD _))
  refine ⟨?_,bound⟩
  simpa only [Nat.reduceAdd,norm_iteratedFDeriv_one,pow_zero,mul_one] using bound 0

/-- Increase only the slow coefficient scale, keeping the ordinary phase and
its fixed prehistory profile unchanged (`app:ch_regular:eq:source-tail`). -/
theorem ordinary_phase_jets_mono {n : ℕ} {φ : Euclidean n → ℝ}
    {U : Set (Euclidean n)} {P : ℕ → ℝ} {T R : ℝ}
    (hP : ∀ q, 0 ≤ P q) (hT : 0 ≤ T) (hTR : T ≤ R)
    (hj : ∀ x ∈ U, ∀ q, ‖iteratedFDeriv ℝ (q+1) φ x‖ ≤ P q*T^q) :
    ∀ x ∈ U, ∀ q, ‖iteratedFDeriv ℝ (q+1) φ x‖ ≤ P q*R^q := by
  intro x hx q
  exact (hj x hx q).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT hTR q) (hP q))
end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles
end
