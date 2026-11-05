module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Basic

/-!
# The ordinary primary phase as a global smooth representative

`PhysicalPairs.OriginalNegativeRows.geometry` needs a globally smooth phase.
The original finite-menu representative is globally smooth; only its germ on
the source chart is identified with the original ordinary carrier. These
elementary transfers are consumed by the actual original-data application in
`PhaseProfiles.Representative` (`main:eq:primary-strain`,
`app:ch_regular:eq:source-tail` in paper-v2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] public noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles

private theorem spatial_representative_spec {n : ℕ} {G : Type}
    (Z : G → Set (Euclidean 3)) (Φ : G → Euclidean n × Euclidean 3 → ℝ)
    (hΦ : ∀ g, ContDiff ℝ ∞ (Φ g) ∧ HasCompactSupport (Φ g))
    (raw : G → Euclidean 3 → Euclidean n → ℝ) {U S : Set (Euclidean n)}
    (hUS : U ⊆ S)
    (hg : ∀ g v, v ∈ S ×ˢ Z g → Φ g =ᶠ[𝓝 v] fun w ↦ raw g w.2 w.1)
    (g : G) (z : Z g) :
    ContDiff ℝ ∞ (fun x : Euclidean n ↦ Φ g (x, z)) ∧
      ∀ x ∈ U, (fun y : Euclidean n ↦ Φ g (y, z)) =ᶠ[𝓝 x] raw g z := by
  refine ⟨(hΦ g).1.comp (contDiff_id.prodMk contDiff_const), ?_⟩
  intro x hx
  exact (hg g (x, z) ⟨hUS hx, z.property⟩).comp_tendsto
    (continuous_id.prodMk continuous_const).continuousAt

private theorem representative_upper_of_germ {n : ℕ}
    {raw representative : Euclidean n → ℝ} {U : Set (Euclidean n)} {G : ℝ}
    (hg : ∀ x ∈ U, representative =ᶠ[𝓝 x] raw)
    (h : ∀ x ∈ U, ‖fderiv ℝ raw x‖ ≤ G) :
    ∀ x ∈ U, ‖fderiv ℝ representative x‖ ≤ G := by
  intro x hx
  rw [(hg x hx).fderiv_eq]
  exact h x hx

private theorem representative_jets_of_germ {n : ℕ}
    {raw representative : Euclidean n → ℝ} {U : Set (Euclidean n)}
    {P : ℕ → ℝ} {R : ℝ}
    (hg : ∀ x ∈ U, representative =ᶠ[𝓝 x] raw)
    (h : ∀ x ∈ U, ∀ q, ‖iteratedFDeriv ℝ (q + 1) raw x‖ ≤ P q * R ^ q) :
    ∀ x ∈ U, ∀ q, ‖iteratedFDeriv ℝ (q + 1) representative x‖ ≤ P q * R ^ q := by
  intro x hx q
  rw [((hg x hx).iteratedFDeriv ℝ (q + 1)).eq_of_nhds]
  exact h x hx q

private theorem representative_gradient_of_germ {n : ℕ}
    {raw representative : Euclidean n → ℝ} {U K : Set (Euclidean n)}
    (hg : ∀ x ∈ U, representative =ᶠ[𝓝 x] raw)
    (h : ∀ x ∈ U, gradient raw x ∈ K) :
    ∀ x ∈ U, gradient representative x ∈ K := by
  intro x hx
  rw [(hg x hx).gradient_eq]
  exact h x hx

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles
end
