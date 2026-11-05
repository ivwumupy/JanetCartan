module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.Amplitude
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.AmplitudeBudgets.Calculus

/-!
# The normalized carrier shift

The change `(x,y,ε,c) ↦ (x,y,ζ(c)+ε)` in
`app:ch_response:thm:response-literal-transfer`. Its finite jet bound is derived
from primitive carrier jets, for `norm_iteratedFDeriv_normalizedParameterAmplitude_le`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer

/-- Joint variables, including both physical positions, for
`app:ch_response:eq:direct-envelope-profile`. -/
abbrev ParameterAmplitudePoint (n : ℕ) (P : Type*) :=
  (Euclidean n × Euclidean n × Euclidean n) × P

variable {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Normalized carrier substitution of
`app:ch_response:thm:response-literal-transfer`. -/
def carrierAmplitudeShift (ζ : P → Euclidean n) (p : ParameterAmplitudePoint n P) :
    Euclidean n × Euclidean n × Euclidean n :=
  (p.1.1, p.1.2.1, ζ p.2 + p.1.2.2)

namespace ParameterAmplitudeBudget

/-- The selector sees the parameter and normalized covector, retaining all its
jets in `app:ch_response:eq:direct-envelope-profile`. -/
def selectorProjection : ParameterAmplitudePoint n P →L[ℝ] (P × Euclidean n) :=
  (ContinuousLinearMap.snd ℝ _ _).prod
    ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)))

/-- No derivative loss in the selector projection for
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_selectorProjection_le : ‖selectorProjection (n := n) (P := P)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖(p.2, p.1.2.2)‖ ≤ 1 * ‖p‖
  rw [one_mul, Prod.norm_def]
  exact max_le (norm_snd_le p)
    ((norm_snd_le p.1.2).trans ((norm_snd_le p.1).trans (norm_fst_le p)))

private def carrierInjection : Euclidean n →L[ℝ]
    (Euclidean n × Euclidean n × Euclidean n) :=
  (0 : Euclidean n →L[ℝ] Euclidean n).prod
    ((0 : Euclidean n →L[ℝ] Euclidean n).prod (ContinuousLinearMap.id ℝ _))

private theorem norm_carrierInjection_le : ‖carrierInjection (n := n)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [carrierInjection, Prod.norm_def]

/-- Finite regularity of the carrier shift is a consequence of regularity of
`ζ`, not an input about a composed amplitude
(`app:ch_response:thm:response-literal-transfer`). -/
theorem carrierAmplitudeShift_contDiffOn {ζ : P → Euclidean n} {N : ℕ}
    {U : Set (ParameterAmplitudePoint n P)} {C : Set P}
    (hζ : ContDiffOn ℝ N ζ C) (hC : ∀ p ∈ U, p.2 ∈ C) :
    ContDiffOn ℝ N (carrierAmplitudeShift ζ) U := by
  exact contDiffOn_fst.fst.prodMk (contDiffOn_fst.snd.fst.prodMk
    ((hζ.comp contDiffOn_snd hC).add contDiffOn_fst.snd.snd))

/-- Every positive joint jet of the shift is bounded by `1 + Z` if the primitive
carrier jets are bounded by `Z`. Both physical positions are retained; no
frequency occurs (`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_jet_carrierAmplitudeShift_le {ζ : P → Euclidean n} {N k : ℕ}
    {C : Set P} (hC : IsOpen C) (hζ : ContDiffOn ℝ N ζ C)
    (hk : k ≤ N) (hkpos : 1 ≤ k) {p : ParameterAmplitudePoint n P}
    (hp : p.2 ∈ C) {Z : ℝ} (hjet : ‖iteratedFDeriv ℝ k ζ p.2‖ ≤ Z) :
    ‖iteratedFDeriv ℝ k (carrierAmplitudeShift ζ) p‖ ≤ 1 + Z := by
  let L : ParameterAmplitudePoint n P →L[ℝ] P := ContinuousLinearMap.snd ℝ _ _
  let R : ParameterAmplitudePoint n P →L[ℝ]
      (Euclidean n × Euclidean n × Euclidean n) := ContinuousLinearMap.fst ℝ _ _
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u ↦ by simpa [L] using norm_snd_le u)
  have hR : ‖R‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u ↦ by simpa [R] using norm_fst_le u)
  have hζp : ContDiffAt ℝ N (ζ ∘ L) p :=
    (hζ.contDiffAt (hC.mem_nhds hp)).comp p L.contDiff.contDiffAt
  have hJ : ContDiffAt ℝ N (carrierInjection ∘ ζ ∘ L) p :=
    hζp.continuousLinearMap_comp carrierInjection
  have he : carrierAmplitudeShift ζ = fun u ↦ R u + (carrierInjection ∘ ζ ∘ L) u := by
    ext u <;> simp [carrierAmplitudeShift, carrierInjection, R, L, add_comm]
  rw [he, fun_iteratedFDeriv_add_apply R.contDiff.contDiffAt
    (hJ.of_le (by exact_mod_cast hk))]
  apply (norm_add_le _ _).trans (add_le_add (norm_positive_jet_linear_le R hR hkpos p) ?_)
  calc
    _ ≤ ‖carrierInjection (n := n)‖ * ‖iteratedFDeriv ℝ k (ζ ∘ L) p‖ :=
      carrierInjection.norm_iteratedFDeriv_comp_left hζp (by exact_mod_cast hk)
    _ ≤ ‖iteratedFDeriv ℝ k (ζ ∘ L) p‖ :=
      mul_le_of_le_one_left (norm_nonneg _) norm_carrierInjection_le
    _ ≤ ‖iteratedFDeriv ℝ k ζ p.2‖ :=
      norm_jet_comp_contraction_le L hL hC hζ hk hp
    _ ≤ Z := hjet

end ParameterAmplitudeBudget
end JanetCartan.ResponseTransfer
