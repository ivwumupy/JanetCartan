module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedSupport

/-!
# A fixed conic target from the constructed local inverses

The homogeneity step of `app:ch_osc:prop:osc-normal`, Step 4'. The common
local target is extended using output frequency normalization; its defining
set is fixed before the family parameter. The inverse is constructed by the
explicit radial formula, and its right-inverse equation is proved from the
literal transport homogeneity. All positive radii are retained. The compact
comparison sphere is only a normalization section, not a bound on support.
-/

open Set Metric Filter
open scoped ContDiff Topology
@[expose] public noncomputable section
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormalReduction.TransportSymbol ContinuumRow.CanonicalConic
variable {n : ℕ}

/-- A fixed conic target obtained from one fixed local target. It is independent of the scale and density; no varying-image intersection is used (`app:ch_osc:prop:osc-normal`, Step 4'). -/
def normalizedConicTarget (b : ℝ) (Ω : Set (Variables n × Euclidean 2)) :
    Set (Variables n × Euclidean 2) :=
  {q | q.1.2.2 ≠ 0 ∧ normalizeOutputRadius b q ∈ Ω}

/-- Extend the constructed local inverse by positive frequency homogeneity. This is the explicit inverse used on the common conic target (`bg-Psi`). -/
def radialExtensionInverse (b : ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (q : Variables n × Euclidean 2) : ℝ × Euclidean (n - 1) :=
  ((u (normalizeOutputRadius b q)).1,
    (‖q.1.2.2‖ / b) • (u (normalizeOutputRadius b q)).2)

/-- The normalization is jointly smooth off zero output frequency (`bg-mixed-input`). -/
theorem normalizeOutputRadius_contDiffAt (b : ℝ) {q : Variables n × Euclidean 2}
    (hq : q.1.2.2 ≠ 0) : ContDiffAt ℝ ∞ (normalizeOutputRadius b) q := by
  have hn : ContDiffAt ℝ ∞ (fun q : Variables n × Euclidean 2 ↦ ‖q.1.2.2‖) q :=
    contDiffAt_fst.snd.snd.norm ℝ hq
  exact (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.fst.prodMk
    ((contDiffAt_const.div hn (norm_ne_zero_iff.mpr hq)).smul
      contDiffAt_fst.snd.snd))).prodMk contDiffAt_snd

/-- The fixed conic target is open. Inverse continuity is not a premise (`bg-Psi`). -/
theorem normalizedConicTarget_isOpen (b : ℝ) {Ω : Set (Variables n × Euclidean 2)}
    (hΩ : IsOpen Ω) : IsOpen (normalizedConicTarget b Ω) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  exact inter_mem ((isOpen_ne_fun continuous_fst.snd.snd continuous_const).mem_nhds hq.1)
    ((normalizeOutputRadius_contDiffAt b hq.1).continuousAt.preimage_mem_nhds
      (hΩ.mem_nhds hq.2))

/-- The common target is genuinely conic; no finite radial support restriction occurs (`bg-Psi`). -/
theorem normalizedConicTarget_smul_iff (b : ℝ) (Ω : Set (Variables n × Euclidean 2))
    (q : Variables n × Euclidean 2) {t : ℝ} (ht : 0 < t) :
    (scaleFrequency t q.1, q.2) ∈ normalizedConicTarget b Ω ↔
      q ∈ normalizedConicTarget b Ω := by
  change (t • q.1.2.2 ≠ 0 ∧ _) ↔ _
  rw [normalizeOutputRadius_scale b q ht]
  exact and_congr ⟨fun h ↦ (smul_ne_zero_iff.mp h).2,
    fun h ↦ smul_ne_zero ht.ne' h⟩ Iff.rfl

/-- Joint smoothness of the radial extension follows from the constructed local inverse (`app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem radialExtensionInverse_smooth (b : ℝ)
    {u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {Ω : Set (Variables n × Euclidean 2)} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ ∞ u Ω) :
    ContDiffOn ℝ ∞ (radialExtensionInverse b u) (normalizedConicTarget b Ω) := by
  intro q hq
  have hv := (hu.contDiffAt (hΩ.mem_nhds hq.2)).comp q
    (normalizeOutputRadius_contDiffAt b hq.1)
  have hn : ContDiffAt ℝ ∞ (fun q : Variables n × Euclidean 2 ↦ ‖q.1.2.2‖) q :=
    contDiffAt_fst.snd.snd.norm ℝ hq.1
  exact (hv.fst.prodMk ((hn.div_const b).smul hv.snd)).contDiffWithinAt

/-- The radial extension is an actual right inverse of the SAME transport map. The proof uses `transportAveragedGradient_smul`, rather than assuming an inverse identity on the cone (`bg-Psi`). -/
theorem radialExtensionInverse_right_inverse {b : ℝ} (hb : 0 < b)
    {Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {Ω : Set (Variables n × Euclidean 2)}
    (hu : ∀ q ∈ Ω, transportAveragedGradient Y (inverseCoordinates u q) = q.1.2.2)
    {q : Variables n × Euclidean 2} (hq : q ∈ normalizedConicTarget b Ω) :
    transportAveragedGradient Y (inverseCoordinates (radialExtensionInverse b u) q) =
      q.1.2.2 := by
  change transportAveragedGradient Y
    (scaleInput (‖q.1.2.2‖ / b) (inverseCoordinates u (normalizeOutputRadius b q))) = _
  rw [transportAveragedGradient_smul, hu _ hq.2]
  change (‖q.1.2.2‖ / b) • ((b / ‖q.1.2.2‖) • q.1.2.2) = _
  rw [smul_smul, div_mul_div_cancel₀ hb.ne', div_self (norm_ne_zero_iff.mpr hq.1), one_smul]

/-- The incidence coordinate has degree zero and the inverse covector degree one on the uncut frequency range (`bg-Psi`, `bg-symbol`). -/
theorem radialExtensionInverse_smul (b : ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (q : Variables n × Euclidean 2) {t : ℝ} (ht : 0 < t) :
    radialExtensionInverse b u (scaleFrequency t q.1, q.2) =
      ((radialExtensionInverse b u q).1, t • (radialExtensionInverse b u q).2) := by
  unfold radialExtensionInverse
  rw [normalizeOutputRadius_scale b q ht]
  simp only [scaleFrequency, norm_smul, Real.norm_eq_abs, abs_of_pos ht, smul_smul]
  rw [mul_div_assoc]

/-- The extension retains the local inverse exactly on the comparison sphere, so its compact range buffer is inherited (`app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem radialExtensionInverse_eq_on_sphere {b : ℝ} (hb : 0 < b)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    {q : Variables n × Euclidean 2} (hq : ‖q.1.2.2‖ = b) :
    radialExtensionInverse b u q = u q := by
  simp [radialExtensionInverse, normalizeOutputRadius_eq_self hb hq, hq, hb.ne']
/-- On the original support, the conic inverse recovers the original input.
Both the normalized input and the constructed local inverse lie in the
compact injectivity set. The two range facts are outputs of the mask and
local-inverse constructions, respectively (`bg-full-complex-amplitude`). -/
theorem radialExtensionInverse_left_inverse {b : ℝ} (hb : 0 < b)
    {Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hi : InjOn (augmentedTransportGradient Y) K)
    (hrange : MapsTo (inverseCoordinates u) Q K) (hQΩ : Q ⊆ Ω)
    (hu : ∀ q ∈ Ω, transportAveragedGradient Y (inverseCoordinates u q) = q.1.2.2)
    {p : InputVariables n} (hne : transportAveragedGradient Y p ≠ 0)
    (hQ : normalizeOutputRadius b (augmentedTransportGradient Y p) ∈ Q)
    (hK : scaleInput (b / ‖transportAveragedGradient Y p‖) p ∈ K) :
    inverseCoordinates (radialExtensionInverse b u) (augmentedTransportGradient Y p) = p := by
  let q := augmentedTransportGradient Y p
  let t := b / ‖q.1.2.2‖
  have hforward : augmentedTransportGradient Y (scaleInput t p) = normalizeOutputRadius b q :=
    augmentedTransportGradient_scaleInput Y t p
  have hlocal : inverseCoordinates u (normalizeOutputRadius b q) = scaleInput t p := by
    apply hi (hrange hQ) hK
    exact (augmentedTransportGradient_inverseCoordinates Y u hu (hQΩ hQ)).trans hforward.symm
  change scaleInput (‖q.1.2.2‖ / b) (inverseCoordinates u (normalizeOutputRadius b q)) = p
  rw [hlocal]
  have hcancel : (‖q.1.2.2‖ / b) * t = 1 := by
    dsimp [t]
    rw [div_mul_div_cancel₀ hb.ne']
    exact div_self (norm_ne_zero_iff.mpr hne)
  simp only [scaleInput, smul_smul, hcancel, one_smul]

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
