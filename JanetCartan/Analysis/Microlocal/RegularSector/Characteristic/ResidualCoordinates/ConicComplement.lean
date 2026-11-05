module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.ComplementNeighborhood
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.SupportedEndpoint

/-!
# The actual conic off-root inverse

Continue the same selected-minor inverse with degree minus one. Its exact
complement equation uses the normalized oblique projector of the leading
endpoint. The common physical/frequency neighborhood was constructed in
`ComplementNeighborhood`; no complement equation is an input here.
Consumer: `CompleteResidual.completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:complement-symbol` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)
local notation "CMat" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ

/-- Normalize the full covector using the SAME spatial radial coordinate as
the phase and transported matrices. Source: `app:ch_regular_base:eq:complement-inverse`. -/
def normalizeCovector (ℓ : Euclidean d →L[ℝ] ℝ) (ξ : E) : E :=
  (ℓ (spatialPart ξ))⁻¹ • ξ

/-- Degree-minus-one continuation of the literal off-root inverse.
Source: `app:ch_regular_base:eq:complement-inverse`. -/
def conicBminus (ℓ : Euclidean d →L[ℝ] ℝ) (i : Fin (d + 1))
    (Q : E → Fin (d + 1) → Mat) (h : RootState (Euclidean d) → ℝ)
    (r c : Fin (d + 1)) (x ξ : E) : CMat :=
  (ℓ (spatialPart ξ))⁻¹ • bminus i Q h r c x (normalizeCovector ℓ ξ)

/-- Smoothness of the full normalization is asserted only away from its
radial denominator. Source: `app:ch_regular_base:eq:complement-inverse`. -/
theorem contDiffAt_normalizeCovector (ℓ : Euclidean d →L[ℝ] ℝ)
    {ξ : E} (hξ : ℓ (spatialPart ξ) ≠ 0) :
    ContDiffAt ℝ ∞ (normalizeCovector ℓ) ξ :=
  (((ℓ.contDiff.comp (coordinateSplit 0).contDiff.snd).contDiffAt).inv hξ).smul contDiffAt_id

private theorem complexify_smooth :
    ContDiff ℝ ∞ (fun M : Mat ↦ M.map Complex.ofReal) := by
  have he : (fun M : Mat ↦ M.map Complex.ofReal) = fun M ↦
      ∑ j, ∑ k, (M j k : ℂ) • (Matrix.single j k 1 : CMat) := by
    funext M
    ext j k
    simp [Matrix.single, Matrix.sum_apply, ite_and]
  rw [he]
  exact ContDiff.sum fun j _ ↦ ContDiff.sum fun k _ ↦
    (Complex.ofRealCLM.contDiff.comp
      (Matrix.entryLinearMap ℝ ℝ j k).toContinuousLinearMap.contDiff).smul contDiff_const

/-- Joint smoothness of the literal inverse at every point of its actual
open domain. The construction uses the original Frobenius matrix topology.
Source: `app:ch_regular_base:eq:complement-inverse`. -/
theorem contDiffAt_bminus
    (i : Fin (d + 1)) {Ω : Set E} {Q : E → Fin (d + 1) → Mat}
    (hQ : ContDiffOn ℝ ∞ Q Ω) {D : Set (RootState (Euclidean d))} (hD : IsOpen D)
    {h : RootState (Euclidean d) → ℝ} (hh : ContDiffOn ℝ ∞ h D)
    (hmap : ∀ w ∈ D, (coordinateSplit i).symm (w.1, w.2.1) ∈ Ω)
    (r c : Fin (d + 1)) {p : E × E} (hp : p ∈ complementDomain i Q h r c D) :
    ContDiffAt ℝ ∞ (Function.uncurry (bminus i Q h r c)) p := by
  have hopen := isOpen_complementDomain i hQ hD hh hmap r c
  have hc := ((contDiffOn_complementData i hQ hh hmap).mono inter_subset_left).contDiffAt
    (hopen.mem_nhds hp)
  exact complexify_smooth.contDiffAt.comp p
    ((contDiffAt_minorComplementInverse_coefficients r c hp.2.1.1 hp.2.1.2 hp.2.2).comp p hc)

/-- The conic inverse is jointly smooth on the continued actual complement
domain. Source: `app:ch_regular_base:eq:complement-inverse`. -/
theorem contDiffAt_conicBminus
    (ℓ : Euclidean d →L[ℝ] ℝ) (i : Fin (d + 1))
    {Ω : Set E} {Q : E → Fin (d + 1) → Mat} (hQ : ContDiffOn ℝ ∞ Q Ω)
    {D : Set (RootState (Euclidean d))} (hD : IsOpen D)
    {h : RootState (Euclidean d) → ℝ} (hh : ContDiffOn ℝ ∞ h D)
    (hmap : ∀ w ∈ D, (coordinateSplit i).symm (w.1, w.2.1) ∈ Ω)
    (r c : Fin (d + 1)) {p : E × E} (hℓ : ℓ (spatialPart p.2) ≠ 0)
    (hp : (p.1, normalizeCovector ℓ p.2) ∈ complementDomain i Q h r c D) :
    ContDiffAt ℝ ∞ (Function.uncurry (conicBminus ℓ i Q h r c)) p := by
  have hn := (contDiffAt_normalizeCovector ℓ hℓ).comp p contDiffAt_snd
  have hb := (contDiffAt_bminus i hQ hD hh hmap r c hp).comp p
    (contDiffAt_fst.prodMk hn)
  exact (((ℓ.contDiff.comp ((coordinateSplit 0).contDiff.comp
    contDiff_snd).snd).contDiffAt).inv hℓ).smul
      hb

/-- The same conic inverse gives exactly the projector at the normalized
spatial covector. This is the complement equation required by the residual,
including off-root temporal frequencies.
Source: `app:ch_regular_base:eq:complement-symbol`. -/
theorem conicBminus_identity
    (ℓ : Euclidean d →L[ℝ] ℝ) (i : Fin (d + 1))
    (Q : E → Fin (d + 1) → Mat) (h : RootState (Euclidean d) → ℝ)
    (r c : Fin (d + 1)) {D : Set (RootState (Euclidean d))}
    (hroot : ∀ w ∈ D, (rootPencil (coordinateSplit i) Q h w).det = 0)
    {x ξ : E} (hp : (x, normalizeCovector ℓ ξ) ∈ complementDomain i Q h r c D) :
    (∑ a, (ξ a : ℂ) • (coefficient i Q x a).map Complex.ofReal) *
      conicBminus ℓ i Q h r c x ξ =
        1 - projector i Q h r c x ((ℓ (spatialPart ξ))⁻¹ • spatialPart ξ) := by
  have hid := complement_identity_on_domain i Q h r c hroot hp
  have hs : spatialPart (normalizeCovector ℓ ξ) = (ℓ (spatialPart ξ))⁻¹ • spatialPart ξ := by
    exact congrArg Prod.snd ((coordinateSplit 0).map_smul (ℓ (spatialPart ξ))⁻¹ ξ)
  rw [hs] at hid
  rw [← hid, conicBminus, Matrix.mul_smul, ← Matrix.smul_mul]
  congr 1
  ext j k
  simp [normalizeCovector, Matrix.sum_apply, Finset.mul_sum, mul_assoc]

/-- The fixed original right multiplier may be any smooth multiplier whose
normalized support stays in the constructed frequency neighborhood. Its
complement equation then holds on the entire physical neighborhood, even
where the transported source symbol vanishes.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem conicBminus_identity_on_common_support
    (ℓ : Euclidean d →L[ℝ] ℝ) (i : Fin (d + 1))
    (Q : E → Fin (d + 1) → Mat) (h : RootState (Euclidean d) → ℝ)
    (r c : Fin (d + 1)) {D : Set (RootState (Euclidean d))}
    (hroot : ∀ w ∈ D, (rootPencil (coordinateSplit i) Q h w).det = 0)
    {X F : Set E} (hXF : X ×ˢ F ⊆ complementDomain i Q h r c D)
    (β : E → ℂ) (hβ : ∀ ξ ∈ tsupport β, normalizeCovector ℓ ξ ∈ F)
    {x : E} (hx : x ∈ X) (ξ : E) (hξ : β ξ ≠ 0) :
    (∑ a, (ξ a : ℂ) • (coefficient i Q x a).map Complex.ofReal) *
      conicBminus ℓ i Q h r c x ξ =
        1 - projector i Q h r c x ((ℓ (spatialPart ξ))⁻¹ • spatialPart ξ) :=
  conicBminus_identity ℓ i Q h r c hroot (hXF ⟨hx, hβ ξ (subset_tsupport β hξ)⟩)

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
