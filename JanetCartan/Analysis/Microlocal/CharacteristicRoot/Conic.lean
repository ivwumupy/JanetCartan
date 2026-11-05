module

public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.Patch

/-!
# Positive homogeneous extension of a scalar root

The conic continuation in `app:ch_seed:prop:seed-actual-menu`. A positive linear
coordinate on the transverse covectors gives a smooth angular section. Extending
an implicit-function branch from this section preserves its exact root equation
and uniqueness. The final assembly constructs the section branch from the symbol.
-/

@[expose] public noncomputable section

open Set
open scoped Topology ContDiff

namespace JanetCartan.CharacteristicRoot

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Angular normalization in a pointed transverse chart
(`app:ch_response:thm:response-compatible-choice`). -/
def normalize (ℓ : E →L[ℝ] ℝ) (p : X × E) : X × E :=
  (p.1, (ℓ p.2)⁻¹ • p.2)

/-- The open conic extension of an angular parameter patch.
(`app:ch_seed:prop:seed-actual-menu`). -/
def conicDomain (ℓ : E →L[ℝ] ℝ) (U : Set (X × E)) : Set (X × E) :=
  {p | 0 < ℓ p.2 ∧ normalize ℓ p ∈ U}

/-- Positive degree-one continuation from an angular section
(`app:ch_seed:prop:seed-actual-menu`). -/
def homogeneousExtension (ℓ : E →L[ℝ] ℝ) (H : X × E → ℝ) (p : X × E) : ℝ :=
  ℓ p.2 * H (normalize ℓ p)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- Normalization is unchanged by positive rescaling.
(`app:ch_seed:prop:seed-actual-menu`). -/
theorem normalize_smul (ℓ : E →L[ℝ] ℝ) (p : X × E) {r : ℝ} (hr : r ≠ 0) :
    normalize ℓ (p.1, r • p.2) = normalize ℓ p := by
  simp only [normalize, map_smul, smul_eq_mul, mul_inv_rev, smul_smul]
  congr 2
  rw [mul_assoc, inv_mul_cancel₀ hr, mul_one]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- The extension is positively homogeneous, including away from its root patch.
(`app:ch_seed:prop:seed-actual-menu`). -/
theorem homogeneousExtension_smul (ℓ : E →L[ℝ] ℝ) (H : X × E → ℝ)
    (p : X × E) {r : ℝ} (hr : 0 < r) :
    homogeneousExtension ℓ H (p.1, r • p.2) = r * homogeneousExtension ℓ H p := by
  simp only [homogeneousExtension, normalize_smul ℓ p hr.ne', map_smul, smul_eq_mul,
    mul_assoc]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- The constructed domain is stable under every positive covector dilation.
(`app:ch_seed:prop:seed-actual-menu`). -/
theorem mem_conicDomain_smul (ℓ : E →L[ℝ] ℝ) (U : Set (X × E))
    {p : X × E} (hp : p ∈ conicDomain ℓ U) {r : ℝ} (hr : 0 < r) :
    (p.1, r • p.2) ∈ conicDomain ℓ U := by
  refine ⟨?_, ?_⟩
  · simpa only [map_smul, smul_eq_mul] using mul_pos hr hp.1
  · simpa only [normalize_smul ℓ p hr.ne'] using hp.2

/-- Smoothness of angular normalization on the positive coordinate chart.
(`app:ch_seed:prop:seed-actual-menu`). -/
theorem contDiffAt_normalize (ℓ : E →L[ℝ] ℝ) {p : X × E} (hp : ℓ p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (normalize ℓ) p := by
  exact contDiffAt_fst.prodMk
    (((ℓ.contDiff.contDiffAt.comp p contDiffAt_snd).inv hp).smul contDiffAt_snd)

/-- A conic extension of an open angular patch is open.
(`app:ch_seed:prop:seed-actual-menu`). -/
theorem isOpen_conicDomain (ℓ : E →L[ℝ] ℝ) {U : Set (X × E)} (hU : IsOpen U) :
    IsOpen (conicDomain ℓ U) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  exact Filter.inter_mem
    (((ℓ.continuous.comp continuous_snd).isOpen_preimage _ isOpen_Ioi).mem_nhds hp.1)
    ((contDiffAt_normalize ℓ hp.1.ne').continuousAt.preimage_mem_nhds (hU.mem_nhds hp.2))

/-- A smooth angular branch has a smooth homogeneous extension on its conic domain.
(`app:ch_seed:prop:seed-actual-menu`). -/
theorem contDiffOn_homogeneousExtension (ℓ : E →L[ℝ] ℝ) {H : X × E → ℝ}
    {U : Set (X × E)} (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) :
    ContDiffOn ℝ ∞ (homogeneousExtension ℓ H) (conicDomain ℓ U) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  exact (ℓ.contDiff.contDiffAt.comp p contDiffAt_snd).mul
    ((hH.contDiffAt (hU.mem_nhds hp.2)).comp p (contDiffAt_normalize ℓ hp.1.ne'))

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- The exact characteristic equation survives homogeneous extension. The only
symbol assumption is its stated degree-one homogeneity.
(`app:ch_seed:prop:seed-actual-menu`). -/
theorem homogeneousExtension_zero (ℓ : E →L[ℝ] ℝ)
    {f : (X × E) × ℝ → ℝ} {H : X × E → ℝ} {U : Set (X × E)}
    (hf : ∀ (x : X) (η : E) (τ : ℝ) (r : ℝ), 0 < r →
      f ((x, r • η), r * τ) = r * f ((x, η), τ))
    (hH : ∀ q ∈ U, f (q, H q) = 0) {p : X × E} (hp : p ∈ conicDomain ℓ U) :
    f (p, homogeneousExtension ℓ H p) = 0 := by
  have he := hf p.1 ((ℓ p.2)⁻¹ • p.2) (H (normalize ℓ p)) (ℓ p.2) hp.1
  have hz : f ((p.1, (ℓ p.2)⁻¹ • p.2), H (normalize ℓ p)) = 0 := hH _ hp.2
  simpa only [smul_inv_smul₀ hp.1.ne', hz, mul_zero, Prod.eta,
    homogeneousExtension] using he

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- Uniqueness in the conic scalar band follows from angular uniqueness.
The scalar band is explicitly normalized, so no global uniqueness is claimed.
(`app:ch_seed:prop:seed-actual-menu`). -/
theorem homogeneousExtension_unique (ℓ : E →L[ℝ] ℝ)
    {f : (X × E) × ℝ → ℝ} {H : X × E → ℝ} {U : Set (X × E)} {V : Set ℝ}
    (hf : ∀ (x : X) (η : E) (τ : ℝ) (r : ℝ), 0 < r →
      f ((x, r • η), r * τ) = r * f ((x, η), τ))
    (hH : ∀ q ∈ U, ∀ τ ∈ V, f (q, τ) = 0 ↔ H q = τ)
    {p : X × E} (hp : p ∈ conicDomain ℓ U) {τ : ℝ} (hτ : τ / ℓ p.2 ∈ V) :
    f (p, τ) = 0 ↔ homogeneousExtension ℓ H p = τ := by
  have he := hf p.1 ((ℓ p.2)⁻¹ • p.2) (τ / ℓ p.2) (ℓ p.2) hp.1
  have hscale : ℓ p.2 * (τ / ℓ p.2) = τ := mul_div_cancel₀ τ hp.1.ne'
  simp only [smul_inv_smul₀ hp.1.ne', hscale, Prod.eta] at he
  rw [he, mul_eq_zero, or_iff_right hp.1.ne']
  change f (normalize ℓ p, τ / ℓ p.2) = 0 ↔ ℓ p.2 * H (normalize ℓ p) = τ
  rw [hH _ hp.2 _ hτ, eq_div_iff hp.1.ne', mul_comm]

end JanetCartan.CharacteristicRoot
