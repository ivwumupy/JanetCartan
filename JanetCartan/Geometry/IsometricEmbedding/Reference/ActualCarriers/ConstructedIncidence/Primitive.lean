module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedIncidence.FirstJet

/-!
# Primitive jets on an incidence cylinder

Restriction to the first patch coordinate is contractive in the shared
product norms. Thus primitive frame and joint carrier-gradient errors control
the entire input first jet of the polynomial incidence coefficient
(`app:ch_seed:prop:seed-actual-menu`, Step 3).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers

variable {n : ℕ}

/-- Linear part of the physical-point/parameter restriction to an incidence
cylinder (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
def incidenceLiftLinear : ((Euclidean n × Euclidean n) × ℝ) →L[ℝ]
    Euclidean n × Euclidean 3 :=
  ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((ContinuousLinearMap.snd ℝ _ _).smulRight (EuclideanSpace.single 0 1))

/-- The distinguished scalar direction has unit Euclidean length, so the
joint restriction is contractive (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem norm_incidenceLiftLinear_apply_le (v : (Euclidean n × Euclidean n) × ℝ) :
    ‖incidenceLiftLinear v‖ ≤ ‖v‖ := by
  change ‖(v.1.1, v.2 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))‖ ≤ ‖v‖
  have he : ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = 1 := by
    simp [EuclideanSpace.single, PiLp.norm_single]
  simp only [Prod.norm_def, norm_smul, he, mul_one]
  exact max_le (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)

/-- Joint derivative of the affine cylinder restriction, retaining the
physical variable (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem hasFDerivAt_incidenceLift (z : Euclidean 3)
    (p : (Euclidean n × Euclidean n) × ℝ) :
    HasFDerivAt (fun w : (Euclidean n × Euclidean n) × ℝ ↦
      (w.1.1, incidenceParameter z w.2)) incidenceLiftLinear p := by
  exact ((hasFDerivAt_fst (p := p)).fst).prodMk
    (((hasFDerivAt_snd (p := p)).smul_const (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))).const_add z)

/-- The literal primitive input of determinant incidence. Here `G` is the
joint physical gradient of a carrier (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
def incidencePrimitive (Q : Euclidean n → Fin n → MetricTensor n)
    (G : Euclidean n × Euclidean 3 → Euclidean n) (z : Euclidean 3)
    (p : (Euclidean n × Euclidean n) × ℝ) :
    ((Fin n → MetricTensor n) × Euclidean n) × Euclidean n :=
  ((Q p.1.1, G (p.1.1, incidenceParameter z p.2)), p.1.2)

/-- Smooth primitive frame and carrier maps give joint smooth incidence
inputs on each cylinder (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem contDiffAt_incidencePrimitive
    {Q : Euclidean n → Fin n → MetricTensor n}
    {G : Euclidean n × Euclidean 3 → Euclidean n} {z : Euclidean 3}
    {p : (Euclidean n × Euclidean n) × ℝ}
    (hQ : ContDiffAt ℝ ∞ Q p.1.1)
    (hG : ContDiffAt ℝ ∞ G (p.1.1, incidenceParameter z p.2)) :
    ContDiffAt ℝ ∞ (incidencePrimitive Q G z) p := by
  exact ((hQ.comp p contDiffAt_fst.fst).prodMk
    (hG.comp p (contDiffAt_fst.fst.prodMk
      (contDiffAt_const.add (contDiffAt_snd.smul contDiffAt_const))))).prodMk
        contDiffAt_fst.snd

/-- Full derivative of the primitive input, before applying the determinant
polynomial (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem hasFDerivAt_incidencePrimitive
    {Q : Euclidean n → Fin n → MetricTensor n}
    {G : Euclidean n × Euclidean 3 → Euclidean n} {z : Euclidean 3}
    {p : (Euclidean n × Euclidean n) × ℝ}
    (hQ : DifferentiableAt ℝ Q p.1.1)
    (hG : DifferentiableAt ℝ G (p.1.1, incidenceParameter z p.2)) :
    HasFDerivAt (incidencePrimitive Q G z)
      (((fderiv ℝ Q p.1.1).comp
        ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _))).prod
        ((fderiv ℝ G (p.1.1, incidenceParameter z p.2)).comp incidenceLiftLinear) |>.prod
          ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _))) p := by
  exact ((hQ.hasFDerivAt.comp p (hasFDerivAt_fst.fst)).prodMk
    (hG.hasFDerivAt.comp p (hasFDerivAt_incidenceLift z p))).prodMk hasFDerivAt_fst.snd

/-- Separate frame and joint gradient first-jet bounds give the full
primitive incidence first-jet bound with no loss of constant. This is used
only with the actual estimates constructed from frame `C⁶` closeness
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem incidencePrimitive_firstJet_comparison
    {Q Q₀ : Euclidean n → Fin n → MetricTensor n}
    {G G₀ : Euclidean n × Euclidean 3 → Euclidean n} {z : Euclidean 3}
    {p : (Euclidean n × Euclidean n) × ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hQ : DifferentiableAt ℝ Q p.1.1) (hQ₀ : DifferentiableAt ℝ Q₀ p.1.1)
    (hG : DifferentiableAt ℝ G (p.1.1, incidenceParameter z p.2))
    (hG₀ : DifferentiableAt ℝ G₀ (p.1.1, incidenceParameter z p.2))
    (hvQ : ‖Q p.1.1 - Q₀ p.1.1‖ ≤ δ)
    (hvG : ‖G (p.1.1, incidenceParameter z p.2) - G₀ (p.1.1, incidenceParameter z p.2)‖ ≤ δ)
    (hdQ : ‖fderiv ℝ Q p.1.1 - fderiv ℝ Q₀ p.1.1‖ ≤ δ)
    (hdG : ‖fderiv ℝ G (p.1.1, incidenceParameter z p.2) -
      fderiv ℝ G₀ (p.1.1, incidenceParameter z p.2)‖ ≤ δ) :
    ‖incidencePrimitive Q G z p - incidencePrimitive Q₀ G₀ z p‖ ≤ δ ∧
    ‖fderiv ℝ (incidencePrimitive Q G z) p -
      fderiv ℝ (incidencePrimitive Q₀ G₀ z) p‖ ≤ δ := by
  constructor
  · simpa only [incidencePrimitive, Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero,
      max_le_iff] using And.intro (And.intro hvQ hvG) hδ
  · rw [(hasFDerivAt_incidencePrimitive hQ hG).fderiv,
      (hasFDerivAt_incidencePrimitive hQ₀ hG₀).fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ hδ
    intro v
    have h₁ := (fderiv ℝ Q p.1.1 - fderiv ℝ Q₀ p.1.1).le_opNorm v.1.1
    have h₂ := (fderiv ℝ G (p.1.1, incidenceParameter z p.2) -
      fderiv ℝ G₀ (p.1.1, incidenceParameter z p.2)).le_opNorm (incidenceLiftLinear v)
    have hb₁ := h₁.trans (mul_le_mul hdQ ((norm_fst_le v.1).trans (norm_fst_le v))
      (norm_nonneg _) hδ)
    have hb₂ := h₂.trans (mul_le_mul hdG (norm_incidenceLiftLinear_apply_le v)
      (norm_nonneg _) hδ)
    change ‖((_, _), v.1.2 - v.1.2)‖ ≤ _
    simp only [sub_self, Prod.norm_def, norm_zero, max_le_iff]
    exact ⟨⟨hb₁, hb₂⟩, mul_nonneg hδ (norm_nonneg v)⟩

end JanetCartan.ActualCarriers
