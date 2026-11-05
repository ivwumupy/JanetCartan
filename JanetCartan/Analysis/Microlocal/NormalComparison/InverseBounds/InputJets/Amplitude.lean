module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.Base

/-!
# Spatial jets of the full normal amplitude

The full two-position matrix `a(x,u) a(y,u)*` of
`app:ch_osc:prop:osc-normal`, in the Frobenius norm. Its finite-jet constant is
an explicit binomial convolution multiplied by the norm of a fixed,
dimension-dependent bilinear map; it is independent of the input family.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.NormalComparison

variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

-- Match the topology in operator norms to the chosen Frobenius norm.
local instance (r : ℕ) : TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- The fixed real bilinear outer product with conjugation, with Frobenius
matrix target (`app:ch_osc:prop:osc-normal`). -/
def normalAmplitudeBilinear (r : ℕ) :
    (Fin r → ℂ) →L[ℝ] (Fin r → ℂ) →L[ℝ] Matrix (Fin r) (Fin r) ℂ :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      (LinearMap.mk₂ ℝ (fun a b : Fin r → ℂ ↦
        (fun i j ↦ a i * star (b j) : Matrix _ _ ℂ))
        (by
          intro a b c
          ext i j
          change (a i + b i) * star (c j) = a i * star (c j) + b i * star (c j)
          exact add_mul _ _ _)
        (by
          intro c a b
          ext i j
          change (c • a i) * star (b j) = c • (a i * star (b j))
          exact smul_mul_assoc _ _ _)
        (by
          intro a b c
          ext i j
          change a i * star (b j + c j) = a i * star (b j) + a i * star (c j)
          rw [star_add, mul_add])
        (by
          intro c a b
          ext i j
          change a i * star (c • b j) = c • (a i * star (b j))
          rw [star_smul, star_trivial, mul_smul_comm])))

/-- The bilinear map is the actual matrix product used in the manuscript
(`app:ch_osc:prop:osc-normal`). -/
@[simp] theorem normalAmplitudeBilinear_apply (a b : Fin r → ℂ) (i j : Fin r) :
    normalAmplitudeBilinear r a b i j = a i * star (b j) := rfl

/-- Projection to the left physical position and input variable
(`app:ch_osc:prop:osc-normal`). -/
def normalLeftInput (n : ℕ) :
    (Euclidean n × (Euclidean n × Euclidean n)) →L[ℝ] (Euclidean n × Euclidean n) :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

/-- Projection to the right physical position and input variable
(`app:ch_osc:prop:osc-normal`). -/
def normalRightInput (n : ℕ) :
    (Euclidean n × (Euclidean n × Euclidean n)) →L[ℝ] (Euclidean n × Euclidean n) :=
  ContinuousLinearMap.snd ℝ _ _

/-- The left projection is a contraction (`app:ch_osc:prop:osc-normal`). -/
theorem norm_normalLeftInput_le (n : ℕ) : ‖normalLeftInput n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change max ‖q.1‖ ‖q.2.2‖ ≤ 1 * ‖q‖
  rw [one_mul]
  exact max_le (norm_fst_le q) ((norm_snd_le q.2).trans (norm_snd_le q))

/-- The right projection is a contraction (`app:ch_osc:prop:osc-normal`). -/
theorem norm_normalRightInput_le (n : ℕ) : ‖normalRightInput n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  simpa [normalRightInput] using norm_snd_le q

/-- The dimension-only bilinear operator norm and the finite binomial
convolution give a constant quantified before the family
(`app:ch_osc:prop:osc-normal`). -/
def normalAmplitudeJetBound (r : ℕ) (C : ℕ → ℝ) (k : ℕ) : ℝ :=
  ‖normalAmplitudeBilinear r‖ *
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * |C j| * |C (k - j)|

/-- Nonnegativity of the explicit amplitude bound
(`app:ch_osc:prop:osc-normal`). -/
theorem normalAmplitudeJetBound_nonneg (r : ℕ) (C : ℕ → ℝ) (k : ℕ) :
    0 ≤ normalAmplitudeJetBound r C k := by
  unfold normalAmplitudeJetBound
  positivity

/-- Each of the two position slices inherits the original amplitude jets
without loss (`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.norm_amplitude_comp_linear_le (F : UniformNormalData G C)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : H →L[ℝ] (Euclidean n × Euclidean n)) (hL : ‖L‖ ≤ 1)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {q : H} (hq : L q ∈ G.X ×ˢ G.D)
    {k : ℕ} (hk : k ≤ 20 * (n + 1)) :
    ‖iteratedFDeriv ℝ k (Function.uncurry (F.amplitude ε) ∘ L) q‖ ≤ |C k| := by
  apply (norm_iteratedFDeriv_comp_linear_on_open_le L (G.isOpen_X.prod G.isOpen_D)
    (F.amplitude_contDiffOn_spatial (F.parameter_subset hε)) hq k).trans
  calc
    _ ≤ ‖iteratedFDeriv ℝ k (Function.uncurry (F.amplitude ε)) (L q)‖ * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hL) (norm_nonneg _)
    _ ≤ |C k| := by
      rw [mul_one]
      exact (F.input_jet_bounds hε hq hk).2.1.trans (le_abs_self _)

/-- Joint spatial smoothness of the full matrix amplitude, retaining both
independent physical positions (`app:ch_osc:prop:osc-normal`). -/
theorem UniformNormalData.normalAmplitude_contDiffOn_spatial (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ F.parameterDomain) :
    ContDiffOn ℝ ∞ (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      normalAmplitude (F.amplitude ε) q.1 q.2.1 q.2.2) (G.X ×ˢ (G.X ×ˢ G.D)) := by
  have hl := (F.amplitude_contDiffOn_spatial hε).comp
    (normalLeftInput n).contDiff.contDiffOn (s := G.X ×ˢ (G.X ×ˢ G.D))
    (fun _ hq ↦ ⟨hq.1, hq.2.2⟩)
  have hr := (F.amplitude_contDiffOn_spatial hε).comp
    (normalRightInput n).contDiff.contDiffOn (s := G.X ×ˢ (G.X ×ˢ G.D))
    (fun _ hq ↦ hq.2)
  exact ((normalAmplitudeBilinear r).contDiff.comp_contDiffOn hl).clm_apply hr

/-- Joint smoothness across the parameter endpoints for the actual normal
amplitude (`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.normalAmplitude_contDiffOn_joint (F : UniformNormalData G C) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      normalAmplitude (F.amplitude q.1) q.2.1 q.2.2.1 q.2.2.2)
      (F.parameterDomain ×ˢ (G.X ×ˢ (G.X ×ˢ G.D))) := by
  intro q hq
  have hl : ContDiffAt ℝ ∞ (fun z : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      F.amplitude z.1 z.2.1 z.2.2.2) q :=
    (F.amplitude_contDiffAt hq.1 hq.2.1 hq.2.2.2).comp q
      (contDiffAt_fst.prodMk (contDiffAt_snd.fst.prodMk contDiffAt_snd.snd.snd))
  have hr : ContDiffAt ℝ ∞ (fun z : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      F.amplitude z.1 z.2.2.1 z.2.2.2) q :=
    (F.amplitude_contDiffAt hq.1 hq.2.2.1 hq.2.2.2).comp q
      (contDiffAt_fst.prodMk (contDiffAt_snd.snd.fst.prodMk contDiffAt_snd.snd.snd))
  exact (((normalAmplitudeBilinear r).contDiff.contDiffAt.comp q hl).clm_apply hr).contDiffWithinAt

/-- The parameter derivative of the actual normal amplitude is the sum of
the two differentiated outer products (`app:ch_osc:prop:osc-normal`, Step 2).
The conjugation is already part of the fixed real bilinear map. -/
theorem UniformNormalData.deriv_normalAmplitude (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ F.parameterDomain) {x y u : Euclidean n}
    (hx : x ∈ G.X) (hy : y ∈ G.X) (hu : u ∈ G.D) :
    deriv (fun t ↦ normalAmplitude (F.amplitude t) x y u) ε =
      normalAmplitudeBilinear r (F.amplitude ε x u) (deriv (fun t ↦ F.amplitude t y u) ε) +
      normalAmplitudeBilinear r (deriv (fun t ↦ F.amplitude t x u) ε) (F.amplitude ε y u) := by
  apply ContinuousLinearMap.deriv_of_bilinear (B := normalAmplitudeBilinear r)
    (u := fun t ↦ F.amplitude t x u) (v := fun t ↦ F.amplitude t y u)
  · intro _
    exact ((F.amplitude_contDiffAt hε hx hu).comp ε
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  · intro _
    exact ((F.amplitude_contDiffAt hε hy hu).comp ε
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)

/-- All spatial Frobenius jets of the actual normal amplitude are controlled
by the original finite input sequence, through the entire available order
(`app:ch_osc:prop:osc-normal`). -/
theorem UniformNormalData.norm_iteratedFDeriv_normalAmplitude_le (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {q : Euclidean n × (Euclidean n × Euclidean n)}
    (hq : q ∈ G.X ×ˢ (G.X ×ˢ G.D)) {k : ℕ} (hk : k ≤ 20 * (n + 1)) :
    ‖iteratedFDeriv ℝ k (fun z : Euclidean n × (Euclidean n × Euclidean n) ↦
      normalAmplitude (F.amplitude ε) z.1 z.2.1 z.2.2) q‖ ≤
      normalAmplitudeJetBound r C k := by
  let U := G.X ×ˢ (G.X ×ˢ G.D)
  have hU : IsOpen U := G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D)
  let a := Function.uncurry (F.amplitude ε) ∘ normalLeftInput n
  let b := Function.uncurry (F.amplitude ε) ∘ normalRightInput n
  have hl : ContDiffOn ℝ ∞ a U := (F.amplitude_contDiffOn_spatial (F.parameter_subset hε)).comp
    (normalLeftInput n).contDiff.contDiffOn (fun _ hz ↦ ⟨hz.1, hz.2.2⟩)
  have hr : ContDiffOn ℝ ∞ b U := (F.amplitude_contDiffOn_spatial (F.parameter_subset hε)).comp
    (normalRightInput n).contDiff.contDiffOn (fun _ hz ↦ hz.2)
  have hb := (normalAmplitudeBilinear r).norm_iteratedFDerivWithin_le_of_bilinear
    hl hr hU.uniqueDiffOn hq (n := k) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hU hq] at hb
  refine hb.trans ?_
  unfold normalAmplitudeJetBound
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (normalAmplitudeBilinear r))
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have ha := F.norm_amplitude_comp_linear_le (normalLeftInput n) (norm_normalLeftInput_le n)
    hε ⟨hq.1, hq.2.2⟩ (hjk.trans hk)
  have hb' := F.norm_amplitude_comp_linear_le (normalRightInput n) (norm_normalRightInput_le n)
    hε hq.2 ((Nat.sub_le k j).trans hk)
  exact mul_le_mul (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _)) hb'
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))

end JanetCartan.NormalComparison
