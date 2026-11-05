module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer

/-!
# Weak first output derivatives

The gain-one paragraph following `app:ch_regular_base:eq:graph-derivative-transfer`.
Only primitive smoothness, compact carriers, and distributional realizations are
inputs. The consumer is `jc-deduce-fio-strong-sobolev`; its realization producers
must supply the initial operator and each actual first output amplitude.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory LineDeriv
open scoped Topology ContDiff SchwartzMap Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- Frequency regularization commutes with the first forward output amplitude.
Source: gain one after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphFirstOutputAmplitude_frequencyCutFullAmplitude
    (S : E → E → ℝ) (χ : E → ℂ) (A : FullAmplitude n r) (i : Fin n) :
    graphFirstOutputAmplitude S (frequencyCutFullAmplitude χ A) i =
      frequencyCutFullAmplitude χ (graphFirstOutputAmplitude S A i) := by
  funext x y η
  have hd := congrArg (fun L : E →L[ℝ] Matrix (Fin r) (Fin r) ℂ ↦
    L (EuclideanSpace.single i 1))
    (congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := fun z ↦ A z y η) (χ η)) x)
  simp only [graphFirstOutputAmplitude, frequencyCutFullAmplitude, smul_add]
  change _ + _ = _ + _
  rw [show partialDeriv (fun z ↦ χ η • A z y η) x i =
    χ η • partialDeriv (fun z ↦ A z y η) x i from hd]
  rw [smul_comm (Complex.I * _) (χ η)]

/-- Differentiate the compact-frequency integral itself, with its physical
normalization and full masks. Source: gain one in Step 3 of
`app:ch_regular_base:thm:actual-calculus`. -/
theorem ForwardRegularized.partialDeriv_graphOperator_firstOutput
    {X Y F : Set E} {S : E → E → ℝ} {A : FullAmplitude n r}
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    {u : E → Fin r → ℂ} (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    {K : Set E} (hK : IsCompact K) (hAK : ∀ x y η, η ∉ K → A x y η = 0)
    (x : E) (i : Fin n) :
    partialDeriv (graphOperator S A u) x i =
      graphOperator S (graphFirstOutputAmplitude S A i) u x := by
  rw [partialDeriv_graphOperator_integral hA hF hF0 hS hu hus hK hAK x i]
  apply congrArg (((2 * Real.pi) ^ n : ℂ)⁻¹ • ·)
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hη : η = 0
  · subst η
    have ha (z y) : A z y 0 = 0 := hA.support z y 0 (Or.inr (Or.inr hF0))
    simp [integrand, graphFirstOutputAmplitude, ha, partialDeriv]
  · exact partialDeriv_integrand x y η i
      (((hS x η hη).comp x (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
        (by simp))
      ((hA.smooth.comp (contDiff_id.prodMk (contDiff_const.prodMk contDiff_const))).differentiable
        (by simp) x)

private theorem forward_firstOutput_pairing_coordinates
    {X Y F : Set E} {S : E → E → ℝ} {A : FullAmplitude n r}
    (hA : ForwardAmplitudeAdmissible X Y F A) (hX : IsCompact X)
    (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    {u : E → Fin r → ℂ} (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    {K : Set E} (hK : IsCompact K) (hAK : ∀ x y η, η ∉ K → A x y η = 0)
    (φ : E → ℂ) (hφ : ContDiff ℝ ∞ φ) (i : Fin n) :
    (∫ x, partialDeriv φ x i • graphOperator S A u x) =
      -(∫ x, φ x • graphOperator S (graphFirstOutputAmplitude S A i) u x) := by
  have hg := ForwardRegularized.smooth_graphOperator hA hF hF0 hS hu hus hK hAK
  have hgs := ForwardRegularized.compactSupport_graphOperator (S := S) (u := u) hA hX
  have hi : Integrable (fun x ↦ φ x • graphOperator S A u x) :=
    (hφ.continuous.smul hg.continuous).integrable_of_hasCompactSupport hgs.smul_left
  have hiφ : Integrable (fun x ↦ partialDeriv φ x i • graphOperator S A u x) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).smul
      hg.continuous).integrable_of_hasCompactSupport hgs.smul_left
  have hig : Integrable (fun x ↦ φ x • partialDeriv (graphOperator S A u) x i) :=
    (hφ.continuous.smul ((hg.continuous_fderiv (by simp)).clm_apply
      continuous_const)).integrable_of_hasCompactSupport
        (hgs.fderiv_apply ℝ (EuclideanSpace.single i 1)).smul_left
  have hb := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hiφ hig hi
    (fun x _ ↦ hφ.differentiable (by simp) x) (fun x _ ↦ hg.differentiable (by simp) x)
  have hw : (∫ x, partialDeriv φ x i • graphOperator S A u x) =
      -(∫ x, φ x • partialDeriv (graphOperator S A u) x i) := by
    simpa only [partialDeriv, neg_neg] using congrArg Neg.neg hb.symm
  simpa only [ForwardRegularized.partialDeriv_graphOperator_firstOutput
    hA hF hF0 hS hu hus hK hAK] using hw

/-- Actual compact-frequency output integration by parts in the complex Hilbert
fiber. Source: gain one following `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graphOperator_frequencyCut_firstOutput_weak_pairing
    {X Y F : Set E} {S : E → E → ℝ} {A : FullAmplitude n r}
    (hA : ForwardAmplitudeAdmissible X Y F A) (hX : IsCompact X)
    (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (i : Fin n) (u : graphTestSpace n r) (φ : 𝓢(E, ℂ)) :
    (∫ x, partialDeriv φ x i • WithLp.toLp 2
      (graphOperator S (frequencyCutFullAmplitude χ A) (fun y ↦ (u.val y).ofLp) x)) =
      -(∫ x, φ x • WithLp.toLp 2
        (graphOperator S (frequencyCutFullAmplitude χ (graphFirstOutputAmplitude S A i))
          (fun y ↦ (u.val y).ofLp) x)) := by
  let L := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
  let Lr := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)
  have hu : ContDiff ℝ ∞ (fun y ↦ (u.val y).ofLp) := Lr.contDiff.comp u.property.1
  have hus : HasCompactSupport (fun y ↦ (u.val y).ofLp) :=
    u.property.2.comp_left Lr.map_zero
  have hcut : ∀ x y η, η ∉ tsupport χ → frequencyCutFullAmplitude χ A x y η = 0 := by
    intro x y η hη
    simp [frequencyCutFullAmplitude, image_eq_zero_of_notMem_tsupport hη]
  have hw := forward_firstOutput_pairing_coordinates (hA.frequencyCut hχ)
    hX hF hF0 hS hu hus hχs hcut φ (φ.smooth ⊤) i
  rw [graphFirstOutputAmplitude_frequencyCutFullAmplitude] at hw
  have he := congrArg L.symm hw
  simp only [map_neg] at he
  simp_rw [← L.symm.integral_comp_comm] at he
  simp only [map_smul] at he
  simpa only [L, PiLp.coe_symm_continuousLinearEquiv] using he

private theorem firstOutput_limit
    (K : FullAmplitude n r → (E → Fin r → ℂ) → E → Fin r → ℂ)
    (χ : ℕ → E → ℂ) (A B : FullAmplitude n r) (T U : H →L[ℂ] H)
    (hT : GraphDistributionalRealization K χ A T)
    (hU : GraphDistributionalRealization K χ B U)
    (u : graphTestSpace n r) (i : Fin n)
    (hpair : ∀ k (φ : 𝓢(E, ℂ)),
      (∫ x, partialDeriv φ x i • WithLp.toLp 2
        (K (frequencyCutFullAmplitude (χ k) A) (fun y ↦ (u.val y).ofLp) x)) =
      -(∫ x, φ x • WithLp.toLp 2
        (K (frequencyCutFullAmplitude (χ k) B) (fun y ↦ (u.val y).ofLp) x))) :
    lineDerivOp (EuclideanSpace.single i (1 : ℝ))
      (T (graphTestToLp u) : 𝓢'(E, V)) = (U (graphTestToLp u) : 𝓢'(E, V)) := by
  ext φ : 1
  have hl := hT u (lineDerivOp (EuclideanSpace.single i (1 : ℝ)) φ)
  have heq := tendsto_nhds_unique hl ((hU u φ).neg.congr (fun k ↦ by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, partialDeriv] using (hpair k φ).symm))
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg]
  exact neg_eq_iff_eq_neg.mpr heq

/-- Weak first output derivative of the forward graph, proved by compact-frequency
integration by parts and distributional limits. The two realization inputs are
owed by the graph realization producer, not derivative identities.
Source: gain one after `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graph_realization_weak_firstOutput
    {X Y F : Set E} {S : E → E → ℝ} {A : FullAmplitude n r}
    (hA : ForwardAmplitudeAdmissible X Y F A) (hX : IsCompact X)
    (hF : IsClosed F) (hF0 : (0 : E) ∉ F)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (χ : ℕ → E → ℂ) (hχ : ∀ k, ContDiff ℝ ∞ (χ k))
    (hχs : ∀ k, HasCompactSupport (χ k)) (i : Fin n) (T U : H →L[ℂ] H)
    (hT : GraphDistributionalRealization (graphOperator S) χ A T)
    (hU : GraphDistributionalRealization (graphOperator S) χ (graphFirstOutputAmplitude S A i) U)
    (u : graphTestSpace n r) :
    lineDerivOp (EuclideanSpace.single i (1 : ℝ))
      (T (graphTestToLp u) : 𝓢'(E, V)) = (U (graphTestToLp u) : 𝓢'(E, V)) :=
  firstOutput_limit _ χ A _ T U hT hU u i (fun k φ ↦
    graphOperator_frequencyCut_firstOutput_weak_pairing hA hX hF hF0 hS
      (χ k) (hχ k) (hχs k) i u φ)

/-- Weak first output derivative of the supplied literal Hilbert adjoint, with
original coordinate order and exactly once conjugated regularizers. No weighted
reverse graph replaces the adjoint. Source: gain one in Step 3 of
`app:ch_regular_base:thm:actual-calculus`. -/
theorem adjointGraph_realization_weak_firstOutput
    {K : Set (E × E)} {S : E → E → ℝ} {A : FullAmplitude n r}
    (hA : ReverseAmplitudeAdmissible K A) (hK : IsCompact K)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (χ : ℕ → E → ℂ) (hχ : ∀ k, ContDiff ℝ ∞ (χ k))
    (hχs : ∀ k, HasCompactSupport (χ k)) (hχ0 : ∀ k, (0 : E) ∉ tsupport (χ k))
    (i : Fin n) (T U : H →L[ℂ] H)
    (hT : GraphDistributionalRealization (reverseGraphOperator S)
      (fun k η ↦ star (χ k η)) (fun x y η ↦ (A x y η).conjTranspose) T.adjoint)
    (hU : GraphDistributionalRealization (reverseGraphOperator S)
      (fun k η ↦ star (χ k η)) (adjointFirstOutputAmplitude A i) U)
    (u : graphTestSpace n r) :
    lineDerivOp (EuclideanSpace.single i (1 : ℝ))
      (T.adjoint (graphTestToLp u) : 𝓢'(E, V)) = (U (graphTestToLp u) : 𝓢'(E, V)) := by
  apply firstOutput_limit _ _ _ _ T.adjoint U hT hU u i
  intro k φ
  have hs : HasCompactSupport (fun η ↦ star (χ k η)) := (hχs k).comp_left (star_zero _)
  have hz : (0 : E) ∉ tsupport (fun η ↦ star (χ k η)) := by
    exact fun hm ↦ hχ0 k ((tsupport_comp_subset (g := star) (star_zero _) _) hm)
  exact reverseGraphOperator_frequencyCut_output_weak_pairing hA.conjTranspose hK hS
    ((starL ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp (hχ k)) hs hz i u φ

end JanetCartan.FourierIntegral
