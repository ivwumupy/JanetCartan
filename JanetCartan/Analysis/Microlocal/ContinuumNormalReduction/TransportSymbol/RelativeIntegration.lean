module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.ShellBounds
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.FrequencyBounds.Completion

/-!
# Local spectator differentiation on the punctured frequency space

The homogeneous amplitude in `app:ch_background:eq:bg-symbol` need not extend
smoothly to the cone vertex. These local forms of spectator differentiation
allow the relative buffer in `FrequencyBounds.Completion` to be used in the
quantitative shell estimate.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- All spectator derivatives commute with integration locally on an open
physical/frequency region. Smoothness at zero frequency is not required.
Source: `app:ch_background:prop:bg-frame`, Step 1. -/
theorem iteratedFDeriv_spectatorIntegral_on
    {U : Set (Variables n)} (hU : IsOpen U)
    {K : Set (Euclidean 2)} (hK : IsCompact K) (j : ℕ)
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : Variables n × Euclidean 2 → G} (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ))
    {x : Variables n} (hx : x ∈ U) :
    iteratedFDeriv ℝ j (fun y ↦ ∫ v in K, f (y, v)) x =
      ∫ v in K, iteratedFDeriv ℝ j (fun y ↦ f (y, v)) x := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  induction j generalizing G with
  | zero =>
    let L := (continuousMultilinearCurryFin0 ℝ (Variables n) G).symm
    exact (L.toContinuousLinearEquiv.integral_comp_comm _).symm
  | succ j ih =>
    let g : Variables n × Euclidean 2 → Variables n →L[ℝ] G :=
      fun p ↦ fderiv ℝ (fun y ↦ f (y, p.2)) p.1
    have hg : ContDiffOn ℝ ∞ g (U ×ˢ univ) := contDiffOn_parameterFDeriv hU isOpen_univ hf
    have he : fderiv ℝ (fun y ↦ ∫ v in K, f (y, v)) =ᶠ[𝓝 x]
        fun y ↦ ∫ v in K, g (y, v) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact fderiv_compactParameterIntegral hU isOpen_univ hK (subset_univ K) hf hy
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
      (he.iteratedFDeriv ℝ j).eq_of_nhds, ih hg]
    let L := (continuousMultilinearCurryRightEquiv' ℝ j (Variables n) G).symm
    change L (∫ v in K, iteratedFDeriv ℝ j (fun y ↦ g (y, v)) x) = _
    calc
      _ = ∫ v in K, L (iteratedFDeriv ℝ j (fun y ↦ g (y, v)) x) :=
        (ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ)
          (E := Variables n [×j]→L[ℝ] Variables n →L[ℝ] G)
          (F := Variables n [×(j + 1)]→L[ℝ] G) L.toContinuousLinearEquiv _).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with v
        exact (iteratedFDeriv_succ_eq_comp_right (f := fun y ↦ f (y, v))).symm

/-- Restricting the spectator does not enlarge jets on an open working
region. Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem norm_iteratedFDeriv_spectatorSlice_on_le
    {U : Set (Variables n)} (hU : IsOpen U)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : Variables n × Euclidean 2 → G} (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ))
    (k : ℕ) {x : Variables n} (hx : x ∈ U) (v : Euclidean 2) :
    ‖iteratedFDeriv ℝ k (fun y ↦ f (y, v)) x‖ ≤
      ‖iteratedFDeriv ℝ k f (x, v)‖ := by
  let L := ContinuousLinearMap.inl ℝ (Variables n) (Euclidean 2)
  let g := fun p : Variables n × Euclidean 2 ↦ f (p + (0, v))
  have hg : ContDiffOn ℝ ∞ g (U ×ˢ univ) :=
    hf.comp (contDiffOn_id.add contDiffOn_const) (by intro p hp; simpa using hp)
  have hpre : L ⁻¹' (U ×ˢ univ) = U := by ext p; simp [L]
  have hp : L x ∈ U ×ˢ univ := by simpa [L] using hx
  have he := L.iteratedFDerivWithin_comp_right hg (hU.prod isOpen_univ).uniqueDiffOn
    (by rw [hpre]; exact hU.uniqueDiffOn) hp (by simp : (k : ℕ∞ω) ≤ ∞)
  have hgAt := hg.contDiffAt ((hU.prod isOpen_univ).mem_nhds hp)
  rw [hpre,
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      ((hgAt.comp x L.contDiff.contDiffAt).of_le (by simp)) hx,
    iteratedFDerivWithin_eq_iteratedFDeriv (hU.prod isOpen_univ).uniqueDiffOn
      (hgAt.of_le (by simp)) hp] at he
  have hfun : (fun y ↦ f (y, v)) = g ∘ L := by funext y; simp [g, L]
  rw [hfun, he]
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (by intro y; simp [L])
  calc
    _ ≤ ‖iteratedFDeriv ℝ k g (L x)‖ * ∏ _ : Fin k, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ k g (L x)‖ * ∏ _ : Fin k, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg L)
        (fun _ _ ↦ hL)) (norm_nonneg _)
    _ = _ := by simp [g, L, iteratedFDeriv_comp_add_right]

/-- A local joint bound passes through the fixed compact Lebesgue spectator
integral with just its volume as cost. Source:
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem norm_iteratedFDeriv_spectatorIntegral_on_le
    {U : Set (Variables n)} (hU : IsOpen U)
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : Variables n × Euclidean 2 → G} (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ))
    {K : Set (Euclidean 2)} (hK : IsCompact K) (k : ℕ)
    {x : Variables n} (hx : x ∈ U) {B : ℝ}
    (hB : ∀ v ∈ K, ‖iteratedFDeriv ℝ k f (x, v)‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun y ↦ ∫ v in K, f (y, v)) x‖ ≤ B * volume.real K := by
  rw [iteratedFDeriv_spectatorIntegral_on hU hK k hf hx]
  apply norm_setIntegral_le_of_norm_le_const_ae' hK.measure_lt_top
  filter_upwards [] with v hv
  exact (norm_iteratedFDeriv_spectatorSlice_on_le hU hf k hx v).trans (hB v hv)

end JanetCartan.ContinuumNormalReduction.TransportSymbol
