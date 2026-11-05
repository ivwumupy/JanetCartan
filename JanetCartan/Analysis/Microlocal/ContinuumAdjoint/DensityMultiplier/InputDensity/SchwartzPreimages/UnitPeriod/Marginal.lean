module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputDensity.SchwartzPreimages.UnitPeriod.Basic
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.CompactIntegral

/-!
# Schwartz marginals over the carrier parameter space

Integration in the three parameter coordinates preserves joint Schwartz
regularity. The proof bounds every polynomially weighted output derivative by
an integrable inverse power of the parameter norm and applies dominated
differentiation. This supplies the marginal step in
`exists_unitPeriodSchwartz_compactSmooth`, for
`app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped SchwartzMap ContDiff Topology
namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open CarrierSobolev

/-- Restricting the output directions to a slice cannot increase the derivative
norm. Used to transfer joint Schwartz bounds to the marginal in
`app:ch_background:eq:bg-density-adjoint`. -/
private theorem norm_unitPeriod_slice_jet_le {n : ℕ}
    (K : 𝓢(InitialSpace n × ParameterSpace, ℂ)) (j : ℕ)
    (x : InitialSpace n) (z : ParameterSpace) :
    ‖iteratedFDeriv ℝ j (fun y ↦ K (y, z)) x‖ ≤
      ‖iteratedFDeriv ℝ j K (x, z)‖ := by
  let L := ContinuousLinearMap.inl ℝ (InitialSpace n) ParameterSpace
  have he : (fun y ↦ K (y, z)) = (fun p ↦ K (p + (0, z))) ∘ L := by
    funext y
    simp [L]
  have ht : ContDiff ℝ ∞ (fun p ↦ K (p + (0, z))) :=
    (K.smooth ⊤).comp (contDiff_id.add contDiff_const)
  rw [he, L.iteratedFDeriv_comp_right ht x (by simp)]
  simp only [iteratedFDeriv_comp_add_right, L, ContinuousLinearMap.inl_apply,
    Prod.mk_add_mk, add_zero, zero_add]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j K (x, z)‖ *
        ∏ _ : Fin j, ‖ContinuousLinearMap.inl ℝ (InitialSpace n) ParameterSpace‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ j K (x, z)‖ * ∏ _ : Fin j, (1 : ℝ) := by
      gcongr
      exact ContinuousLinearMap.norm_inl_le_one ℝ _ _
    _ = _ := by simp

/-- Each polynomially weighted output jet has an integrable bound independent
of the output point. This is the domination needed by the marginal construction
for `app:ch_background:prop:bg-adjoint`. -/
private theorem exists_unitPeriod_weighted_slice_bound {n : ℕ}
    (K : 𝓢(InitialSpace n × ParameterSpace, ℂ)) (k j : ℕ) :
    ∃ b : ParameterSpace → ℝ, Integrable b ∧ ∀ x z,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (fun y ↦ K (y, z)) x‖ ≤ b z := by
  let l := (volume : Measure ParameterSpace).integrablePower
  let C := 2 ^ (k + l) * (Finset.Iic (k + l, j)).sup
    (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) K
  refine ⟨fun z ↦ C * (1 + ‖z‖) ^ (-(l : ℝ)),
    (Measure.integrable_pow_neg_integrablePower volume).const_mul C, ?_⟩
  intro x z
  dsimp only
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  calc
    _ = (‖x‖ ^ k * (1 + ‖z‖) ^ l) *
        ‖iteratedFDeriv ℝ j (fun y ↦ K (y, z)) x‖ := by ring
    _ ≤ ((1 + ‖(x, z)‖) ^ k * (1 + ‖(x, z)‖) ^ l) *
        ‖iteratedFDeriv ℝ j K (x, z)‖ := by
      gcongr
      · exact (norm_fst_le (x, z)).trans (by linarith [norm_nonneg (x, z)])
      · exact norm_snd_le (x, z)
      · exact norm_unitPeriod_slice_jet_le K j x z
    _ = (1 + ‖(x, z)‖) ^ (k + l) * ‖iteratedFDeriv ℝ j K (x, z)‖ := by
      rw [pow_add]
    _ ≤ C := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (k + l, j)) le_rfl le_rfl K (x, z)


/-- Integrating a genuine joint Schwartz function over the literal Lebesgue
volume on the carrier parameter space gives a Schwartz function in the initial
variables. No restriction on the transverse dimension is required. This is the
marginal construction consumed by `exists_unitPeriodSchwartz_compactSmooth`
for `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`. -/
theorem exists_unitPeriodSchwartz_marginal (n : ℕ)
    (K : 𝓢(InitialSpace n × ParameterSpace, ℂ)) :
    ∃ g : 𝓢(InitialSpace n, ℂ), ∀ x, g x = ∫ z : ParameterSpace, K (x, z) := by
  have hb := fun j ↦ exists_unitPeriod_weighted_slice_bound K 0 j
  choose b hi hb using hb
  simp only [pow_zero, one_mul] at hb
  have hjoint (j : ℕ) : ContDiff ℝ ∞
      (fun p : InitialSpace n × ParameterSpace ↦
        iteratedFDeriv ℝ j (fun y ↦ K (y, p.2)) p.1) :=
    FiniteChain.Retarded.KernelDecay.contDiff_outputJet (K.smooth ⊤) j
  have hm (j : ℕ) (x : InitialSpace n) : AEStronglyMeasurable
      (fun z : ParameterSpace ↦ iteratedFDeriv ℝ j (fun y ↦ K (y, z)) x) :=
    ((hjoint j).continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hint (j : ℕ) (x : InitialSpace n) : Integrable
      (fun z : ParameterSpace ↦ iteratedFDeriv ℝ j (fun y ↦ K (y, z)) x) :=
    (hi j).mono' (hm j x) (ae_of_all _ (hb j x))
  have heq (j : ℕ) (x : InitialSpace n) :
      iteratedFDeriv ℝ j (fun y ↦ ∫ z : ParameterSpace, K (y, z)) x =
        ∫ z : ParameterSpace, iteratedFDeriv ℝ j (fun y ↦ K (y, z)) x := by
    apply MeasureEnvelopes.iteratedFDeriv_integral_of_dominated
      (r := j) (b := b) (s := Set.univ) isOpen_univ
    · exact ae_of_all _ fun z y _ ↦
        ((K.smooth j).comp (contDiff_id.prodMk contDiff_const)).contDiffAt
    · exact fun i _ y _ ↦ hm i y
    · exact fun i _ ↦ hi i
    · exact fun i _ ↦ ae_of_all _ fun z y _ ↦ hb i y z
    · exact le_rfl
    · exact Set.mem_univ x
  have hdiff (j : ℕ) : Differentiable ℝ
      (fun x ↦ ∫ z : ParameterSpace, iteratedFDeriv ℝ j (fun y ↦ K (y, z)) x) := by
    intro x
    let L := continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (j + 1) ↦ InitialSpace n) ℂ
    apply HasFDerivAt.differentiableAt
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := Set.univ) (bound := b (j + 1)) (F' := fun y z ↦
        fderiv ℝ (iteratedFDeriv ℝ j (fun t ↦ K (t, z))) y) (Filter.univ_mem)
    · exact Filter.Eventually.of_forall (hm j)
    · exact hint j x
    · exact L.continuous.comp_aestronglyMeasurable (hm (j + 1) x)
    · simpa only [norm_fderiv_iteratedFDeriv] using
        (ae_of_all (volume : Measure ParameterSpace) fun z y (_ : y ∈ Set.univ) ↦ hb (j + 1) y z)
    · exact hi (j + 1)
    · exact ae_of_all _ fun z y _ ↦
        (((K.smooth ⊤).comp (contDiff_id.prodMk contDiff_const)).differentiable_iteratedFDeriv
          (m := j) (by exact_mod_cast ENat.natCast_lt_top j)).differentiableAt.hasFDerivAt
  refine ⟨{ toFun := fun x ↦ ∫ z : ParameterSpace, K (x, z)
            smooth' := ?_
            decay' := ?_ }, fun _ ↦ rfl⟩
  · apply contDiff_of_differentiable_iteratedFDeriv
    intro j _
    simpa only [funext (heq j)] using hdiff j
  · intro k j
    obtain ⟨c, hc, hcBound⟩ := exists_unitPeriod_weighted_slice_bound K k j
    refine ⟨∫ z, c z, fun x ↦ ?_⟩
    rw [heq j x]
    calc
      _ ≤ ‖x‖ ^ k * ∫ z : ParameterSpace,
          ‖iteratedFDeriv ℝ j (fun y ↦ K (y, z)) x‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
      _ = ∫ z : ParameterSpace, ‖x‖ ^ k *
          ‖iteratedFDeriv ℝ j (fun y ↦ K (y, z)) x‖ := (integral_const_mul _ _).symm
      _ ≤ ∫ z, c z := integral_mono ((hint j x).norm.const_mul _) hc (hcBound x)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
