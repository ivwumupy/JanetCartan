module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.UniformJets

/-!
# Quantitative transport flux jets

The literal fluxes `wⱼ A` used by `normalTransportCoefficient` in
`app:ch_osc:prop:osc-normal`, Step 2. All norms on matrices are Frobenius norms.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.NormalComparison
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

-- Use the topology belonging to the Frobenius norm throughout matrix calculus.
local instance (r : ℕ) : TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- The flux whose input divergence enters the actual coefficient `c₀` in
`app:ch_osc:prop:osc-normal`. It contains no mask. -/
def UniformNormalData.normalTransportFlux (F : UniformNormalData G C)
    (ε : ℝ) (j : Fin n) (x y u : Euclidean n) : Matrix (Fin r) (Fin r) ℂ :=
  F.transportVelocity ε x y u j • normalAmplitude (F.amplitude ε) x y u

/-- Ambient joint smoothness of the actual flux, including at parameter
endpoints (`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem UniformNormalData.normalTransportFlux_contDiffAt (F : UniformNormalData G C)
    (j : Fin n) {q : ℝ × (Euclidean n × (Euclidean n × Euclidean n))}
    (hq : q ∈ Icc 0 G.ε₀ ×ˢ (G.X ×ˢ (G.X ×ˢ G.D))) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      F.normalTransportFlux p.1 j p.2.1 p.2.2.1 p.2.2.2) q := by
  have ha := F.normalAmplitude_contDiffOn_joint.contDiffAt
    ((F.isOpen_parameterDomain.prod (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D))).mem_nhds
      ⟨F.parameter_subset hq.1, hq.2⟩)
  exact ((EuclideanSpace.proj j).contDiff.contDiffAt.comp q
    (F.transportVelocity_contDiffAt hq)).smul ha

/-- Spatial smoothness of the flux on the original boxes
(`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem UniformNormalData.normalTransportFlux_contDiffOn_spatial
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) (j : Fin n) :
    ContDiffOn ℝ ∞ (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      F.normalTransportFlux ε j q.1 q.2.1 q.2.2) (G.X ×ˢ (G.X ×ˢ G.D)) := by
  intro q hq
  exact ((F.normalTransportFlux_contDiffAt j (q := (ε, q)) ⟨hε, hq⟩).comp q
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

/-- The full spatial jets of every `wⱼ A` are controlled by the fixed input
jets and determinant gap, uniformly before the choice of family
(`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem UniformNormalGeometry.exists_normalTransportFlux_jet_bound
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) (N : ℕ)
    (hN : N + 2 ≤ 20 * (n + 1)) :
    ∃ K > 0, ∀ F : UniformNormalData G C,
      ∀ ε ∈ Icc 0 G.ε₀, ∀ j : Fin n, ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.D), ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          F.normalTransportFlux ε j q.1 q.2.1 q.2.2) z‖ ≤ K := by
  obtain ⟨W, hW, hw⟩ := G.exists_transportVelocity_jet_bound C N hN
  let A := ∑ k ∈ Finset.range (N + 1), normalAmplitudeJetBound r C k
  let K := (2 : ℝ)^N * W * A
  refine ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro F ε hε j z hz k hk
  have hU : IsOpen (G.X ×ˢ (G.X ×ˢ G.D)) :=
    G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D)
  have hvel := F.transportVelocity_contDiffOn_spatial hε
  have hproj : ‖(EuclideanSpace.proj j : Euclidean n →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa using PiLp.norm_apply_le v j
  let b : Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℂ →L[ℝ] Matrix (Fin r) (Fin r) ℂ :=
    (ContinuousLinearMap.lsmul ℝ ℝ).comp (EuclideanSpace.proj j)
  have hbNorm : ‖b‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul ContinuousLinearMap.opNorm_lsmul_le hproj (norm_nonneg _) zero_le_one).trans_eq
        (one_mul 1))
  have hamps (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv ℝ i (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
        normalAmplitude (F.amplitude ε) q.1 q.2.1 q.2.2) z‖ ≤ A :=
    (F.norm_iteratedFDeriv_normalAmplitude_le hε hz (by omega)).trans
      (Finset.single_le_sum (fun l _ ↦ normalAmplitudeJetBound_nonneg r C l)
        (Finset.mem_range.mpr (by omega)))
  have hb := InverseChartJet.norm_iteratedFDeriv_bilinear_on_open_le
    b hbNorm hU hvel
    (F.normalAmplitude_contDiffOn_spatial (F.parameter_subset hε)) hW.le hz k
    (fun i hi ↦ hw F ε hε z hz i (hi.trans hk)) hamps
  apply hb.trans
  apply le_trans _ (le_max_right 1 K)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ ↦ normalAmplitudeJetBound_nonneg r C i)
  dsimp [K]
  gcongr
  norm_num

/-- Restricting the differential to an input coordinate gives the literal
`partialDeriv` used in the divergence coefficient of
`app:ch_osc:prop:osc-normal`. -/
theorem partialDeriv_input_eq_fderiv
    {f : (Euclidean n × (Euclidean n × Euclidean n)) → Matrix (Fin r) (Fin r) ℂ}
    {q : Euclidean n × (Euclidean n × Euclidean n)}
    (hf : DifferentiableAt ℝ f q) (j : Fin n) :
    partialDeriv (fun u ↦ f (q.1, (q.2.1, u))) q.2.2 j =
      fderiv ℝ f q (0, (0, EuclideanSpace.single j 1)) := by
  let L : Euclidean n →L[ℝ] (Euclidean n × (Euclidean n × Euclidean n)) :=
    (ContinuousLinearMap.inr ℝ (Euclidean n) (Euclidean n × Euclidean n)).comp
      (ContinuousLinearMap.inr ℝ (Euclidean n) (Euclidean n))
  have hp : HasFDerivAt (fun u : Euclidean n ↦ (q.1, (q.2.1, u))) L q.2.2 :=
    (hasFDerivAt_prodMk_right q.1 q.2).comp q.2.2
      (hasFDerivAt_prodMk_right q.2.1 q.2.2)
  have hd := hf.hasFDerivAt.comp q.2.2 hp
  change (fderiv ℝ (f ∘ fun u ↦ (q.1, (q.2.1, u))) q.2.2)
    (EuclideanSpace.single j 1) = _
  rw [hd.fderiv]
  rfl

/-- Taking an input partial derivative costs one full spatial jet and no
norm factor. This bounds the divergence of `normalTransportFlux` in
`app:ch_osc:prop:osc-normal`. -/
theorem norm_iteratedFDeriv_partialDeriv_input_le
    {f : (Euclidean n × (Euclidean n × Euclidean n)) → Matrix (Fin r) (Fin r) ℂ}
    {U : Set (Euclidean n × (Euclidean n × Euclidean n))} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U)
    {q : Euclidean n × (Euclidean n × Euclidean n)} (hq : q ∈ U) (j : Fin n) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z : Euclidean n × (Euclidean n × Euclidean n) ↦
      partialDeriv (fun u ↦ f (z.1, (z.2.1, u))) z.2.2 j) q‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) f q‖ := by
  let e : Euclidean n × (Euclidean n × Euclidean n) :=
    (0, (0, EuclideanSpace.single j 1))
  let L := ContinuousLinearMap.apply ℝ (Matrix (Fin r) (Fin r) ℂ) e
  have he : ‖e‖ ≤ 1 := by
    simp [e, Prod.norm_def, EuclideanSpace.single, PiLp.norm_single]
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro A
    exact (A.le_opNorm e).trans (by simpa using mul_le_mul_of_nonneg_left he (norm_nonneg A))
  have heq : (fun z : Euclidean n × (Euclidean n × Euclidean n) ↦
      partialDeriv (fun u ↦ f (z.1, (z.2.1, u))) z.2.2 j) =ᶠ[𝓝 q]
      (L ∘ fderiv ℝ f) := by
    filter_upwards [hU.mem_nhds hq] with z hz
    exact partialDeriv_input_eq_fderiv ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt
      (by simp)) j
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
  have hb := L.norm_iteratedFDeriv_comp_left
    ((hf.contDiffAt (hU.mem_nhds hq)).fderiv_right (m := ∞) (by simp)) (n := k) (by simp)
  rw [norm_iteratedFDeriv_fderiv] at hb
  exact hb.trans (by
    simpa using (mul_le_mul_of_nonneg_right hL
      (norm_nonneg (iteratedFDeriv ℝ (k + 1) f q))))

/-- The divergence summands are ambient jointly smooth at the endpoints,
as required for `c₀` in `app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.normalTransportFlux_partialDeriv_contDiffAt
    (F : UniformNormalData G C) (j : Fin n)
    {q : ℝ × (Euclidean n × (Euclidean n × Euclidean n))}
    (hq : q ∈ Icc 0 G.ε₀ ×ˢ (G.X ×ˢ (G.X ×ˢ G.D))) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      partialDeriv (F.normalTransportFlux p.1 j p.2.1 p.2.2.1) p.2.2.2 j) q := by
  have hf := F.normalTransportFlux_contDiffAt j hq
  have haux := hf.comp (q, q.2.2.2)
    (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.fst.prodMk
      (contDiffAt_fst.snd.snd.fst.prodMk contDiffAt_snd)))
  exact (haux.fderiv contDiffAt_snd.snd.snd (by simp)).clm_apply contDiffAt_const

/-- All literal transport coefficients are ambient jointly smooth at
admissible points (`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem UniformNormalData.normalTransportCoefficient_contDiffAt
    (F : UniformNormalData G C) (k : Option (Fin n))
    {q : ℝ × (Euclidean n × (Euclidean n × Euclidean n))}
    (hq : q ∈ Icc 0 G.ε₀ ×ˢ (G.X ×ˢ (G.X ×ˢ G.D))) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      F.normalTransportCoefficient p.1 k p.2.1 p.2.2.1 p.2.2.2) q := by
  cases k with
  | some j => exact (F.normalTransportFlux_contDiffAt j hq).neg
  | none =>
    have ha := F.normalAmplitude_contDiffOn_joint.contDiffAt
      ((F.isOpen_parameterDomain.prod (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D))).mem_nhds
        ⟨F.parameter_subset hq.1, hq.2⟩)
    exact (contDiffAt_parameter_deriv ha).sub
      (ContDiffAt.sum (fun j _ ↦ F.normalTransportFlux_partialDeriv_contDiffAt j hq))

/-- Uniform Frobenius jets of the literal `c₀ = ∂ε A - divᵤ(w A)` and
`cⱼ = -wⱼ A`. This is the local quantitative coefficient estimate in
`app:ch_osc:prop:osc-normal`, before buffered zero extension. -/
theorem UniformNormalGeometry.exists_normalTransportCoefficient_jet_bound
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) (N : ℕ)
    (hN : N + 3 ≤ 20 * (n + 1)) :
    ∃ K > 0, ∀ F : UniformNormalData G C,
      ∀ ε ∈ Icc 0 G.ε₀, ∀ c : Option (Fin n),
      ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.D), ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          F.normalTransportCoefficient ε c q.1 q.2.1 q.2.2) z‖ ≤ K := by
  obtain ⟨W, hW, hw⟩ := G.exists_normalTransportFlux_jet_bound C (N + 1) (by omega)
  let A := ∑ k ∈ Finset.range (N + 1), normalAmplitudeParameterJetBound r C k
  refine ⟨max W (A + n * W), lt_of_lt_of_le hW (le_max_left _ _), ?_⟩
  intro F ε hε c z hz k hk
  have hU : IsOpen (G.X ×ˢ (G.X ×ˢ G.D)) :=
    G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D)
  cases c with
  | some j =>
    change ‖iteratedFDeriv ℝ k (fun q ↦ -(F.normalTransportFlux ε j q.1 q.2.1 q.2.2)) z‖ ≤ _
    rw [show (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      -(F.normalTransportFlux ε j q.1 q.2.1 q.2.2)) =
      -(fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
        F.normalTransportFlux ε j q.1 q.2.1 q.2.2) from rfl,
      iteratedFDeriv_neg_apply, norm_neg]
    exact (hw F ε hε j z hz k (by omega)).trans (le_max_left _ _)
  | none =>
    let dA := fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      deriv (fun t ↦ normalAmplitude (F.amplitude t) q.1 q.2.1 q.2.2) ε
    let dB := fun j (q : Euclidean n × (Euclidean n × Euclidean n)) ↦
      partialDeriv (F.normalTransportFlux ε j q.1 q.2.1) q.2.2 j
    have hdA : ContDiffAt ℝ ∞ dA z :=
      (F.normalAmplitude_parameterDeriv_contDiffOn (F.parameter_subset hε)).contDiffAt
        (hU.mem_nhds hz)
    have hdB (j : Fin n) : ContDiffAt ℝ ∞ (dB j) z :=
      (F.normalTransportFlux_partialDeriv_contDiffAt j (q := (ε, z)) ⟨hε, hz⟩).comp z
        (contDiffAt_const.prodMk contDiffAt_id)
    have hjA : ‖iteratedFDeriv ℝ k dA z‖ ≤ A :=
      (F.norm_iteratedFDeriv_normalAmplitude_parameterDeriv_le hε hz (by omega)).trans
        (Finset.single_le_sum (fun i _ ↦ normalAmplitudeParameterJetBound_nonneg r C i)
          (Finset.mem_range.mpr (by omega)))
    have hjB (j : Fin n) : ‖iteratedFDeriv ℝ k (dB j) z‖ ≤ W :=
      (norm_iteratedFDeriv_partialDeriv_input_le hU
        (F.normalTransportFlux_contDiffOn_spatial hε j) hz j k).trans
          (hw F ε hε j z hz (k + 1) (by omega))
    change ‖iteratedFDeriv ℝ k (fun q ↦ dA q - ∑ j, dB j q) z‖ ≤ _
    rw [fun_iteratedFDeriv_sub_apply (hdA.of_le (by simp))
      ((ContDiffAt.sum (fun j _ ↦ hdB j)).of_le (by simp)),
      iteratedFDeriv_fun_sum_apply (fun j _ ↦ (hdB j).of_le (by simp))]
    apply (norm_sub_le _ _).trans
    apply (add_le_add hjA ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ ↦ hjB j)))).trans
    simp

end JanetCartan.NormalComparison
