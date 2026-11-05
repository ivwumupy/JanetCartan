module

public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.SourceJets
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition.SmoothExtension
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.CoefficientNorms

/-!
# Classical joint response bounds from the original Fourier envelopes

The response and preparation consumers measure the full physical/label/covector
jet, whereas the reconstruction theorem returns spatial Fourier norms of each
ordered parameter derivative. Use the existing product basis and Schwarz
identity on the original open parameter domain, followed by spatial Sobolev
embedding. The constants precede the response, frequency and finite history.

The finite reserve is `m + n + 1`: a parameter word of length `k` requires
spatial order `m - k + n + 1`. No parameter integration, additional cutoff, or
change of response is used in this conversion.

Consumers: `PreparedPositiveRun.exists_finite_preparation_with_constructed_current`
and `Sampling.exists_initialized_originalScale_corrected_event_and_transport`.
The actual reduced-solution envelope is a separate producer obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.CanonicalAtomRealization

open LocalSobolev Pseudodifferential
open RegularSector.FiniteAssembly.CoefficientNorms
open ResponseTransfer.FullSourceEnvelopes
open ResponseTransfer.Complement.ParameterDerivatives

private theorem exists_spatialResponse_fourier_jet_constant (n r m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : Euclidean n → EuclideanSpace ℂ (Fin r)), ContDiff ℝ ∞ f →
      ∀ (u : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n))),
        u =ᵐ[volume] f → MemVectorFourierSobolev ((m + n + 1 : ℕ) : ℝ) u →
      ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤
        C * vectorFourierSobolevNorm ((m + n + 1 : ℕ) : ℝ) u := by
  obtain ⟨Cf, hCf, hfourier⟩ := vector_restrictionSobolev_nat_bounds n r (m+n+1)
  obtain ⟨Ce, hCe, hemb⟩ :=
    exists_cNorm_le_restrictionSobolevNorm (F := EuclideanSpace ℂ (Fin r)) n m
  refine ⟨Ce * Cf, mul_nonneg (zero_le_one.trans hCe) hCf.le, ?_⟩
  intro f hf u hrep hu j hj x
  let V := ball x 2
  let v : LocalL2 V (EuclideanSpace ℂ (Fin r)) := ((Lp.memLp u).restrict V).toLp u
  have huv : (u : Euclidean n → _) =ᵐ[volume.restrict V] v := (MemLp.coeFn_toLp _).symm
  obtain ⟨hmem, hnorm⟩ := hfourier u hu V v huv
  have hrepV : (u : Euclidean n → _) =ᵐ[volume.restrict V] f := ae_restrict_of_ae hrep
  have hfv : f =ᵐ[volume.restrict V] v := hrepV.symm.trans huv
  have hC := hemb x 1 2 (by norm_num) (by norm_num) f hf.contDiffOn v hfv hmem
  have hjC := norm_iteratedFDeriv_le_cNorm (isCompact_closedBall x 1)
    (hf.of_le (by simp)) (mem_closedBall_self (by norm_num)) hj
  exact hjC.trans (hC.trans ((mul_le_mul_of_nonneg_left hnorm
    (zero_le_one.trans hCe)).trans_eq (mul_assoc _ _ _).symm))

private theorem parameterListJet_congr_near
    {X Y F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : X × Y → F} {x : X} {c : Y}
    (hfg : f =ᶠ[𝓝 (x,c)] g) (ws : List Y) :
    (fun y ↦ parameterListJet (fun b ↦ f (y,b)) ws c) =ᶠ[𝓝 x]
      (fun y ↦ parameterListJet (fun b ↦ g (y,b)) ws c) := by
  obtain ⟨U, hU, hUopen, hxc⟩ := _root_.mem_nhds_iff.mp hfg
  filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually
    (hUopen.mem_nhds hxc)] with y hy
  have hp : (fun b ↦ f (y,b)) =ᶠ[𝓝 c] (fun b ↦ g (y,b)) := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually
      (hUopen.mem_nhds hy)] with b hb
    exact hU hb
  exact congrArg (fun T ↦ T ws.get) ((hp.iteratedFDeriv ℝ ws.length).eq_of_nhds)

/-- The existing full-source mixed-word identity is local on the original
open parameter domain. Only a smooth germ is extended to invoke Schwarz
symmetry; its Fourier representative is never changed. -/
private theorem exists_localResponse_mixedBasisJet_spatial_parameter
    {n d r j : ℕ} {V : Set (Euclidean 3 × Euclidean d)} (hV : IsOpen V)
    {f : Euclidean n × (Euclidean 3 × Euclidean d) → EuclideanSpace ℂ (Fin r)}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ V))
    (v : Fin j → (Fin n ⊕ (Fin 3 ⊕ Fin d))) (x : Euclidean n)
    {c : Euclidean 3 × Euclidean d} (hc : c ∈ V) :
    ∃ xs : List (Euclidean n), ∃ ws : List (Euclidean 3 × Euclidean d),
      xs.length + ws.length = j ∧
      (∀ y ∈ xs, ‖y‖ ≤ 1) ∧ (∀ w ∈ ws, ‖w‖ ≤ 1) ∧
      iteratedFDeriv ℝ j f (x,c) (fun k ↦ fullSourceMixedBasis n d (v k)) =
        parameterListJet (fun y ↦ parameterListJet (fun b ↦ f (y,b)) ws c) xs x := by
  obtain ⟨xs, ws, hlen, hxs, hws, hword⟩ :=
    exists_fullSource_mixedBasisJet_spatial_parameter (r := r) v
  have hO : IsOpen ((univ : Set (Euclidean n)) ×ˢ V) := isOpen_univ.prod hV
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO (x,c) ⟨mem_univ x, hc⟩
  obtain ⟨g, hg, _, _, heq⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall (x,c)
      (half_pos hε) hO ((closedBall_subset_ball (half_lt_self hε)).trans hball) hf
  have hgf : g =ᶠ[𝓝 (x,c)] f := heq (x,c) (mem_closedBall_self (half_pos hε).le)
  refine ⟨xs, ws, hlen, hxs, hws, ?_⟩
  rw [← (hgf.iteratedFDeriv ℝ j).eq_of_nhds, hword g hg x c]
  exact congrArg (fun T ↦ T xs.get)
    (((parameterListJet_congr_near hgf ws).iteratedFDeriv ℝ xs.length).eq_of_nhds)

/-- The joint classical seminorm of a full response is controlled by the
spatial Fourier norms of its ordered parameter jets. A word of length `k`
uses exactly spatial order `m-k+n+1`; thus the total reserve is fixed before
the field and the original parameter set. This is the Sobolev-to-classical
step of `app:ch_response:eq:response-graded-derivative` and the finite response
bound used in `app:ch_mean_pairs:eq:mean-prepared-scalar`. -/
theorem exists_fullParameterResponse_cNorm_constant (n d r m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (V : Set (Euclidean 3 × Euclidean d)), IsOpen V →
      ∀ (f : Euclidean n × (Euclidean 3 × Euclidean d) → EuclideanSpace ℂ (Fin r)),
        ContDiffOn ℝ ∞ f (univ ×ˢ V) →
      ∀ A : ℝ, 0 ≤ A →
        (∀ c ∈ V, ∀ k ≤ m, ∀ w : Fin k → (Euclidean 3 × Euclidean d),
          (∀ l, ‖w l‖ ≤ 1) →
          ∃ u : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (Euclidean n)),
            u =ᵐ[volume] (fun x ↦ iteratedFDeriv ℝ k (fun b ↦ f (x,b)) c w) ∧
            MemVectorFourierSobolev ((m-k+n+1 : ℕ) : ℝ) u ∧
            vectorFourierSobolevNorm ((m-k+n+1 : ℕ) : ℝ) u ≤ A) →
      ∀ J : Set (Euclidean n × (Euclidean 3 × Euclidean d)), J ⊆ univ ×ˢ V →
        cNorm J m f ≤ C * A := by
  classical
  choose D hD hspatial using fun k ↦ exists_spatialResponse_fourier_jet_constant n r (m-k)
  let Dsum := ∑ k ∈ Finset.range (m+1), D k
  have hDsum : 0 ≤ Dsum := Finset.sum_nonneg (fun k _ ↦ hD k)
  let dim : ℝ := n + (3+d)
  have hdim : 1 ≤ dim := by
    dsimp [dim]
    have := Nat.cast_nonneg (α := ℝ) n
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  refine ⟨(m+1 : ℝ) * dim^m * Dsum, by positivity, ?_⟩
  intro V hV f hf A hA hfourier J hJ
  have hparam : ContDiffOn ℝ ∞ (fun q : (Euclidean 3 × Euclidean d) × Euclidean n ↦
      f (q.2,q.1)) (V ×ˢ univ) :=
    hf.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ h ↦ ⟨h.2, h.1⟩)
  have hjet (j : ℕ) (hj : j ≤ m) (p : Euclidean n × (Euclidean 3 × Euclidean d))
      (hp : p ∈ J) : ‖iteratedFDeriv ℝ j f p‖ ≤ dim^m * Dsum * A := by
    have hc := (hJ hp).2
    have hbasis (v : Fin j → (Fin n ⊕ (Fin 3 ⊕ Fin d))) :
        ‖iteratedFDeriv ℝ j f p (fun k ↦ fullSourceMixedBasis n d (v k))‖ ≤ Dsum * A := by
      obtain ⟨xs, ws, hlen, hxs, hws, heq⟩ :=
        exists_localResponse_mixedBasisJet_spatial_parameter hV hf v p.1 hc
      have hk : ws.length ≤ m := by omega
      have hx : xs.length ≤ m-ws.length := by omega
      let g := fun x ↦ parameterListJet (fun b ↦ f (x,b)) ws p.2
      have hg : ContDiff ℝ ∞ g :=
        fullSource_parameterJet_contDiff hV hparam ws.length ws.get hc
      obtain ⟨u, hrep, hu, hnorm⟩ := hfourier p.2 hc ws.length hk ws.get
        (fun l ↦ hws _ (List.get_mem ..))
      have hDle : D ws.length ≤ Dsum := Finset.single_le_sum (fun k _ ↦ hD k)
        (Finset.mem_range.mpr (by omega))
      rw [heq]
      exact ((iteratedFDeriv ℝ xs.length g p.1).unit_le_opNorm
        (pi_norm_le_iff_of_nonneg zero_le_one |>.mpr (fun l ↦ hxs _ (List.get_mem ..)))).trans
        ((hspatial ws.length g hg u hrep hu xs.length hx p.1).trans
          (mul_le_mul hDle hnorm (norm_nonneg _) hDsum))
    apply (norm_fullSource_mixedTensor_le_sum _).trans
    calc
      _ ≤ ∑ _v : Fin j → (Fin n ⊕ (Fin 3 ⊕ Fin d)), Dsum * A :=
        Finset.sum_le_sum (fun v _ ↦ hbasis v)
      _ = dim^j * Dsum * A := by simp [dim, Fintype.card_sum]; ring
      _ ≤ dim^m * Dsum * A := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hdim hj) hDsum) hA
  have h := cNorm_le_sum_of_bounds (s := J) (r := m)
    (fun _ _ ↦ mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hdim) _) hDsum) hA)
    hjet
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, mul_assoc] using h

end JanetCartan.CanonicalAtomRealization
