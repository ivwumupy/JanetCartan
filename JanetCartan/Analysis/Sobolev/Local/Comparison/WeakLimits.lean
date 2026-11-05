module

public import JanetCartan.Analysis.Sobolev.Local.Comparison.Intrinsic

/-!
# Closure of local weak jets under L² limits

The passage to the completion in `app:ch_regular_base:lem:ball-extension`,
with the L² convention of `app:not:fourier`. Test integrals are continuous
in the local L² norm, including on unbounded open domains.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Function
open scoped Topology ContDiff ENNReal NNReal

namespace JanetCartan.Mollification

section IntegralLimits

variable {X A B : Type*} [MeasurableSpace X]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] {μ : Measure X}
  {ι : Type*} {l : Filter ι}

/-- Continuous linear maps preserve L² convergence (`app:not:fourier`). -/
theorem tendsto_eLpNorm_compCLM_sub (L : A →L[ℝ] B)
    {f : ι → X → A} {g : X → A}
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun k ↦ eLpNorm (f k - g) 2 μ) l (𝓝 0)) :
    Tendsto (fun k ↦ eLpNorm ((L ∘ f k) - L ∘ g) 2 μ) l (𝓝 0) := by
  have hbound (k : ι) : eLpNorm ((L ∘ f k) - L ∘ g) 2 μ ≤
      (‖L‖₊ : ℝ≥0∞) * eLpNorm (f k - g) 2 μ := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      ((L.comp_memLp' (hf k)).sub (L.comp_memLp' hg)).aestronglyMeasurable
    exact Eventually.of_forall fun x ↦ by
      simpa only [Pi.sub_apply, comp_apply, ← map_sub] using L.le_opNNNorm (f k x - g x)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (ENNReal.Tendsto.const_mul (a := (‖L‖₊ : ℝ≥0∞)) hlim
      (Or.inr ENNReal.coe_ne_top))) (fun _ ↦ zero_le) hbound

/-- Pairing with an L² scalar function is continuous for L² convergence
(`app:ch_regular_base:lem:ball-extension`). -/
theorem tendsto_integral_smul_of_tendsto_eLpNorm_two
    {ψ : X → ℝ} (hψ : MemLp ψ 2 μ) {f : ι → X → A} {g : X → A}
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun k ↦ eLpNorm (f k - g) 2 μ) l (𝓝 0)) :
    Tendsto (fun k ↦ ∫ x, ψ x • f k x ∂μ) l (𝓝 (∫ x, ψ x • g x ∂μ)) := by
  apply tendsto_integral_of_L1' _
    (Eventually.of_forall fun k ↦ memLp_one_iff_integrable.mp (hψ.smul (hf k)))
  have hbound (k : ι) :
      eLpNorm ((fun x ↦ ψ x • f k x) - (fun x ↦ ψ x • g x)) 1 μ ≤
        eLpNorm ψ 2 μ * eLpNorm (f k - g) 2 μ := by
    simpa only [Pi.smul_def', Pi.sub_def, smul_sub] using
      (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hψ.aestronglyMeasurable
        ((hf k).sub hg).aestronglyMeasurable)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ENNReal.Tendsto.const_mul hlim (Or.inr hψ.eLpNorm_ne_top))
    (fun _ ↦ zero_le) hbound

end IntegralLimits

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set (EuclideanSpace ℝ (Fin n))}

private theorem integral_test_eq_restrict
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hs : tsupport ψ ⊆ U)
    (f : EuclideanSpace ℝ (Fin n) → F) :
    (∫ x, ψ x • f x) = ∫ x in U, ψ x • f x := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp [image_eq_zero_of_notMem_tsupport (mt (fun h ↦ hs h) hx)]

/-- Weak Fréchet derivative identities are closed under simultaneous local L²
convergence of the function and derivative field. Local integrability of the
limits follows from their L² membership, even when `U` has infinite volume
(`app:ch_regular_base:lem:ball-extension`, `app:not:fourier`). -/
theorem hasWeakFDerivOn_of_tendsto_eLpNorm_two
    {ι : Type*} {l : Filter ι} [NeBot l]
    {f : ι → EuclideanSpace ℝ (Fin n) → F}
    {D : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] F}
    {g : EuclideanSpace ℝ (Fin n) → F}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] F}
    (hw : ∀ k, HasWeakFDerivOn volume (f k) (D k) U)
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict U))
    (hD : ∀ k, MemLp (D k) 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U)) (hG : MemLp G 2 (volume.restrict U))
    (hflim : Tendsto (fun k ↦ eLpNorm (f k - g) 2 (volume.restrict U)) l (𝓝 0))
    (hDlim : Tendsto (fun k ↦ eLpNorm (D k - G) 2 (volume.restrict U)) l (𝓝 0)) :
    HasWeakFDerivOn volume g G U := by
  refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hg.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hG.locallyIntegrable (by norm_num)), ?_⟩
  intro ψ hψ hc hs v
  let ev := ContinuousLinearMap.apply ℝ F v
  have hleft := tendsto_integral_smul_of_tendsto_eLpNorm_two
    (μ := volume.restrict U) (hψ.continuous.memLp_of_hasCompactSupport hc)
    (fun k ↦ ev.comp_memLp' (hD k)) (ev.comp_memLp' hG)
    (tendsto_eLpNorm_compCLM_sub ev hD hG hDlim)
  have hd : Continuous (fun x ↦ fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (fun x ↦ fderiv ℝ ψ x v) :=
    (hc.fderiv ℝ).comp_left (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ L v) rfl
  have hds : tsupport (fun x ↦ fderiv ℝ ψ x v) ⊆ U :=
    (tsupport_comp_subset (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ L v)
      (f := fderiv ℝ ψ) rfl).trans ((tsupport_fderiv_subset ℝ).trans hs)
  have hright := (tendsto_integral_smul_of_tendsto_eLpNorm_two
    (hd.memLp_of_hasCompactSupport hdc) hf hg hflim).neg
  rw [integral_test_eq_restrict hs, integral_test_eq_restrict hds]
  apply tendsto_nhds_unique hleft
  convert hright using 1
  funext k
  simpa only [← integral_test_eq_restrict hs, ← integral_test_eq_restrict hds,
    comp_apply, ev, ContinuousLinearMap.apply_apply] using hw k |>.2.2 ψ hψ hc hs v

/-- Almost-everywhere changes on the domain preserve weak derivatives
(`app:ch_regular_base:lem:ball-extension`). Values outside the domain do not
enter the compactly supported test identities. -/
theorem HasWeakFDerivOn.congr_ae
    {f g : EuclideanSpace ℝ (Fin n) → F}
    {D G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] F}
    (hw : HasWeakFDerivOn volume f D U)
    (hf : f =ᵐ[volume.restrict U] g) (hD : D =ᵐ[volume.restrict U] G) :
    HasWeakFDerivOn volume g G U := by
  refine ⟨hw.1.congr hf, hw.2.1.congr hD, ?_⟩
  intro ψ hψ hc hs v
  have hds : tsupport (fun x ↦ fderiv ℝ ψ x v) ⊆ U :=
    (tsupport_comp_subset (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ L v)
      (f := fderiv ℝ ψ) rfl).trans ((tsupport_fderiv_subset ℝ).trans hs)
  rw [integral_test_eq_restrict hs, integral_test_eq_restrict hds]
  calc
    _ = ∫ x in U, ψ x • D x v := integral_congr_ae
      ((EventuallyEq.rfl : ψ =ᵐ[volume.restrict U] ψ).smul (hD.symm.fun_comp fun L ↦ L v))
    _ = - ∫ x in U, fderiv ℝ ψ x v • f x := by
      simpa only [← integral_test_eq_restrict hs, ← integral_test_eq_restrict hds] using
        hw.2.2 ψ hψ hc hs v
    _ = _ := congrArg Neg.neg (integral_congr_ae (EventuallyEq.rfl.smul hf))

/-- Almost-everywhere changes preserve finite weak jets provided the new
zeroth component has the required exact value
(`app:ch_regular_base:lem:ball-extension`). -/
theorem HasWeakJetOn.congr_ae
    {f g : EuclideanSpace ℝ (Fin n) → F}
    {J K : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F} {m : ℕ}
    (hw : HasWeakJetOn volume f J U m)
    (hzero : K 0 = iteratedFDeriv ℝ 0 g)
    (hJ : ∀ j ≤ m, J j =ᵐ[volume.restrict U] K j) :
    HasWeakJetOn volume g K U m := by
  refine ⟨hzero, fun j hj ↦ (hw.2 j hj).congr_ae (hJ j hj.le) ?_⟩
  exact (hJ (j + 1) hj).fun_comp _

/-- Normalize the zeroth jet to the exact order-zero derivative of the chosen
function representative. Positive-order fields are retained
(`app:not:fourier`, `app:ch_regular_base:lem:ball-extension`). -/
def normalizeWeakJet (f : EuclideanSpace ℝ (Fin n) → F)
    (J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F) :
    (j : ℕ) → EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F
  | 0 => iteratedFDeriv ℝ 0 f
  | j + 1 => J (j + 1)

/-- Normalization changes no local L² class when order zero already agrees
almost everywhere (`app:not:fourier`). -/
theorem normalizeWeakJet_ae
    {f : EuclideanSpace ℝ (Fin n) → F}
    {J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F}
    (hzero : J 0 =ᵐ[volume.restrict U] iteratedFDeriv ℝ 0 f) (j : ℕ) :
    J j =ᵐ[volume.restrict U] normalizeWeakJet f J j := by
  cases j with
  | zero => exact hzero
  | succ j => rfl

/-- Normalizing the zeroth jet preserves local L² membership
(`app:not:fourier`). -/
theorem memLp_normalizeWeakJet
    {f : EuclideanSpace ℝ (Fin n) → F}
    {J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F}
    (hzero : J 0 =ᵐ[volume.restrict U] iteratedFDeriv ℝ 0 f)
    {j : ℕ} (hJ : MemLp (J j) 2 (volume.restrict U)) :
    MemLp (normalizeWeakJet f J j) 2 (volume.restrict U) :=
  hJ.ae_eq (normalizeWeakJet_ae hzero j)

/-- Finite weak jets are closed under componentwise local L² convergence
when the limiting order-zero component is exactly normalized. The separate
normalization theorem below obtains this condition from L² limits
(`app:ch_regular_base:lem:ball-extension`). -/
theorem hasWeakJetOn_of_tendsto_eLpNorm_two
    {ι : Type*} {l : Filter ι} [NeBot l] {m : ℕ}
    {f : ι → EuclideanSpace ℝ (Fin n) → F} {g : EuclideanSpace ℝ (Fin n) → F}
    {J : ι → (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F}
    {K : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F}
    (hw : ∀ k, HasWeakJetOn volume (f k) (J k) U m)
    (hJ : ∀ k j, j ≤ m → MemLp (J k j) 2 (volume.restrict U))
    (hK : ∀ j ≤ m, MemLp (K j) 2 (volume.restrict U))
    (hlim : ∀ j ≤ m,
      Tendsto (fun k ↦ eLpNorm (J k j - K j) 2 (volume.restrict U)) l (𝓝 0))
    (hzero : K 0 = iteratedFDeriv ℝ 0 g) : HasWeakJetOn volume g K U m := by
  refine ⟨hzero, fun j hj ↦ ?_⟩
  let L := continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin (j + 1) ↦ EuclideanSpace ℝ (Fin n)) F
  have hD (k : ι) : MemLp (L ∘ J k (j + 1)) 2 (volume.restrict U) := by
    apply (hJ k (j + 1) hj).of_le_enorm (f := L ∘ J k (j + 1))
      (L.continuous.comp_aestronglyMeasurable (hJ k (j + 1) hj).aestronglyMeasurable)
    exact Eventually.of_forall fun x ↦ (L.enorm_map (J k (j + 1) x)).le
  have hG : MemLp (L ∘ K (j + 1)) 2 (volume.restrict U) := by
    apply (hK (j + 1) hj).of_le_enorm (f := L ∘ K (j + 1))
      (L.continuous.comp_aestronglyMeasurable (hK (j + 1) hj).aestronglyMeasurable)
    exact Eventually.of_forall fun x ↦ (L.enorm_map (K (j + 1) x)).le
  apply hasWeakFDerivOn_of_tendsto_eLpNorm_two (n := n)
    (F := (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F) (l := l)
    (fun k ↦ (hw k).2 j hj) (fun k ↦ hJ k j hj.le) hD (hK j hj.le) hG (hlim j hj.le)
  apply (hlim (j + 1) hj).congr
  intro k
  have heq : (L ∘ J k (j + 1)) - L ∘ K (j + 1) =
      L ∘ (J k (j + 1) - K (j + 1)) := by
    funext x
    exact (L.map_sub _ _).symm
  rw [heq]
  symm
  apply eLpNorm_congr_enorm_ae
    (L.continuous.comp_aestronglyMeasurable
      ((hJ k (j + 1) hj).sub (hK (j + 1) hj)).aestronglyMeasurable)
    ((hJ k (j + 1) hj).sub (hK (j + 1) hj)).aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ L.enorm_map _

/-- L² limits of functions and their zeroth weak jets agree almost everywhere,
which is the precise equality furnished by convergence (`app:not:fourier`). -/
theorem weakJet_zero_ae_of_tendsto_eLpNorm_two
    {ι : Type*} {l : Filter ι} [NeBot l] {m : ℕ}
    {f : ι → EuclideanSpace ℝ (Fin n) → F} {g : EuclideanSpace ℝ (Fin n) → F}
    {J : ι → (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F}
    {K : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n)) [×0]→L[ℝ] F}
    (hw : ∀ k, HasWeakJetOn volume (f k) (J k) U m)
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U))
    (hK : MemLp K 2 (volume.restrict U))
    (hflim : Tendsto (fun k ↦ eLpNorm (f k - g) 2 (volume.restrict U)) l (𝓝 0))
    (hJlim : Tendsto (fun k ↦ eLpNorm (J k 0 - K) 2 (volume.restrict U)) l (𝓝 0)) :
    K =ᵐ[volume.restrict U] iteratedFDeriv ℝ 0 g := by
  let L := (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin n)) F).symm
    |>.toContinuousLinearEquiv.toContinuousLinearMap
  have hJ (k : ι) : J k 0 = L ∘ f k := by
    rw [(hw k).1, iteratedFDeriv_zero_eq_comp]
    rfl
  have hJmem (k : ι) : MemLp (J k 0) 2 (volume.restrict U) := by
    rw [hJ k]
    exact L.comp_memLp' (hf k)
  have hgm : MemLp (iteratedFDeriv ℝ 0 g) 2 (volume.restrict U) := by
    rw [iteratedFDeriv_zero_eq_comp]
    exact L.comp_memLp' hg
  have hglim : Tendsto (fun k ↦ eLpNorm (J k 0 - iteratedFDeriv ℝ 0 g) 2
      (volume.restrict U)) l (𝓝 0) := by
    simp_rw [hJ, iteratedFDeriv_zero_eq_comp]
    exact tendsto_eLpNorm_compCLM_sub L hf hg hflim
  apply (hK.toLp_eq_toLp_iff hgm).mp
  exact tendsto_nhds_unique
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hJmem _ hK).mpr hJlim)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hJmem _ hgm).mpr hglim)

/-- Componentwise L² limits of finite weak jets give a weak jet of the chosen
function limit after normalizing order zero. The normalization preserves every
local L² class; no pointwise equality is inferred from convergence
(`app:ch_regular_base:lem:ball-extension`, `app:not:fourier`). -/
theorem hasWeakJetOn_normalize_of_tendsto_eLpNorm_two
    {ι : Type*} {l : Filter ι} [NeBot l] {m : ℕ}
    {f : ι → EuclideanSpace ℝ (Fin n) → F} {g : EuclideanSpace ℝ (Fin n) → F}
    {J : ι → (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F}
    {K : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F}
    (hw : ∀ k, HasWeakJetOn volume (f k) (J k) U m)
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U))
    (hJ : ∀ k j, j ≤ m → MemLp (J k j) 2 (volume.restrict U))
    (hK : ∀ j ≤ m, MemLp (K j) 2 (volume.restrict U))
    (hflim : Tendsto (fun k ↦ eLpNorm (f k - g) 2 (volume.restrict U)) l (𝓝 0))
    (hJlim : ∀ j ≤ m,
      Tendsto (fun k ↦ eLpNorm (J k j - K j) 2 (volume.restrict U)) l (𝓝 0)) :
    HasWeakJetOn volume g (normalizeWeakJet g K) U m ∧
      ∀ j, K j =ᵐ[volume.restrict U] normalizeWeakJet g K j := by
  have hzero := weakJet_zero_ae_of_tendsto_eLpNorm_two hw hf hg (hK 0 (Nat.zero_le m))
    hflim (hJlim 0 (Nat.zero_le m))
  refine ⟨hasWeakJetOn_of_tendsto_eLpNorm_two (l := l) hw hJ
    (fun j hj ↦ memLp_normalizeWeakJet hzero (hK j hj)) ?_ rfl, normalizeWeakJet_ae hzero⟩
  intro j hj
  apply (hJlim j hj).congr
  intro k
  exact eLpNorm_congr_ae (EventuallyEq.rfl.sub (normalizeWeakJet_ae hzero j))

/-- Lp limits of smooth finite jets give a weak jet representing the Lp
function limit. This is the completion-ready form of the closure theorem;
order zero is normalized without changing any Lp class
(`app:ch_regular_base:lem:ball-extension`, `app:not:fourier`). -/
theorem hasWeakJetOn_normalize_of_contDiff_tendsto_Lp
    {ι : Type*} {l : Filter ι} [NeBot l] {m : ℕ}
    {f : ι → EuclideanSpace ℝ (Fin n) → F}
    (u : Lp F 2 (volume.restrict U))
    (K : (j : ℕ) → Lp ((EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F) 2 (volume.restrict U))
    (hsmooth : ∀ k, ContDiff ℝ m (f k))
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict U))
    (hJ : ∀ k j, j ≤ m → MemLp (iteratedFDeriv ℝ j (f k)) 2 (volume.restrict U))
    (hflim : Tendsto (fun k ↦ (hf k).toLp (f k)) l (𝓝 u))
    (hJlim : ∀ j (hj : j ≤ m),
      Tendsto (fun k ↦ (hJ k j hj).toLp (iteratedFDeriv ℝ j (f k))) l (𝓝 (K j))) :
    HasWeakJetOn volume u (normalizeWeakJet u (fun j ↦ K j)) U m ∧
      ∀ j, (K j : EuclideanSpace ℝ (Fin n) → _) =ᵐ[volume.restrict U]
        normalizeWeakJet u (fun j ↦ K j) j := by
  apply hasWeakJetOn_normalize_of_tendsto_eLpNorm_two (l := l)
    (fun k ↦ hasWeakJetOn_of_contDiff volume (hsmooth k) U) hf (Lp.memLp u) hJ
    (fun j _ ↦ Lp.memLp (K j))
  · apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u (Lp.memLp u)).mp
    simpa only [Lp.toLp_coeFn] using hflim
  · intro j hj
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun k ↦ iteratedFDeriv ℝ j (f k)) (fun k ↦ hJ k j hj) (K j) (Lp.memLp (K j))).mp
    simpa only [Lp.toLp_coeFn] using hJlim j hj

end JanetCartan.Mollification
