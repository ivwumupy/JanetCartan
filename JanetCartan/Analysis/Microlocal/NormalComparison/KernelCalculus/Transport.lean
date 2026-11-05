module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Transport.ParameterIntegral
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Transport.PhaseCalculus

/-!
# Compact scalar-entry normal transport

Differentiation and integration by parts in the original input variable for
`app:ch_osc:prop:osc-normal`. The mask is smooth only on the open input domain.
Only its value and first input derivatives occur in the resulting formula.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan.NormalComparison

open CompactTransport

variable {n : ℕ}

/-- Scalar-entry transport in `app:ch_osc:prop:osc-normal`. The functions `Φ,A,w`
may retain any independent spectator parameters, in particular both physical
positions. The common carrier is compact inside `D`; it supplies all integrability
and boundary cancellation. The sole geometric premise is the pointwise phase
velocity identity. No bounds on higher mask derivatives are used. -/
theorem hasDerivAt_compact_transport_on_support
    {U : Set ℝ} {D S : Set (Euclidean n)}
    (hU : IsOpen U) (hD : IsOpen D) (hS : IsCompact S) (hSD : S ⊆ D)
    {Φ : ℝ × Euclidean n → ℝ} {A : ℝ × Euclidean n → ℂ}
    {w : Euclidean n → Euclidean n} {m : Euclidean n → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hA : ContDiff ℝ ∞ A)
    (hw : ContDiffOn ℝ ∞ w D) (hm : ContDiffOn ℝ ∞ m D)
    (hs : ∀ t ∈ U, tsupport (fun u ↦ A (t, u)) ⊆ S)
    {s : ℝ} (hsU : s ∈ U) (K : ℝ)
    (hv : ∀ u ∈ D, A (s, u) ≠ 0 → deriv (fun t ↦ Φ (t, u)) s =
      fderiv ℝ (fun v ↦ Φ (s, v)) u (w u)) :
    HasDerivAt (fun t ↦ ∫ u in D, oscillatoryFactor K (Φ (t, u)) * (m u • A (t, u)))
      (∫ u in D, oscillatoryFactor K (Φ (s, u)) *
        (m u • transportCoefficient (fun v ↦ deriv (fun t ↦ A (t, v)) s)
          (fun j v ↦ w v j • A (s, v)) u +
        ∑ j, partialDeriv m u j • (-(w u j • A (s, u))))) s := by
  let E : ℝ × Euclidean n → ℂ := fun p ↦ oscillatoryFactor K (Φ p)
  let Aε : Euclidean n → ℂ := fun u ↦ deriv (fun t ↦ A (t, u)) s
  let B : Fin n → Euclidean n → ℂ := fun j u ↦ w u j • A (s, u)
  have hE : ContDiff ℝ ∞ E := contDiff_oscillatoryFactor hΦ K
  have hEs : ContDiff ℝ ∞ (fun u ↦ E (s, u)) :=
    hE.comp (contDiff_const.prodMk contDiff_id)
  have hAs : ContDiff ℝ ∞ (fun u ↦ A (s, u)) :=
    hA.comp (contDiff_const.prodMk contDiff_id)
  have hAε : ContDiff ℝ ∞ Aε := contDiff_parameterDeriv hA s
  have hzero : ∀ t ∈ U, ∀ u ∉ S, A (t, u) = 0 := fun t ht u hu ↦
    image_eq_zero_of_notMem_tsupport (f := fun v ↦ A (t, v))
      (fun h ↦ hu (hs t ht h))
  have hsAε : tsupport Aε ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro u hu
    by_contra h
    exact hu (deriv_eq_zero_off_carrier hU hzero hsU h)
  have hcAε : HasCompactSupport Aε := hS.of_isClosed_subset (isClosed_tsupport _) hsAε
  have hB (j : Fin n) : ContDiff ℝ ∞ (B j) := by
    have hwj : ContDiffOn ℝ ∞ (fun u ↦ w u j) D :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) j).contDiff.comp_contDiffOn hw
    exact contDiff_mask_smul hD hwj hAs ((hs s hsU).trans hSD)
  have hsB (j : Fin n) : tsupport (B j) ⊆ S :=
    (tsupport_smul_subset_right (fun u ↦ w u j) (fun u ↦ A (s, u))).trans (hs s hsU)
  have hcB (j : Fin n) : HasCompactSupport (B j) :=
    hS.of_isClosed_subset (isClosed_tsupport _) (hsB j)
  have hF : ContDiffOn ℝ ∞ (fun p : ℝ × Euclidean n ↦ E p * (m p.2 • A p))
      (U ×ˢ D) := by
    exact hE.contDiffOn.mul
      ((hm.comp contDiffOn_snd (fun _ hp ↦ hp.2)).smul hA.contDiffOn)
  have hd := hasDerivAt_integral_carrier hU hD hS hSD hF
    (fun t ht u hu ↦ by simp [hzero t ht u hu]) hsU
  have hpoint (u : Euclidean n) (hu : u ∈ D) :
      deriv (fun t ↦ E (t, u) * (m u • A (t, u))) s =
        E (s, u) * (m u • Aε u) +
          ∑ j, partialDeriv (fun v ↦ E (s, v)) u j * (m u • B j u) := by
    have he : DifferentiableAt ℝ (fun t ↦ E (t, u)) s :=
      (hE.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) s
    have ha : DifferentiableAt ℝ (fun t ↦ A (t, u)) s :=
      (hA.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) s
    have hh := (he.hasDerivAt.fun_mul (ha.hasDerivAt.const_smul (m u))).deriv
    dsimp only [Pi.smul_apply] at hh
    rw [hh]
    change deriv (fun t ↦ oscillatoryFactor K (Φ (t, u))) s * (m u • A (s, u)) +
      E (s, u) * (m u • Aε u) = _
    by_cases hz : A (s, u) = 0
    · simp [B, hz]
    rw [deriv_oscillatoryFactor_transport hΦ s K u (w u) (hv u hu hz)]
    rw [add_comm]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [B, E]
    ring
  have hint := integral_transport_expansion hD hm hEs hAε hcAε (hsAε.trans hSD)
    hB hcB (fun j ↦ (hsB j).trans hSD)
  apply hd.congr_deriv
  calc
    _ = ∫ u in D, E (s, u) * (m u • Aε u) +
        ∑ j, partialDeriv (fun v ↦ E (s, v)) u j * (m u • B j u) :=
      setIntegral_congr_fun hD.measurableSet hpoint
    _ = _ := hint

/-- The original everywhere-on-domain form of compact transport, obtained
from support-local transport (`app:ch_osc:prop:osc-normal`). -/
theorem hasDerivAt_compact_transport
    {U : Set ℝ} {D S : Set (Euclidean n)}
    (hU : IsOpen U) (hD : IsOpen D) (hS : IsCompact S) (hSD : S ⊆ D)
    {Φ : ℝ × Euclidean n → ℝ} {A : ℝ × Euclidean n → ℂ}
    {w : Euclidean n → Euclidean n} {m : Euclidean n → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hA : ContDiff ℝ ∞ A)
    (hw : ContDiffOn ℝ ∞ w D) (hm : ContDiffOn ℝ ∞ m D)
    (hs : ∀ t ∈ U, tsupport (fun u ↦ A (t, u)) ⊆ S)
    {s : ℝ} (hsU : s ∈ U) (K : ℝ)
    (hv : ∀ u ∈ D, deriv (fun t ↦ Φ (t, u)) s =
      fderiv ℝ (fun v ↦ Φ (s, v)) u (w u)) :
    HasDerivAt (fun t ↦ ∫ u in D, oscillatoryFactor K (Φ (t, u)) * (m u • A (t, u)))
      (∫ u in D, oscillatoryFactor K (Φ (s, u)) *
        (m u • transportCoefficient (fun v ↦ deriv (fun t ↦ A (t, v)) s)
          (fun j v ↦ w v j • A (s, v)) u +
        ∑ j, partialDeriv m u j • (-(w u j • A (s, u))))) s :=
  hasDerivAt_compact_transport_on_support hU hD hS hSD hΦ hA hw hm hs hsU K
    (fun u hu _ ↦ hv u hu)

/-- The literal two-position scalar-entry formula from
`app:ch_osc:prop:osc-normal`, with `Φ = φ(s,x,u) - φ(s,y,u)`. Both positions are
independent. The parent can instantiate `A = aᵢ(s,x,u) * star(aⱼ(s,y,u))` and
multiply by the constant normalization squared. The coefficients are exactly
`c₀ = ∂s A - ∑ⱼ ∂uⱼ(wⱼ A)` and `cⱼ = -wⱼ A`. -/
theorem hasDerivAt_twoPosition_transport
    {U : Set ℝ} {D S : Set (Euclidean n)}
    (hU : IsOpen U) (hD : IsOpen D) (hS : IsCompact S) (hSD : S ⊆ D)
    (φ : ℝ → Euclidean n → Euclidean n → ℝ)
    (A : ℝ → Euclidean n → Euclidean n → Euclidean n → ℂ)
    (w : ℝ → Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (m : Euclidean n → ℝ) (x y : Euclidean n)
    (hφx : ContDiff ℝ ∞ (fun p : ℝ × Euclidean n ↦ φ p.1 x p.2))
    (hφy : ContDiff ℝ ∞ (fun p : ℝ × Euclidean n ↦ φ p.1 y p.2))
    (hA : ContDiff ℝ ∞ (fun p : ℝ × Euclidean n ↦ A p.1 x y p.2))
    (hm : ContDiffOn ℝ ∞ m D)
    (hs : ∀ t ∈ U, tsupport (A t x y) ⊆ S)
    {s : ℝ} (hsU : s ∈ U) (hw : ContDiffOn ℝ ∞ (w s x y) D) (K : ℝ)
    (hv : ∀ u ∈ D, deriv (fun t ↦ φ t x u - φ t y u) s =
      fderiv ℝ (fun v ↦ φ s x v - φ s y v) u (w s x y u)) :
    HasDerivAt
      (fun t ↦ ∫ u in D, oscillatoryFactor K (φ t x u - φ t y u) * A t x y u * (m u : ℂ))
      (∫ u in D, oscillatoryFactor K (φ s x u - φ s y u) *
        (transportCoefficient (fun v ↦ deriv (fun t ↦ A t x y v) s)
          (fun j v ↦ (w s x y v j : ℂ) * A s x y v) u * (m u : ℂ) +
        ∑ j, (-((w s x y u j : ℂ) * A s x y u)) * ((partialDeriv m u j : ℝ) : ℂ))) s := by
  have h := hasDerivAt_compact_transport hU hD hS hSD (hφx.sub hφy) hA hw hm hs hsU K hv
  simpa only [Complex.real_smul, mul_assoc, mul_comm, mul_left_comm] using h

end JanetCartan.NormalComparison
