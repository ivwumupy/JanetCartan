module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.StrongIntegral

/-!
# Compact regularizations of the elapsed graph

Continuity and integrability of the literal frequency-cut kernels precede the
strong-limit argument in `app:ch_regular_base:eq:fixed-time-representation`.
The auxiliary results below use only joint continuity and fixed compact carriers,
which the original smooth masked amplitudes supply. No operator-norm continuity
or test-kernel identity is assumed in these analytic results.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

open FourierIntegral

variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp V 2 (volume : Measure E)

/-- A jointly continuous compact physical representative gives a continuous
L²-valued curve. Consumer: compact-cutoff test orbits in
`app:ch_regular_base:eq:fixed-time-representation`. This concerns a single datum,
not continuity in operator norm. -/
theorem continuous_L2_of_compact_representative
    (g : ℝ → H) (F : ℝ → E → V)
    (hc : Continuous (Function.uncurry F)) {K : Set E} (hK : IsCompact K)
    (hs : ∀ r x, x ∉ K → F r x = 0)
    (he : ∀ r, g r =ᵐ[volume] F r) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro r₀
  let D : ℝ → E → V := fun r x ↦ F r x - F r₀ x
  have hD : Continuous (Function.uncurry D) :=
    hc.sub (hc.comp (continuous_const.prodMk continuous_snd))
  have hI : Continuous (fun r ↦ ∫ x in K, inner ℂ (D r x) (D r x)) :=
    continuous_parametric_integral_of_continuous (hD.inner hD) hK
  have hnorm (r : ℝ) : ‖g r - g r₀‖ =
      Real.sqrt ((∫ x in K, inner ℂ (D r x) (D r x)).re) := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), L2.inner_def]
    apply congrArg (fun z : ℂ ↦ Real.sqrt z.re)
    calc
      _ = ∫ x, inner ℂ (D r x) (D r x) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (g r) (g r₀), he r, he r₀] with x hx hr hr₀
        simp only [hx, Pi.sub_apply, hr, hr₀, D]
      _ = ∫ x in K, inner ℂ (D r x) (D r x) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
          simp [D, hs r x hx, hs r₀ x hx])).symm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp_rw [hnorm]
  simpa [Function.comp_def, D] using
    (Real.continuous_sqrt.comp (Complex.continuous_re.comp hI)).continuousAt.tendsto (x := r₀)

/-- Almost-everywhere identification with a compact continuous representative
suffices for measurability of an L²-valued curve. Consumer: cutoff operators
whose test realization is available only on the fixed elapsed-time slab in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem aestronglyMeasurable_L2_of_compact_representative
    (g : ℝ → H) (F : ℝ → E → V) (μ : Measure ℝ)
    (hc : Continuous (Function.uncurry F)) {K : Set E} (hK : IsCompact K)
    (hs : ∀ r x, x ∉ K → F r x = 0)
    (he : ∀ᵐ r ∂μ, g r =ᵐ[volume] F r) : AEStronglyMeasurable g μ := by
  have hf (r : ℝ) : MemLp (F r) 2 volume :=
    (hc.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
      (HasCompactSupport.intro hK (hs r))
  let g₀ : ℝ → H := fun r ↦ (hf r).toLp (F r)
  have hg₀ : Continuous g₀ := continuous_L2_of_compact_representative g₀ F hc hK hs
    (fun r ↦ (hf r).coeFn_toLp)
  apply hg₀.aestronglyMeasurable.congr
  filter_upwards [he] with r hr
  exact Lp.ext ((hf r).coeFn_toLp.trans hr.symm)

/-- Joint continuity of the full, source-first graph integrand. Consumer:
compact regularized kernels in `app:ch_regular_base:eq:fixed-time-representation`.
Both physical positions remain in the amplitude. -/
theorem continuous_graph_integrand
    (S : ℝ → E → E → ℝ) (A : ℝ → FullAmplitude n q)
    (hS : Continuous (fun p : (ℝ × E) × E ↦ S p.1.1 p.1.2 p.2))
    (hA : Continuous (fun p : ((ℝ × E) × E) × E ↦ A p.1.1.1 p.1.1.2 p.1.2 p.2))
    (u : E → Fin q → ℂ) (hu : Continuous u) :
    Continuous (fun p : ((ℝ × E) × E) × E ↦
      graphOscillation (S p.1.1.1) p.1.1.2 p.2 p.1.2 •
        (A p.1.1.1 p.1.1.2 p.2 p.1.2).mulVec (u p.2)) := by
  have hp : Continuous (fun p : ((ℝ × E) × E) × E ↦ S p.1.1.1 p.1.1.2 p.1.2) :=
    hS.comp continuous_fst
  have ha : Continuous (fun p : ((ℝ × E) × E) × E ↦
      A p.1.1.1 p.1.1.2 p.2 p.1.2) := hA.comp
    ((continuous_fst.fst.prodMk continuous_snd).prodMk continuous_fst.snd)
  have hg : Continuous (fun p : ((ℝ × E) × E) × E ↦
      graphOscillation (S p.1.1.1) p.1.1.2 p.2 p.1.2) := by
    exact (continuous_const.mul (Complex.continuous_ofReal.comp
      (hp.sub (continuous_snd.inner continuous_fst.snd)))).cexp
  exact hg.smul (ha.matrix_mulVec (hu.comp continuous_snd))

/-- Absolute integrability of the actual compact-cutoff source/frequency
integrand. Consumer: Fubini and Fourier splitting in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem integrable_compact_graph_integrand
    (S : ℝ → E → E → ℝ) (A : ℝ → FullAmplitude n q)
    (hS : Continuous (fun p : (ℝ × E) × E ↦ S p.1.1 p.1.2 p.2))
    (hA : Continuous (fun p : ((ℝ × E) × E) × E ↦ A p.1.1.1 p.1.1.2 p.1.2 p.2))
    {Y K : Set E} (hY : IsCompact Y) (hK : IsCompact K)
    (hs : ∀ r x z ξ, z ∉ Y ∨ ξ ∉ K → A r x z ξ = 0)
    (u : E → Fin q → ℂ) (hu : Continuous u) (r : ℝ) (x : E) :
    Integrable (fun p : E × E ↦ graphOscillation (S r) x p.2 p.1 •
      (A r x p.2 p.1).mulVec (u p.2)) (volume.prod volume) := by
  have hc : Continuous (fun p : E × E ↦ graphOscillation (S r) x p.2 p.1 •
      (A r x p.2 p.1).mulVec (u p.2)) :=
    (continuous_graph_integrand S A hS hA u hu).comp
      (f := fun p : E × E ↦ (((r, x), p.1), p.2))
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (hK.prod hY)
  intro p hp
  have hz : p.2 ∉ Y ∨ p.1 ∉ K := by tauto
  simp [hs r x p.2 p.1 hz]

/-- Joint continuity of the literal finite graph output in elapsed time and
physical output. The two iterated integrals are over fixed compact carriers.
Consumer: datum-wise measurability in
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem continuous_compact_graphTestOutput
    (S : ℝ → E → E → ℝ) (A : ℝ → FullAmplitude n q)
    (hS : Continuous (fun p : (ℝ × E) × E ↦ S p.1.1 p.1.2 p.2))
    (hA : Continuous (fun p : ((ℝ × E) × E) × E ↦ A p.1.1.1 p.1.1.2 p.1.2 p.2))
    {Y K : Set E} (hY : IsCompact Y) (hK : IsCompact K)
    (hs : ∀ r x z ξ, z ∉ Y ∨ ξ ∉ K → A r x z ξ = 0)
    (u : graphTestSpace n q) :
    Continuous (fun p : ℝ × E ↦ graphTestOutput (S p.1) (A p.1) u p.2) := by
  let f : ((ℝ × E) × E) × E → Fin q → ℂ := fun p ↦
    graphOscillation (S p.1.1.1) p.1.1.2 p.2 p.1.2 •
      (A p.1.1.1 p.1.1.2 p.2 p.1.2).mulVec (u.val p.2).ofLp
  have hf : Continuous f := continuous_graph_integrand S A hS hA _
    ((PiLp.continuous_ofLp 2 _).comp u.property.1.continuous)
  have hi : Continuous (fun p : (ℝ × E) × E ↦ ∫ z in Y, f (p, z)) :=
    continuous_parametric_integral_of_continuous hf hY
  have ho : Continuous (fun p : ℝ × E ↦ ∫ ξ in K, ∫ z in Y, f ((p, ξ), z)) :=
    continuous_parametric_integral_of_continuous hi hK
  have he (r : ℝ) (x ξ : E) : (∫ z, f (((r, x), ξ), z)) =
      ∫ z in Y, f (((r, x), ξ), z) := by
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz ↦ by
      simp [f, hs r x z ξ (Or.inl hz)])).symm
  have hk (r : ℝ) (x : E) : (∫ ξ, ∫ z in Y, f (((r, x), ξ), z)) =
      ∫ ξ in K, ∫ z in Y, f (((r, x), ξ), z) := by
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun ξ hξ ↦ by
      simp [f, hs r x _ ξ (Or.inr hξ)])).symm
  have heq : (fun p : ℝ × E ↦ graphTestOutput (S p.1) (A p.1) u p.2) =
      fun p ↦ WithLp.toLp 2 (((2 * Real.pi) ^ n : ℂ)⁻¹ •
        ∫ ξ in K, ∫ z in Y, f ((p, ξ), z)) := by
    funext p
    simp only [graphTestOutput, graphOperator]
    change WithLp.toLp 2 (_ • ∫ ξ, ∫ z, f ((p, ξ), z)) = _
    simp_rw [he, hk]
  rw [heq]
  exact (PiLp.continuous_toLp 2 _).comp (ho.const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹))

/-- Compact physical output support survives both integrations. Consumer:
the L² continuity step of `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem graphTestOutput_eq_zero_off_output
    (S : E → E → ℝ) (A : FullAmplitude n q) {X : Set E}
    (hs : ∀ x z ξ, x ∉ X → A x z ξ = 0)
    (u : graphTestSpace n q) (x : E) (hx : x ∉ X) :
    graphTestOutput S A u x = 0 := by
  simp [graphTestOutput, graphOperator, hs x _ _ hx]


/-- Joint continuity of the literal reverse integral, still in the original
`(x,z,ξ)` order. Consumer: adjoint measurability in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem continuous_compact_reverseGraphOutput
    (S : ℝ → E → E → ℝ) (A : ℝ → FullAmplitude n q)
    (hS : Continuous (fun p : (ℝ × E) × E ↦ S p.1.1 p.1.2 p.2))
    (hA : Continuous (fun p : ((ℝ × E) × E) × E ↦ A p.1.1.1 p.1.1.2 p.1.2 p.2))
    {X K : Set E} (hX : IsCompact X) (hK : IsCompact K)
    (hs : ∀ r x z ξ, x ∉ X ∨ ξ ∉ K → A r x z ξ = 0)
    (u : graphTestSpace n q) :
    Continuous (fun p : ℝ × E ↦ WithLp.toLp 2
      (reverseGraphOperator (S p.1) (A p.1) (fun x ↦ (u.val x).ofLp) p.2)) := by
  let f : ((ℝ × E) × E) × E → Fin q → ℂ := fun p ↦
    star (graphOscillation (S p.1.1.1) p.2 p.1.1.2 p.1.2) •
      (A p.1.1.1 p.2 p.1.1.2 p.1.2).mulVec (u.val p.2).ofLp
  have hp : Continuous (fun p : ((ℝ × E) × E) × E ↦ S p.1.1.1 p.2 p.1.2) :=
    hS.comp ((continuous_fst.fst.fst.prodMk continuous_snd).prodMk continuous_fst.snd)
  have ha : Continuous (fun p : ((ℝ × E) × E) × E ↦ A p.1.1.1 p.2 p.1.1.2 p.1.2) :=
    hA.comp (((continuous_fst.fst.fst.prodMk continuous_snd).prodMk
      continuous_fst.fst.snd).prodMk continuous_fst.snd)
  have hg : Continuous (fun p : ((ℝ × E) × E) × E ↦
      graphOscillation (S p.1.1.1) p.2 p.1.1.2 p.1.2) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (hp.sub (continuous_fst.fst.snd.inner continuous_fst.snd)))).cexp
  have hf : Continuous f := hg.star.smul (ha.matrix_mulVec
    (((PiLp.continuous_ofLp 2 _).comp u.property.1.continuous).comp continuous_snd))
  have hi : Continuous (fun p : (ℝ × E) × E ↦ ∫ x in X, f (p, x)) :=
    continuous_parametric_integral_of_continuous hf hX
  have ho : Continuous (fun p : ℝ × E ↦ ∫ ξ in K, ∫ x in X, f ((p, ξ), x)) :=
    continuous_parametric_integral_of_continuous hi hK
  have he (r : ℝ) (z ξ : E) : (∫ x, f (((r, z), ξ), x)) =
      ∫ x in X, f (((r, z), ξ), x) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      simp [f, hs r x z ξ (Or.inl hx)])).symm
  have hk (r : ℝ) (z : E) : (∫ ξ, ∫ x in X, f (((r, z), ξ), x)) =
      ∫ ξ in K, ∫ x in X, f (((r, z), ξ), x) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun ξ hξ ↦ by
      simp [f, hs r _ z ξ (Or.inr hξ)])).symm
  have heq : (fun p : ℝ × E ↦ WithLp.toLp 2
      (reverseGraphOperator (S p.1) (A p.1) (fun x ↦ (u.val x).ofLp) p.2)) =
      fun p ↦ WithLp.toLp 2 (((2 * Real.pi) ^ n : ℂ)⁻¹ •
        ∫ ξ in K, ∫ x in X, f ((p, ξ), x)) := by
    funext p
    change WithLp.toLp 2 (_ • ∫ ξ, ∫ x, f ((p, ξ), x)) = _
    simp_rw [he, hk]
  rw [heq]
  exact (PiLp.continuous_toLp 2 _).comp (ho.const_smul (((2 * Real.pi) ^ n : ℂ)⁻¹))

/-- The reverse output is supported in the original source mask. Consumer:
adjoint L² continuity in `app:ch_regular_base:lem:retarded-kernel`. -/
theorem reverseGraphOutput_eq_zero_off_source
    (S : E → E → ℝ) (A : FullAmplitude n q) {Y : Set E}
    (hs : ∀ x z ξ, z ∉ Y → A x z ξ = 0)
    (u : graphTestSpace n q) (z : E) (hz : z ∉ Y) :
    WithLp.toLp 2 (reverseGraphOperator S A (fun x ↦ (u.val x).ofLp) z) = 0 := by
  simp [reverseGraphOperator, hs _ z _ hz]

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
