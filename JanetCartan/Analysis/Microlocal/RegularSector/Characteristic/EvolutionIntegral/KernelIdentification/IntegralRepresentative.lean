module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.CompactKernels
/-!
# L² integrals of compact kernel representatives

The compact forward and reverse kernels in
`app:ch_regular_base:eq:fixed-time-representation` must represent the actual
L²-valued time integral. Test-space density and compact Fubini prove this
without evaluating arbitrary L² classes at points.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open FourierIntegral
variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp V 2 (volume : Measure E)

/-- A continuous compact kernel represents the datum-wise L² integral.
Consumer: the forward and reversed retarded regularizations in
`app:ch_regular_base:eq:fixed-time-representation`. The representative is
proved by testing against the dense compact smooth domain and applying Fubini. -/
theorem integral_L2_eq_compact_representative
    (g : ℝ → H) (F : ℝ → E → V) (Δ : ℝ)
    (hc : Continuous (Function.uncurry F)) {K : Set E} (hK : IsCompact K)
    (hs : ∀ r x, x ∉ K → F r x = 0)
    (he : ∀ᵐ r ∂volume.restrict (Icc 0 Δ), g r =ᵐ[volume] F r) :
    (∫ r in Icc 0 Δ, g r) =ᵐ[volume] fun x ↦ ∫ r in Icc 0 Δ, F r x := by
  have hf (r : ℝ) : MemLp (F r) 2 volume :=
    (hc.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
      (HasCompactSupport.intro hK (hs r))
  let g₀ : ℝ → H := fun r ↦ (hf r).toLp (F r)
  have hg₀ : Continuous g₀ := continuous_L2_of_compact_representative g₀ F hc hK hs
    (fun r ↦ (hf r).coeFn_toLp)
  have hgg : g =ᵐ[volume.restrict (Icc 0 Δ)] g₀ := by
    filter_upwards [he] with r hr
    exact Lp.ext (hr.trans (hf r).coeFn_toLp.symm)
  rw [integral_congr_ae hgg]
  let J : E → V := fun x ↦ ∫ r in Icc 0 Δ, F r x
  have hswap : Continuous (fun p : E × ℝ ↦ F p.2 p.1) :=
    hc.comp (continuous_snd.prodMk continuous_fst)
  have hJ : Continuous J := continuous_parametric_integral_of_continuous
    hswap (isCompact_Icc : IsCompact (Icc (0 : ℝ) Δ))
  have hJs (x : E) (hx : x ∉ K) : J x = 0 := by simp [J, hs _ x hx]
  have hJlp : MemLp J 2 volume := hJ.memLp_of_hasCompactSupport
    (HasCompactSupport.intro hK hJs)
  have hLp : (∫ r in Icc 0 Δ, g₀ r) = hJlp.toLp J := by
    apply denseRange_graphTestToLp.eq_of_inner_right ℂ
    intro v
    rw [← integral_inner hg₀.integrableOn_Icc]
    have hp (r : ℝ) : inner ℂ (graphTestToLp v) (g₀ r) =
        ∫ x in K, inner ℂ (v.val x) (F r x) := by
      rw [L2.inner_def]
      calc
        _ = ∫ x, inner ℂ (v.val x) (F r x) := by
          apply integral_congr_ae
          filter_upwards [(graphTest_memLp v).coeFn_toLp, (hf r).coeFn_toLp] with x hx hx'
          change (graphTestToLp v) x = v.val x at hx
          change g₀ r x = F r x at hx'
          rw [hx, hx']
        _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx ↦ by simp [hs r x hx])).symm
    simp_rw [hp]
    have hpcont : Continuous (fun p : ℝ × E ↦ inner ℂ (v.val p.2) (F p.1 p.2)) :=
      (v.property.1.continuous.comp continuous_snd).inner hc
    have hpi : Integrable (fun p : ℝ × E ↦ inner ℂ (v.val p.2) (F p.1 p.2))
        ((volume.restrict (Icc 0 Δ)).prod (volume.restrict K)) := by
      rw [Measure.prod_restrict]
      exact hpcont.continuousOn.integrableOn_compact (isCompact_Icc.prod hK)
    rw [integral_integral_swap hpi]
    have hint (x : E) : (∫ r in Icc 0 Δ, inner ℂ (v.val x) (F r x)) =
        inner ℂ (v.val x) (J x) :=
      integral_inner (hc.comp (continuous_id.prodMk continuous_const)).integrableOn_Icc _
    simp_rw [hint]
    rw [L2.inner_def]
    calc
      _ = ∫ x, inner ℂ (v.val x) (J x) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx ↦ by simp [hJs x hx])
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [(graphTest_memLp v).coeFn_toLp, hJlp.coeFn_toLp] with x hx hx'
        change (graphTestToLp v) x = v.val x at hx
        rw [hx, hx']
  rw [hLp]
  exact hJlp.coeFn_toLp
end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
