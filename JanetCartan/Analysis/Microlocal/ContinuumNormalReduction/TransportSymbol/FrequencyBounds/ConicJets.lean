module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.HighFrequency

/-!
# Mixed jets under positive frequency dilation

The derivative bookkeeping in `app:ch_background:prop:bg-frame`, Step 1.
The consumer is the normalized-shell estimate in `TransportSymbol`: a frequency
slot lowers the degree by one, while either physical-position slot preserves it.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- The invertible linear dilation used to differentiate
`app:ch_background:eq:bg-symbol`; both physical positions are retained. -/
def frequencyDilationEquiv (t : ℝ) (ht : t ≠ 0) : Variables n ≃L[ℝ] Variables n where
  toFun := scaleFrequency t
  invFun := scaleFrequency t⁻¹
  left_inv p := by simp [scaleFrequency, smul_smul, ht]
  right_inv p := by simp [scaleFrequency, smul_smul, ht]
  map_add' p q := by simp [scaleFrequency, smul_add]
  map_smul' r p := by simp [scaleFrequency, smul_smul, mul_comm]
  continuous_toFun := continuous_fst.prodMk
    (continuous_snd.fst.prodMk (continuous_snd.snd.const_smul t))
  continuous_invFun := continuous_fst.prodMk
    (continuous_snd.fst.prodMk (continuous_snd.snd.const_smul t⁻¹))

/-- Differentiating a local positive-dilation identity in all variables.
No symbol bound is an input. Source: `app:ch_background:eq:bg-symbol`. -/
theorem iteratedFDeriv_dilation_identity {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : Variables n → G) {t : ℝ} (ht : 0 < t) (p : Variables n)
    (h : (fun q ↦ f (scaleFrequency t q)) =ᶠ[𝓝 p] f)
    (j : ℕ) (v : Fin j → Variables n) :
    iteratedFDeriv ℝ j f (scaleFrequency t p) (fun i ↦ scaleFrequency t (v i)) =
      iteratedFDeriv ℝ j f p v := by
  have he := (frequencyDilationEquiv (n := n) t ht.ne').iteratedFDerivWithin_comp_right
    f uniqueDiffOn_univ (x := p) (mem_univ _) j
  simp only [preimage_univ, iteratedFDerivWithin_univ] at he
  have hh := (h.iteratedFDeriv ℝ j).eq_of_nhds
  exact (congrArg (fun A ↦ A v) he).symm.trans (congrArg (fun A ↦ A v) hh)

/-- An arbitrary set of frequency slots contributes exactly its cardinality
to the negative degree; the remaining slots can involve both positions.
Source: `app:ch_background:prop:bg-frame`, Step 1. -/
theorem iteratedFDeriv_mixed_frequency_scaling {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : Variables n → G) {t : ℝ} (ht : 0 < t) (p : Variables n)
    (h : (fun q ↦ f (scaleFrequency t q)) =ᶠ[𝓝 p] f)
    (j : ℕ) (S : Finset (Fin j)) (v : Fin j → Variables n)
    (hk : ∀ i ∈ S, (v i).1 = 0 ∧ (v i).2.1 = 0)
    (hx : ∀ i ∉ S, (v i).2.2 = 0) :
    iteratedFDeriv ℝ j f (scaleFrequency t p) v =
      (t ^ S.card)⁻¹ • iteratedFDeriv ℝ j f p v := by
  have hd (i : Fin j) : scaleFrequency t (v i) = (if i ∈ S then t else 1) • v i := by
    by_cases hi : i ∈ S
    · obtain ⟨h₁, h₂⟩ := hk i hi
      ext <;> simp [scaleFrequency, hi, h₁, h₂]
    · ext <;> simp [scaleFrequency, hi, hx i hi]
  have he := iteratedFDeriv_dilation_identity f ht p h j v
  simp_rw [hd] at he
  rw [ContinuousMultilinearMap.map_smul_univ] at he
  simp only [Fintype.prod_ite_mem, Finset.prod_const] at he
  rw [← he, inv_smul_smul₀ (pow_ne_zero _ ht.ne')]

/-- A nonzero dilation weight is divided by one factor of `t` per frequency
slot. Taking `c = t^m` gives degree `m - |β|`, including the primitive inverse
and Jacobian degrees. Positions remain unscaled. Source:
`app:ch_background:eq:bg-jacobian` and `app:ch_background:prop:bg-frame`, Step 1. -/
theorem iteratedFDeriv_weighted_mixed_frequency_scaling {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : Variables n → G) {t c : ℝ} (ht : 0 < t) (hc : c ≠ 0) (p : Variables n)
    (h : (fun q ↦ f (scaleFrequency t q)) =ᶠ[𝓝 p] (fun q ↦ c • f q))
    (j : ℕ) (S : Finset (Fin j)) (v : Fin j → Variables n)
    (hk : ∀ i ∈ S, (v i).1 = 0 ∧ (v i).2.1 = 0)
    (hx : ∀ i ∉ S, (v i).2.2 = 0) :
    iteratedFDeriv ℝ j f (scaleFrequency t p) v =
      (c / t ^ S.card) • iteratedFDeriv ℝ j f p v := by
  let e : G ≃L[ℝ] G := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  have he := (frequencyDilationEquiv (n := n) t ht.ne').iteratedFDerivWithin_comp_right
    f uniqueDiffOn_univ (x := p) (mem_univ _) j
  simp only [preimage_univ, iteratedFDerivWithin_univ] at he
  have hleft : iteratedFDeriv ℝ j (fun q ↦ c • f q) p =
      c • iteratedFDeriv ℝ j f p := e.iteratedFDeriv_comp_left
  have hj := (congrArg (fun A ↦ A v) he).symm.trans
    (congrArg (fun A ↦ A v) ((h.iteratedFDeriv ℝ j).eq_of_nhds.trans hleft))
  change iteratedFDeriv ℝ j f (scaleFrequency t p)
    (fun i ↦ scaleFrequency t (v i)) = c • iteratedFDeriv ℝ j f p v at hj
  have hd (i : Fin j) : scaleFrequency t (v i) = (if i ∈ S then t else 1) • v i := by
    by_cases hi : i ∈ S
    · obtain ⟨h₁, h₂⟩ := hk i hi
      ext <;> simp [scaleFrequency, hi, h₁, h₂]
    · ext <;> simp [scaleFrequency, hi, hx i hi]
  simp_rw [hd] at hj
  rw [ContinuousMultilinearMap.map_smul_univ] at hj
  simp only [Fintype.prod_ite_mem, Finset.prod_const] at hj
  calc
    _ = (t ^ S.card)⁻¹ • ((t ^ S.card) • iteratedFDeriv ℝ j f
        (scaleFrequency t p) v) := (inv_smul_smul₀ (pow_ne_zero _ ht.ne') _).symm
    _ = _ := by rw [hj, smul_smul]; congr 1; ring

/-- Actual homogeneous amplitude jets, derived from primitive chart, inverse,
and Jacobian scaling, with no parity assumption on angular masks. The literal
spectator integral is unchanged. Source: `app:ch_background:eq:bg-symbol`. -/
theorem iteratedFDeriv_homogeneousAmplitude_mixed_scaling
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    {t : ℝ} (ht : 0 < t)
    (hΩ : ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (hu : ∀ p ∈ Ω, u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2))
    (hJ : ∀ p ∈ Ω, J (scaleInput t (inverseCoordinates u p)) =
      t * J (inverseCoordinates u p))
    (p : Variables n) (j : ℕ) (S : Finset (Fin j)) (v : Fin j → Variables n)
    (hk : ∀ i ∈ S, (v i).1 = 0 ∧ (v i).2.1 = 0)
    (hx : ∀ i ∉ S, (v i).2.2 = 0) :
    iteratedFDeriv ℝ j (amplitude (homogeneousCoefficients a) J u Ω K)
        (scaleFrequency t p) v =
      (t ^ S.card)⁻¹ • iteratedFDeriv ℝ j
        (amplitude (homogeneousCoefficients a) J u Ω K) p v := by
  apply iteratedFDeriv_mixed_frequency_scaling _ ht p _ j S v hk hx
  exact Filter.Eventually.of_forall (amplitude_homogeneous a J u Ω K ht hΩ hu hJ)

end JanetCartan.ContinuumNormalReduction.TransportSymbol
