module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.Volumes

/-!
# Summable majorants for two independent physical shell indices

These scalar estimates are consumed after `exists_normalizedPair_derivative_bound`
and `independent_frequency_size_le` in `app:ch_regular:eq:chain-tail`.
The integration threshold depends only on dimension and fixed symbol/output
orders. No ordering of the derivative scale and input frequency is imposed.
-/

@[expose] public noncomputable section
namespace JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable

set_option maxHeartbeats 800000

/-- Two extra integrations beyond the fixed real exponent give one inverse
factor for each independent shell radius. Their cost is a fixed power of
`L`, independent of accuracy, with no assumption `L ≤ ρ`
(`app:ch_regular:eq:chain-tail`). -/
theorem pair_power_le {ρ R L s t p : ℝ} (hρ : 0 < ρ) (hR : 1 ≤ R)
    (hL : 0 ≤ L) (hs : 0 < s) (ht : 0 < t)
    (hρR : ρ ≤ R) (hsR : s ≤ R) (htR : t ≤ R)
    (a q : ℕ) (hp : p ≤ (a : ℝ)) :
    R ^ p * (L / R) ^ (q + a + 2) ≤
      L ^ (a + 2) * (L / ρ) ^ q * (s⁻¹ * t⁻¹) := by
  have hR0 := zero_lt_one.trans_le hR
  have hpow : R ^ p ≤ R ^ a := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hR hp
  have hq : (L / R) ^ q ≤ (L / ρ) ^ q :=
    pow_le_pow_left₀ (div_nonneg hL hR0.le)
      (div_le_div_of_nonneg_left hL hρ hρR) q
  have hst : R⁻¹ * R⁻¹ ≤ s⁻¹ * t⁻¹ :=
    mul_le_mul ((inv_le_inv₀ hR0 hs).mpr hsR) ((inv_le_inv₀ hR0 ht).mpr htR)
      (inv_nonneg.mpr hR0.le) (inv_nonneg.mpr hs.le)
  calc
    _ ≤ R ^ a * (L / R) ^ (q + a + 2) :=
      mul_le_mul_of_nonneg_right hpow (pow_nonneg (div_nonneg hL hR0.le) _)
    _ = L ^ (a + 2) * (L / R) ^ q * (R⁻¹ * R⁻¹) := by
      rw [show q + a + 2 = q + (a + 2) by omega, pow_add, div_pow, div_pow,
        pow_add R a 2]
      field_simp
    _ ≤ _ := mul_le_mul
      (mul_le_mul_of_nonneg_left hq (pow_nonneg hL _)) hst
      (mul_nonneg (inv_nonneg.mpr hR0.le) (inv_nonneg.mpr hR0.le))
      (mul_nonneg (pow_nonneg hL _) (pow_nonneg (div_nonneg hL hρ.le) _))

/-- The majorant for expanding graph annuli and independent output cutoffs.
The output index zero is included (`app:ch_regular:eq:chain-tail`). -/
def expandingPairWeight (j k : ℕ) : ℝ := (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ k

/-- Contracting graph annuli keep their actual volume; only the output index
uses the large-frequency decay (`app:ch_regular:eq:chain-tail`). -/
def contractingPairWeight (n j k : ℕ) : ℝ :=
  (((2 : ℝ) ^ j)⁻¹) ^ n * (1 / 2 : ℝ) ^ k

/-- Radius used only for carrier-volume bookkeeping of the selected actual
graph annulus. Its symbol scale is `max 1 (branchRadius low j)`
(`app:ch_regular:eq:chain-tail`). -/
def branchRadius (low : Bool) (j : ℕ) : ℝ :=
  if low then ((2 : ℝ) ^ j)⁻¹ else (2 : ℝ) ^ j

/-- Every graph annulus has a strictly positive radius, with no uniform
positive lower bound required (`app:ch_regular:eq:chain-tail`). -/
theorem branchRadius_pos (low : Bool) (j : ℕ) : 0 < branchRadius low j := by
  cases low <;> simp only [branchRadius, Bool.false_eq_true, ↓reduceIte] <;> positivity

/-- A concrete integration radius for each independent cutoff pair. The
bounded output cutoff contributes radius one to this bookkeeping, while its
actual support lies in the fixed profile ball (`app:ch_regular:eq:chain-tail`). -/
def pairRadius (ρ : ℝ) (low : Bool) (j k : ℕ) : ℝ :=
  max ρ (max (branchRadius low j) ((2 : ℝ) ^ k))

/-- The concrete radius bounds every clipped symbol scale needed for the
actual high/low pair estimate (`app:ch_regular:eq:high-amplitude`). -/
theorem pairRadius_bounds {ρ : ℝ} (hρ : 1 ≤ ρ) (low : Bool) (j k : ℕ) :
    1 ≤ pairRadius ρ low j k ∧ ρ ≤ pairRadius ρ low j k ∧
      max 1 (branchRadius low j) ≤ pairRadius ρ low j k ∧
      (2 : ℝ) ^ k ≤ pairRadius ρ low j k := by
  have h₁ : ρ ≤ pairRadius ρ low j k := le_max_left _ _
  have h₂ : branchRadius low j ≤ pairRadius ρ low j k :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : (2 : ℝ) ^ k ≤ pairRadius ρ low j k :=
    (le_max_right _ _).trans (le_max_right _ _)
  exact ⟨hρ.trans h₁, h₁, max_le (hρ.trans h₁) h₂, h₃⟩

/-- A majorant on the independent graph/output index product. Source:
`app:ch_regular:eq:chain-tail`. -/
def pairWeight (low : Bool) (n j k : ℕ) : ℝ :=
  if low then contractingPairWeight n j k else expandingPairWeight j k

/-- Nonnegativity of the actual pair majorant
(`app:ch_regular:eq:chain-tail`). -/
theorem pairWeight_nonneg (low : Bool) (n j k : ℕ) : 0 ≤ pairWeight low n j k := by
  cases low <;> simp only [pairWeight, expandingPairWeight, contractingPairWeight,
    Bool.false_eq_true, ↓reduceIte] <;> positivity

/-- Expanding pair majorants are summable on the full independent product of
indices, without an assumed diagonal shell decomposition
(`app:ch_regular:eq:chain-tail`). -/
theorem summable_expandingPairWeight :
    Summable (fun p : ℕ × ℕ => expandingPairWeight p.1 p.2) :=
  (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_of_nonneg
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    (fun _ => by positivity) (fun _ => by positivity)

/-- Contracting pair majorants are summable in positive dimension, retaining
all arbitrarily small graph frequencies (`app:ch_regular:eq:chain-tail`). -/
theorem summable_contractingPairWeight {n : ℕ} (hn : 0 < n) :
    Summable (fun p : ℕ × ℕ => contractingPairWeight n p.1 p.2) :=
  summable_contracting_pair_volume hn
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    (fun _ => by positivity)

/-- Summability for each actual graph branch, including the bounded output
ball and all contracting graph annuli (`app:ch_regular:eq:chain-tail`). -/
theorem summable_pairWeight {n : ℕ} (hn : 0 < n) (low : Bool) :
    Summable (fun p : ℕ × ℕ => pairWeight low n p.1 p.2) := by
  cases low
  · exact summable_expandingPairWeight
  · exact summable_contractingPairWeight hn

/-- Every positive-dimensional branch has the same product-geometric upper
majorant. This gives a common bound on arbitrary finite collections of
physical pairs (`app:ch_regular:eq:chain-tail`). -/
theorem pairWeight_le_expanding {n : ℕ} (hn : 0 < n) (low : Bool) (j k : ℕ) :
    pairWeight low n j k ≤ expandingPairWeight j k := by
  cases low
  · exact le_rfl
  · change (((2 : ℝ) ^ j)⁻¹) ^ n * (1 / 2 : ℝ) ^ k ≤ _
    have hj : ((2 : ℝ) ^ j)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hp := pow_le_pow_of_le_one (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ j)⁻¹)
      hj (show 1 ≤ n by omega)
    have he : (((2 : ℝ) ^ j)⁻¹) ^ n ≤ (1 / 2 : ℝ) ^ j := by
      simpa only [pow_one, inv_pow, one_div] using hp
    exact mul_le_mul_of_nonneg_right he (by positivity)

/-- The full independent-index geometric mass is four. This is the fixed
global zeroth-kernel majorant factor, independent of external positions and
the shell truncation (`app:ch_regular:eq:chain-tail`). -/
theorem tsum_expandingPairWeight :
    (∑' p : ℕ × ℕ, expandingPairWeight p.1 p.2) = 4 := by
  have hsum := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  change (∑' p : ℕ × ℕ, (1 / 2 : ℝ) ^ p.1 * (1 / 2 : ℝ) ^ p.2) = 4
  rw [← hsum.summable.tsum_mul_tsum hsum.summable summable_expandingPairWeight]
  rw [hsum.tsum_eq]
  norm_num

/-- Summing either noncomparable branch costs at most four, including the
bounded output ball and the infinite low graph tail
(`app:ch_regular:eq:chain-tail`). -/
theorem tsum_pairWeight_le_four {n : ℕ} (hn : 0 < n) (low : Bool) :
    (∑' p : ℕ × ℕ, pairWeight low n p.1 p.2) ≤ 4 := by
  have h : (∑' p : ℕ × ℕ, pairWeight low n p.1 p.2) ≤
      ∑' p : ℕ × ℕ, expandingPairWeight p.1 p.2 :=
    (summable_pairWeight hn low).tsum_le_tsum
      (fun p => pairWeight_le_expanding hn low p.1 p.2) summable_expandingPairWeight
  exact h.trans_eq tsum_expandingPairWeight

/-- A globally uniform majorant for every finite collection of pair weights,
including rectangular cutoff partial sums. The actual kernel estimate
multiplies this by its uniform `q = m = 0` coefficient
(`app:ch_regular:eq:chain-tail`). -/
theorem sum_pairWeight_le_four {n : ℕ} (hn : 0 < n) (low : Bool)
    (s : Finset (ℕ × ℕ)) : ∑ p ∈ s, pairWeight low n p.1 p.2 ≤ 4 :=
  ((summable_pairWeight hn low).sum_le_tsum s
    (fun p _ => pairWeight_nonneg low n p.1 p.2)).trans (tsum_pairWeight_le_four hn low)

/-- The complete expanding-pair scalar factor after its three physical
Fourier measures. Choose `a` above `2*n+p`; the loss `a+2` is fixed before
accuracy `q`. The remaining power of the input scale is exactly `ρ^n`
(`app:ch_regular:eq:chain-tail`). -/
theorem expanding_pair_size_le {ρ R L p : ℝ} (hρ : 0 < ρ) (hR : 1 ≤ R)
    (hL : 0 ≤ L) (hρR : ρ ≤ R) (n j k a q : ℕ)
    (hj : (2 : ℝ) ^ j ≤ R) (hk : (2 : ℝ) ^ k ≤ R)
    (hp : (2 * n : ℕ) + p ≤ (a : ℝ)) :
    (ρ ^ n * ((2 : ℝ) ^ j) ^ n * ((2 : ℝ) ^ k) ^ n) * R ^ p *
        (L / R) ^ (q + a + 2) ≤
      ρ ^ n * L ^ (a + 2) * (L / ρ) ^ q * expandingPairWeight j k := by
  have hR0 := zero_lt_one.trans_le hR
  have hv : (((2 : ℝ) ^ j) ^ n * ((2 : ℝ) ^ k) ^ n) * R ^ p ≤
      R ^ ((2 * n : ℕ) + p : ℝ) := by
    calc
      _ ≤ (R ^ n * R ^ n) * R ^ p :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (pow_le_pow_left₀ (by positivity) hj n)
            (pow_le_pow_left₀ (by positivity) hk n) (by positivity) (by positivity))
          (Real.rpow_nonneg hR0.le p)
      _ = _ := by
        rw [Real.rpow_add hR0, Real.rpow_natCast, show 2 * n = n + n by omega, pow_add]
  have hb := pair_power_le hρ hR hL (by positivity : (0 : ℝ) < 2 ^ j)
    (by positivity : (0 : ℝ) < 2 ^ k) hρR hj hk a q hp
  calc
    _ = ρ ^ n * ((((2 : ℝ) ^ j) ^ n * ((2 : ℝ) ^ k) ^ n) * R ^ p) *
        (L / R) ^ (q + a + 2) := by ring
    _ ≤ ρ ^ n * (R ^ ((2 * n : ℕ) + p : ℝ) * (L / R) ^ (q + a + 2)) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv (pow_nonneg hρ.le n))
          (pow_nonneg (div_nonneg hL hR0.le) (q + a + 2))
    _ ≤ ρ ^ n * (L ^ (a + 2) * (L / ρ) ^ q *
        (((2 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ k)⁻¹)) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hρ.le n)
    _ = _ := by simp only [expandingPairWeight, inv_pow, one_div]; ring

/-- The contracting-pair scalar factor keeps its shrinking graph volume.
The threshold is fixed above `n+p`, and the output index still includes its
bounded-frequency ball (`app:ch_regular:eq:chain-tail`). -/
theorem contracting_pair_size_le {ρ R L p : ℝ} (hρ : 0 < ρ) (hR : 1 ≤ R)
    (hL : 0 ≤ L) (hρR : ρ ≤ R) (n j k a q : ℕ)
    (hk : (2 : ℝ) ^ k ≤ R) (hp : (n : ℝ) + p ≤ (a : ℝ)) :
    (ρ ^ n * (((2 : ℝ) ^ j)⁻¹) ^ n * ((2 : ℝ) ^ k) ^ n) * R ^ p *
        (L / R) ^ (q + a + 2) ≤
      ρ ^ n * L ^ (a + 2) * (L / ρ) ^ q * contractingPairWeight n j k := by
  have hR0 := zero_lt_one.trans_le hR
  have hv : ((2 : ℝ) ^ k) ^ n * R ^ p ≤ R ^ ((n : ℝ) + p) := by
    rw [Real.rpow_add hR0, Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hk n)
      (Real.rpow_nonneg hR0.le p)
  have hb := pair_power_le hρ hR hL (by norm_num : (0 : ℝ) < 1)
    (by positivity : (0 : ℝ) < 2 ^ k) hρR hR hk a q hp
  calc
    _ = (ρ ^ n * (((2 : ℝ) ^ j)⁻¹) ^ n) *
        (((2 : ℝ) ^ k) ^ n * R ^ p) * (L / R) ^ (q + a + 2) := by ring
    _ ≤ (ρ ^ n * (((2 : ℝ) ^ j)⁻¹) ^ n) *
        (R ^ ((n : ℝ) + p) * (L / R) ^ (q + a + 2)) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv
          (by positivity : 0 ≤ ρ ^ n * (((2 : ℝ) ^ j)⁻¹) ^ n))
          (pow_nonneg (div_nonneg hL hR0.le) (q + a + 2))
    _ ≤ (ρ ^ n * (((2 : ℝ) ^ j)⁻¹) ^ n) *
        (L ^ (a + 2) * (L / ρ) ^ q * ((1 : ℝ)⁻¹ * ((2 : ℝ) ^ k)⁻¹)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by simp only [contractingPairWeight, inv_pow, one_div, inv_one, one_mul]; ring

end JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable
