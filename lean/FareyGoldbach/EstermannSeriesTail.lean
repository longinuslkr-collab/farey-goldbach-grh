import FareyGoldbach.PrimeSums

/-! # Positivity before truncation and the geometric analytic tail -/

open Finset

namespace FareyGoldbach

theorem estermann_real_tail_lower {t B p value : ℝ} {K : ℕ} (ht : 1<t) (hK : 1≤K)
    (b : ℕ→ℝ) (hb₀ : 1≤b 0+p) (hb : ∀ n,0≤b n+p)
    (hsum : HasSum (fun n => t^n*b n) value)
    (hbound : ∀ n, -B*(3/4:ℝ)^n≤t^n*b n) (hcut : 4*B*(3/4:ℝ)^K≤1/2) :
    1/2-p/(t-1)*t^K ≤ value-p/(t-1) := by
  let v (n : ℕ) := t^n*b n
  have hpre : 1≤∑ n∈range K,t^n*(b n+p) := by
    apply hb₀.trans
    have h := Finset.single_le_sum (s:=range K) (f:=fun n => t^n*(b n+p))
      (fun n _ => mul_nonneg (pow_nonneg (zero_lt_one.trans ht).le n) (hb n))
      (Finset.mem_range.mpr (by omega : 0<K))
    simpa only [pow_zero,one_mul] using h
  simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul] at hpre
  have hz : HasSum v value := hsum
  have htail := (hasSum_nat_add_iff' K).mpr hz
  have hgeom := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤3/4)
    (by norm_num : (3/4:ℝ)<1)).mul_left (-B*(3/4:ℝ)^K)
  have hpoint (n : ℕ) : -B*(3/4:ℝ)^K*(3/4:ℝ)^n≤v (n+K) := by
    apply le_trans _ (hbound (n+K))
    rw [pow_add]
    exact le_of_eq (by ring)
  have hrest := hgeom.summable.tsum_le_tsum hpoint htail.summable
  rw [hgeom.tsum_eq,htail.tsum_eq] at hrest
  norm_num only [show ((1:ℝ)-3/4)⁻¹=4 by norm_num] at hrest
  have hsum' : 1≤(∑ n∈range K, v n)+(∑ n∈range K,t^n)*p := hpre
  have hG := geom_sum_mul t K
  have hgem : p/(t-1)*t^K=p/(t-1)+(∑ n∈range K,t^n)*p := by
    field_simp [(sub_pos.mpr ht).ne']
    linear_combination p * -hG
  rw [hgem]
  linarith only [hrest,hsum',hcut]

end FareyGoldbach
