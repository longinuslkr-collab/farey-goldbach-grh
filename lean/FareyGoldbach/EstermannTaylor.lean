import FareyGoldbach.EstermannCutoff
import FareyGoldbach.EstermannCoefficients
import FareyGoldbach.EstermannSeriesTail

/-! # Estermann's Taylor lower bound near one -/

open Filter
open scoped Topology

namespace FareyGoldbach

/-- A circle bound for the regular part and positivity of the full series
give the Estermann lower bound. The constant is independent of the conductor,
residue, point of evaluation, and individual Dirichlet series. -/
theorem estermann_four_factor_lower (A : ℝ) (hA : 0<A) :
    ∃ C : ℝ, 0<C ∧ ∀ {Q : ℕ} {res β : ℝ} {F G : ℂ→ℂ},
      1≤Q → 0≤res → 7/8≤β → β<1 →
      DiffContOnCl ℂ G (Metric.ball 2 (3/2:ℝ)) →
      (∀ s∈Metric.sphere (2:ℂ) (3/2:ℝ), ‖G s‖≤A*(Q:ℝ)^10) →
      (F =ᶠ[𝓝 (2:ℂ)] (fun s => G s+(res:ℂ)/(s-1))) →
      F β=G β+(res:ℂ)/((β:ℂ)-1) → 1≤(F 2).re → (∀ n,0≤(estermannCoeff F n).re) →
      1/2-res/(1-β)*(2*(Q:ℝ))^(C*(1-β)) ≤ (F β).re := by
  obtain ⟨C,hC,hcutoff⟩ := estermann_log_cutoff A hA
  refine ⟨C,hC,?_⟩
  intro Q res β F G hQ hres hβ hβ' hG hbound hreg hpoint hF₀ hF
  let t := 2-β
  let B := A*(Q:ℝ)^10
  have hd : 0<1-β := sub_pos.mpr hβ'
  have ht : 1<t := by dsimp [t]; linarith
  have ht₀ := zero_lt_one.trans ht
  have ht₁ : t-1=1-β := by dsimp [t]; ring
  have ht' : t=1+(1-β) := by dsimp [t]; ring
  have hratio : t/(3/2)≤3/4 := by dsimp [t]; linarith
  obtain ⟨K,hK,hcut,hpow⟩ := hcutoff hQ
  have hcoeff (n : ℕ) : (estermannCoeff F n).re=(estermannCoeff G n).re+res := by
    rw [estermann_coeff_add_pole hG hreg,Complex.add_re,Complex.ofReal_re]
  have hF₀' : 1≤(estermannCoeff G 0).re+res :=
    (show 1≤(estermannCoeff F 0).re by simpa only [estermannCoeff_zero] using hF₀).trans_eq (hcoeff 0)
  have hFn (n : ℕ) : 0≤(estermannCoeff G n).re+res := (hF n).trans_eq (hcoeff n)
  have hmaj (n : ℕ) : -(B*(3/4:ℝ)^n)≤t^n*(estermannCoeff G n).re := by
    have hm := estermann_coeff_norm_bound hG hbound n
    have hp := (abs_le.mp (Complex.abs_re_le_norm (estermannCoeff G n))).1
    have hpow' := pow_le_pow_left₀ (div_nonneg ht₀.le (by norm_num)) hratio n
    have hge : t^n*(B/(3/2:ℝ)^n) ≤ B*(3/4:ℝ)^n := by
      calc _ = B*(t/(3/2))^n := by rw [div_pow t (3/2:ℝ) n]; ring
           _ ≤ _ := mul_le_mul_of_nonneg_left hpow' (by dsimp [B]; positivity)
    have := mul_le_mul_of_nonneg_left ((neg_le_neg hm).trans hp) (pow_nonneg ht₀.le n)
    linarith only [this,hge]
  have hreal := estermann_real_tail_lower ht hK (fun n => (estermannCoeff G n).re) hF₀' hFn
    (estermann_hasSum_real hβ hβ' hG) (fun n => by simpa only [neg_mul] using hmaj n) hcut
  rw [ht₁] at hreal
  have hFβ : (F β).re=(G β).re-res/(1-β) := by
    rw [hpoint,Complex.add_re,←Complex.ofReal_one,←Complex.ofReal_sub,←Complex.ofReal_div,
      Complex.ofReal_re,show β-1=-(1-β) by ring,div_neg]
    ring
  rw [hFβ]
  apply le_trans _ hreal
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left (ht' ▸ hpow (1-β) hd.le)
    (div_nonneg hres hd.le)) _

open scoped ComplexOrder in
theorem estermann_lseries_lower (A : ℝ) (hA : 0<A) :
    ∃ C : ℝ, 0<C ∧ ∀ {Q : ℕ} {res β : ℝ} {F G : ℂ→ℂ} {a : ℕ→ℂ},
      1≤Q → 0≤res → 7/8≤β → β<1 →
      DiffContOnCl ℂ G (Metric.ball 2 (3/2:ℝ)) →
      (∀ s∈Metric.sphere (2:ℂ) (3/2:ℝ), ‖G s‖≤A*(Q:ℝ)^10) →
      (F =ᶠ[𝓝 (2:ℂ)] (fun s => G s+(res:ℂ)/(s-1))) →
      F β=G β+(res:ℂ)/((β:ℂ)-1) →
      (∀ n,0≤a n) → a 1=1 → (∀ s : ℂ,1<s.re → LSeriesSummable a s) →
      (F =ᶠ[𝓝 (2:ℂ)] LSeries a) →
      1/2-res/(1-β)*(2*(Q:ℝ))^(C*(1-β)) ≤ (F β).re := by
  obtain ⟨C,hC,H⟩ := estermann_four_factor_lower A hA
  refine ⟨C,hC,?_⟩
  intro Q res β F G a hQ hres hβ hβ' hG hB hreg hpt ha ha1 hsum hLS
  obtain ⟨hF₂,hF⟩ := estermann_lseries_coeff_nonneg ha ha1 hsum hLS
  exact H hQ hres hβ hβ' hG hB hreg hpt hF₂ hF

/-- At a nonpositive real value the preceding estimate forces a lower bound
for the residue. In particular one may evaluate at a zero of one factor. -/
theorem estermann_residue_lower_of_nonpos {Q : ℕ} (hQ : 1≤Q) {res β C y : ℝ}
    (hβ : β<1) (hy : y≤0)
    (h : 1/2-res/(1-β)*(2*(Q:ℝ))^(C*(1-β))≤y) :
    (1-β)/2*(2*(Q:ℝ))^(-(C*(1-β)))≤res := by
  have hq : (0:ℝ)<Q := Nat.cast_pos.mpr hQ
  have hd := sub_pos.mpr hβ
  have hp := Real.rpow_pos_of_pos (by positivity : (0:ℝ)<2*(Q:ℝ)) (C*(1-β))
  rw [Real.rpow_neg (by positivity),←div_eq_mul_inv,div_le_iff₀ hp]
  have h' : (1/2:ℝ)≤(res*(2*(Q:ℝ))^(C*(1-β)))/(1-β) := by
    rw [div_mul_eq_mul_div] at h
    linarith only [h,hy]
  have h'' := (le_div_iff₀ hd).mp h'
  linarith only [h'']

end FareyGoldbach
