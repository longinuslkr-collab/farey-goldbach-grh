import FareyGoldbach.ChenAPPrimeReduction
import FareyGoldbach.PrimeNumberTheoremUnconditional

/-! # Prime distribution in the AP Chen sieve under Dirichlet GRH -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

private theorem ap_level_product {δ θ : ℝ} {N r : ℕ} (hN : 0<N) (hr : (r:ℝ)≤(N:ℝ)^δ) :
    r*chenPowerLevel θ N≤chenPowerLevel (δ+θ) N := by
  have hp : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  apply Nat.le_floor
  rw [Nat.cast_mul,Real.rpow_add hp]
  exact mul_le_mul hr (Nat.floor_le (Real.rpow_nonneg hp.le _)) (Nat.cast_nonneg _)
    (Real.rpow_nonneg hp.le _)

theorem chenAP_prime_mass_of_count {N r count : ℕ} {E ε : ℝ} (hr : 0<r) (hl : 1≤Real.log (N:ℝ))
    (hN : 0<N) (hε : 0<ε)
    (hcard : |(count:ℝ)-(N.primeCounting:ℝ)/r.totient|≤E)
    (he : E≤(ε/2)*chenAPLogScale N r)
    (hpi : |(N.primeCounting:ℝ)/((N:ℝ)/Real.log N)-1|≤ε/2) :
    |(count:ℝ)/chenAPMassScale N r-1|≤ε := by
  let P := (N.primeCounting:ℝ)/r.totient
  let M := chenAPMassScale N r
  have hφ : 0<(r.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hl₀ := zero_lt_one.trans_le hl
  have hm : 0<M := div_pos hn (mul_pos hφ hl₀)
  have hscale : chenAPLogScale N r ≤ M := by
    apply div_le_div_of_nonneg_left hn.le (mul_pos hφ hl₀)
    exact mul_le_mul_of_nonneg_left (by nlinarith only [hl,sq_nonneg (Real.log (N:ℝ)-1)]) hφ.le
  have hle : |(count:ℝ)/M-P/M|≤ε/2 := by
    rw [←sub_div,abs_div,abs_of_pos hm]
    exact (div_le_iff₀ hm).mpr (hcard.trans (he.trans (mul_le_mul_of_nonneg_left hscale (by positivity))))
  have heq : P/M=(N.primeCounting:ℝ)/((N:ℝ)/Real.log N) := by
    dsimp only [P,M,chenAPMassScale]
    field_simp
  exact (abs_sub_le _ (P/M) 1).trans (by rw [heq] at hle ⊢; linarith only [hpi,hle])

/-- Uniform single-class error and its full Chen-level budget. The additive allowance of
three covers replacing the upper endpoint N by N−3. -/
theorem chenAP_prime_class_budget {δ θ : ℝ} (hθ₀ : 0≤θ) (hsum : δ+θ<1/2)
    (hGRH : DirichletGRH) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ r : ℕ, 0<r → (r:ℝ)≤(N:ℝ)^δ → ∃ U : ℝ, 0≤U ∧
      (∀ e a : ℕ, 0<e → e≤r*chenPowerLevel θ N → a.Coprime e →
        |((N.primesLE.filter fun p => p%e=a%e).card:ℝ)-(N.primeCounting:ℝ)/e.totient|≤U) ∧
      2*(U+3)≤ε*chenAPLogScale N r ∧
      (chenPowerLevel θ N:ℝ)*(2*(U+3))*(1+Real.log (N:ℝ))≤ε*chenAPLogScale N r := by
  obtain ⟨C,hC,hAP⟩ := primeAP_count_of_dirichletGRH hGRH
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [chenPowerLevel_allErrors_small hsum (show 0≤2*C+6 by linarith only [hC]) hε,
    hlog,eventually_ge_atTop (2:ℕ)] with N hbudget hL hN r hr hrδ
  change 1≤Real.log (N:ℝ) at hL
  have hn : 0<N := by omega
  have hNr : (2:ℝ)≤N := Nat.cast_le.mpr hN
  have hp : 0<(N:ℝ) := Nat.cast_pos.mpr hn
  let D := chenPowerLevel θ N
  let D' := chenPowerLevel (δ+θ) N
  let F := Real.sqrt (N:ℝ)*Real.log (2*(N:ℝ))^2
  let E := (2*C+6)*F
  have hD : 1≤D := Nat.le_floor (by
    simpa only [Nat.cast_one] using Real.one_le_rpow (by linarith only [hNr] : (1:ℝ)≤N) hθ₀)
  have hRD : r*D≤D' := ap_level_product hn hrδ
  have hD'N : D'≤N := chenPowerLevel_le_self (by linarith only [hsum]) hn
  have hF : 1≤F := by
    have hlog₂ : Real.log (N:ℝ)≤Real.log (2*(N:ℝ)) :=
      Real.log_le_log hp (by linarith only [hp])
    apply one_le_mul_of_one_le_of_one_le
    · rw [←Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith only [hNr])
    · exact one_le_pow₀ (hL.trans hlog₂)
  have hF₀ := zero_le_one.trans hF
  have hE : 1≤E := one_le_mul_of_one_le_of_one_le (by linarith only [hC]) hF
  have hE₀ := zero_le_one.trans hE
  have hphysical (k : ℕ) (hk : 0<k) (hkD : k≤N) (u : ℕ) (hu : u.Coprime k) :
      |((N.primesLE.filter (fun p => p%k=u%k)).card:ℝ)-(N.primeCounting:ℝ)/k.totient|≤C*F := by
    simpa only [F,mul_assoc] using hAP hN hk hkD hu
  have hφ : 0<(r.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hφD : (r.totient:ℝ)*(D:ℝ)≤(D':ℝ) :=
    by exact_mod_cast (Nat.mul_le_mul_right D (Nat.totient_le r)).trans hRD
  have hfac : 1≤1+Real.log (N:ℝ) := by linarith only [hL]
  have htotal : (D:ℝ)*E*(1+Real.log N)≤ε*chenAPLogScale N r := by
    have hb : (D':ℝ)*E*(1+Real.log N)≤ε*chenLogScale N := by
      simpa only [D',E,F,mul_assoc] using hbudget
    have hscale : ε*chenAPLogScale N r=(ε*chenLogScale N)/(r.totient:ℝ) := by
      unfold chenAPLogScale chenLogScale
      ring
    rw [hscale]
    apply (le_div_iff₀ hφ).mpr
    calc _ = ((r.totient:ℝ)*D)*E*(1+Real.log N) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hφD hE₀) (zero_le_one.trans hfac)).trans hb
  have hplain := (le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg D) hE₀) hfac).trans htotal
  have hone : E≤ε*chenAPLogScale N r :=
    (le_mul_of_one_le_left hE₀ (Nat.one_le_cast.mpr hD)).trans hplain
  have hex : 2*(C*F+3)≤E := by dsimp only [E]; nlinarith only [hF]
  refine ⟨C*F,mul_nonneg hC.le hF₀,fun e a he heD ha =>
    hphysical e he (heD.trans (hRD.trans hD'N)) a ha,hex.trans hone,?_⟩
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hex (Nat.cast_nonneg D))
    (zero_le_one.trans hfac)).trans htotal

theorem chenAPPrimeDistribution_of_dirichletGRH {δ θ : ℝ} (hδ : 0<δ)
    (hθ : 11/24<θ) (hsum : δ+θ<1/2) (hGRH : DirichletGRH) :
    ChenAPPrimeDistributionAt δ θ := by
  intro ε hε
  have hhalf : 0<ε/2 := by positivity
  have hpnt := Metric.tendsto_nhds.mp primeCounting_ratio_unconditional (ε/2) hhalf
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [chenAP_prime_class_budget (by linarith only [hθ] : 0≤θ) hsum hGRH hhalf,
    hpnt,hlog,eventually_ge_atTop (2:ℕ)] with N hb hpi hL hN _ r b₁ b₂ hr hrδ hb₁ hb₂ hadm
  change 1≤Real.log (N:ℝ) at hL
  obtain ⟨U,hU,hclass,hone,hall⟩ := hb r hr hrδ
  let D := chenPowerLevel θ N
  have hD : 1≤D := Nat.le_floor (by
    simpa only [Nat.cast_one] using Real.one_le_rpow (Nat.one_le_cast.mpr (by omega : 1≤N))
      (by linarith only [hθ] : 0≤θ))
  have hpoint (d : ℕ) (hd : 0<d) (hdD : d≤D) (hc : d.Coprime (r*N)) :
      |chenAPPrimeError N r b₁ d|≤2*(U+3) := by
    exact (chenAPPrimeError_le_of_prime_classes hr hd hb₁ hc (fun e a he heD ha =>
      hclass e a he (heD.trans (Nat.mul_le_mul_left r hdD)) ha)).trans (by linarith)
  obtain ⟨hred,hmed⟩ := chenAPPrimeDistribution_finite hN hb₂ hadm (by linarith only [hU]) hpoint
  have hs : 0≤chenAPLogScale N r := by unfold chenAPLogScale; positivity
  have hε' := mul_le_mul_of_nonneg_right (by linarith only [hε] : ε/2≤ε) hs
  have hmain := hclass r b₁ hr (Nat.le_mul_of_pos_right r hD) hb₁
  rw [←chenAPA_card_eq_prime_class] at hmain
  refine ⟨chenAP_prime_mass_of_count hr hL (by omega) hε hmain ((by linarith only [hU] : U≤2*(U+3)).trans hone) ?_,
    hred.trans ((le_mul_of_one_le_right (by positivity)
      (by linarith only [hL] : 1≤1+Real.log (N:ℝ))).trans (hall.trans hε')),
    hmed.trans (hall.trans hε')⟩
  simpa only [Real.dist_eq] using hpi.le

end FareyGoldbach
