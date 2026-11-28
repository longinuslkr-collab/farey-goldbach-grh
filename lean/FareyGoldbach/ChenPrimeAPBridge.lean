import FareyGoldbach.BVInducedPrimes
import FareyGoldbach.BVPrimeAbel
import FareyGoldbach.ChenSwitchingAsymptotics

/-! # Reduced progression errors from the primitive Mangoldt estimate -/

open Filter Finset
open scoped Classical Topology

namespace FareyGoldbach

private theorem bvPrime_budget {D L l s n ε : ℝ}
    (hD : 0≤D) (hL : 1≤L) (hl : 0<l) (hlL : l≤L) (hLl : L≤3*l)
    (hs : 1≤s) (hn : 0≤n) (hε : 0≤ε) :
    D*(2*L)+2*L^2*(2/l*(ε/72*n/l^3)+D*(s+2*s*l)+D*(2*L)) ≤
    ε/2*(n/l^2) + 12*(D*s)*L^3 := by
  have hL₀ := zero_le_one.trans hL
  have hs₀ := zero_le_one.trans hs
  have hsig : 2*L^2*(2/l*(ε/72*n/l^3)) ≤ ε/2*(n/l^2) := by
    calc _ = L^2*(ε/18*n/l^4) := by ring
      _ ≤ (3*l)^2*(ε/18*n/l^4) := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hL₀ hLl 2) (by positivity)
      _ = _ := by field_simp [hl.ne']; ring
  have h₁ : s+2*s*l≤3*s*L := by
    have hsL := mul_le_mul_of_nonneg_left hL hs₀
    have hll := mul_le_mul_of_nonneg_left hlL hs₀
    linarith only [hsL,hll]
  have h₂ : 2*L≤2*s*L := by
    have h := mul_le_mul_of_nonneg_right hs hL₀
    linarith only [h]
  have hsmall : D*(2*L)≤2*(D*s)*L^3 := by
    calc _ ≤ D*(2*s*L) := mul_le_mul_of_nonneg_left h₂ hD
      _ = 2*(D*s)*L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa using (pow_le_pow_right₀ hL (by norm_num : 1≤3))) (by positivity)
  have hlarge := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left h₁ hD) (mul_le_mul_of_nonneg_left h₂ hD)) (by positivity : 0≤2*L^2)
  linarith only [hsig,hsmall,hlarge]

theorem bv_prime_classes_of_primitive_mangoldt (hBV : ChenPrimitiveMangoldtBV)
    {θ : ℝ} (hθ : 11/24<θ) (hh : θ<1/2) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (a : ℕ→ℕ), (∀ d, 0<d → d.Coprime K → (a d).Coprime d) →
      chenReducedError K (chenPowerLevel θ N) (fun d => ((N.primesLE.filter fun p => p%d=a d%d).card:ℝ) -
        (N.primeCounting:ℝ)/(d.totient:ℝ)) ≤
      ε*chenLogScale N := by
  have hβ : θ+1/2<1 := by linarith only [hh]
  have hg := chenSwitching_budget_small hβ (C:=12) (by norm_num) (by positivity : 0<ε/2)
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 2
  filter_upwards [hBV θ hθ hh (ε/72) (by positivity),hg,hlog,eventually_ge_atTop (3:ℕ)] with
    N hBV' hsmall hlog hN K a ha
  change 2≤Real.log (N:ℝ) at hlog
  let D := chenPowerLevel θ N
  let L := chenSwitchLog N
  let l := Real.log (N:ℝ)
  let s := Real.sqrt (N:ℝ)
  have hn : 1≤N := by omega
  have hnr : (0:ℝ)<N := Nat.cast_pos.mpr hn
  have hDp : D≤N := chenPowerLevel_le_self (by linarith only [hh]) hn
  have hs : 1≤s := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hn)
  have hl : 0<l := by dsimp [l]; linarith only [hlog]
  have hL : 1≤L := one_le_chenSwitchLog hn
  have hlt : l≤L := log_le_chenSwitchLog hn
  have hD : 0≤(D:ℝ) := Nat.cast_nonneg _
  have hB := bvPrime_average_le hlog hn hBV'
  have hb := bvReducedPrimeClasses_of_average K a ha hn hDp (by positivity) hB
  have hsum := bvPrime_budget hD hL hl hlt (chenSwitchLog_le_three_log hN) hs hnr.le hε.le
  have hprod : (D:ℝ)*s≤(N:ℝ)^(θ+1/2) := by
    dsimp only [D,s]
    rw [Real.sqrt_eq_rpow,Real.rpow_add hnr]
    exact mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity)
  have herr : 12*((D:ℝ)*s)*L^3≤ ε/2*chenLogScale N := by
    apply le_trans _ hsmall
    calc _ ≤ 12*((N:ℝ)^(θ+1/2)*L^20) := by
            rw [mul_assoc]
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul hprod (pow_le_pow_right₀ hL (by norm_num)) (by positivity) (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact le_add_of_nonneg_left (by positivity)
  calc _ ≤ _ := hb
    _ ≤ ε/2*chenLogScale N + 12*((D:ℝ)*s)*L^3 := hsum
    _ ≤ ε/2*chenLogScale N + ε/2*chenLogScale N := add_le_add_right herr _
    _ = _ := by ring

theorem chen_prime_reduced_error_of_primitive_mangoldt (hBV : ChenPrimitiveMangoldtBV)
    {θ : ℝ} (hθ : 11/24<θ) (hh : θ<1/2) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, chenReducedError N (chenPowerLevel θ N) (chenPrimeAPError N) ≤
      ε*chenLogScale N := by
  filter_upwards [bv_prime_classes_of_primitive_mangoldt hBV hθ hh ε hε] with N h
  simpa only [chenReducedError,chenPrimeAPError,chenAPError,chenDivisible_card_eq_progression,
    chenA_card_eq_primeCounting] using h N (fun _ => N) (fun _ _ hd => hd.symm)

end FareyGoldbach
