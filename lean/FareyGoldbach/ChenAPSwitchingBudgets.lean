import FareyGoldbach.ChenSwitchingBudgets
import FareyGoldbach.ChenAPScale

/-! # Uniform summation budgets for the AP conductor bounds -/

open Finset
open scoped Classical

namespace FareyGoldbach

noncomputable def chenAPConductorCut (N r : ℕ) : ℕ :=
  ⌈(r:ℝ)*(chenSwitchLog N)^12⌉₊

noncomputable def chenAPBoxBudget (N a D R : ℕ) (B : ℝ) : ℝ :=
  (R:ℝ)*a*B+100000*(chenSwitchLog N)^2*((N:ℝ)/R+
    Real.sqrt (a:ℝ)*(N:ℝ)^(7/8:ℝ)+(a:ℝ)*(D:ℝ)*Real.sqrt N)

theorem chenAPConductorCut_bounds {N r : ℕ} (hN : 1≤N) (hr : 0<r) :
    1≤chenAPConductorCut N r ∧ (r:ℝ)*(chenSwitchLog N)^12≤chenAPConductorCut N r ∧
      (chenAPConductorCut N r:ℝ)≤2*((r:ℝ)*(chenSwitchLog N)^12) := by
  have hs : (1:ℝ)≤(r:ℝ)*(chenSwitchLog N)^12 :=
    one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr hr) (one_le_pow₀ (one_le_chenSwitchLog hN))
  have hlo := Nat.le_ceil ((r:ℝ)*(chenSwitchLog N)^12)
  have hhi := Nat.ceil_lt_add_one (show 0≤(r:ℝ)*(chenSwitchLog N)^12 by positivity)
  exact ⟨by exact_mod_cast hs.trans hlo,hlo,by unfold chenAPConductorCut; linarith only [hs,hhi]⟩

private theorem sum_divisors_real_le {r N : ℕ} (hr : 0<r) (hrN : r≤N) :
    (∑ a∈r.divisors,(a:ℝ))≤(r:ℝ)*chenSwitchLog N := by
  have hdiv {a : ℕ} (ha : a∈r.divisors) : a∣r := (Nat.mem_divisors.mp ha).1
  have hm {a : ℕ} (ha : a∈r.divisors) : r/a∈r.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (hdiv ha),hr.ne'⟩
  have he : (∑ a∈r.divisors,(a:ℝ)) = ∑ a∈r.divisors,((r/a:ℕ):ℝ) := by
    refine Finset.sum_bij' (fun a _ => r/a) (fun a _ => r/a)
      (fun a ha => hm ha) (fun a ha => hm ha) ?_ ?_ ?_
    · exact fun a ha => Nat.div_div_self (hdiv ha) hr.ne'
    · exact fun a ha => Nat.div_div_self (hdiv ha) hr.ne'
    · intro a ha
      exact_mod_cast (Nat.div_div_self (hdiv ha) hr.ne').symm
  have hsub : r.divisors⊆Finset.Icc 1 r := by
    intro a ha
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos (hdiv ha) hr,Nat.le_of_dvd hr (hdiv ha)⟩
  have ht : (∑ a∈r.divisors,1/(a:ℝ))≤chenSwitchLog N := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by positivity)).trans ?_
    have hl := Real.log_le_log (Nat.cast_pos.mpr hr)
      (show (r:ℝ)≤2*(N:ℝ) by exact_mod_cast (show r≤2*N by omega))
    exact (harmonic_le_one_add_log hr).trans (by unfold chenSwitchLog; linarith only [hl])
  rw [he]
  calc
    (∑ a∈r.divisors,((r/a:ℕ):ℝ)) = (r:ℝ)*∑ a∈r.divisors,1/(a:ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Nat.cast_div (hdiv ha) (by exact_mod_cast (Nat.pos_of_dvd_of_pos (hdiv ha) hr).ne')]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)

private theorem card_divisors_le {r : ℕ} (hr : 0<r) : r.divisors.card≤r := by
  have hs : r.divisors⊆Finset.Icc 1 r := by
    intro a ha
    have hd := (Nat.mem_divisors.mp ha).1
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd hr,Nat.le_of_dvd hr hd⟩
  simpa using Finset.card_le_card hs

private theorem pow_div_weaken {n L : ℝ} (hn : 0≤n) (hL : 1≤L) :
    L^2*(n/L^12)≤n/L^7 := by
  have hp : 0<L := zero_lt_one.trans_le hL
  rw [← mul_div_assoc,div_le_div_iff₀ (pow_pos hp 12) (pow_pos hp 7)]
  calc
    L^2*n*L^7=n*L^9 := by ring
    _≤n*L^12 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by decide : 9≤12)) hn

/-- The shell budgets sum with the correct dependence on the divisor
sum of r. The first term uses the full r factor in the conductor cutoff. -/
theorem chen_ap_sum_box_budget {N r D : ℕ} {C H : ℝ}
    (hN : 1≤N) (hr : 0<r) (hrN : r≤N) (hC : 0≤C) (hH : 0≤H)
    (hsmall : (r:ℝ)^2*(N:ℝ)^(7/8:ℝ)≤H)
    (hlarge : (r:ℝ)*(D:ℝ)*Real.sqrt N≤H) :
    (∑ a∈r.divisors,chenAPBoxBudget N a D (chenAPConductorCut N r)
      (C*(N:ℝ)^(7/8:ℝ)*(chenSwitchLog N)^2))≤
        (2*C+200000)*((N:ℝ)/(chenSwitchLog N)^7+H*(chenSwitchLog N)^16) := by
  let L := chenSwitchLog N
  let R := chenAPConductorCut N r
  let U := (N:ℝ)^(7/8:ℝ)
  let B := C*U*L^2
  let T := r.divisors
  have hL := one_le_chenSwitchLog hN
  have hL₀ : 0≤L := zero_le_one.trans hL
  have hn := Nat.cast_nonneg (α:=ℝ) N
  have hB : 0≤B := by dsimp [B,U]; positivity
  have hU : 0≤U := by dsimp [U]; positivity
  obtain ⟨hR,hRlo,hRhi⟩ := chenAPConductorCut_bounds hN hr
  have hRp : (0:ℝ)<R := Nat.cast_pos.mpr hR
  have hS : (∑ a∈T,(a:ℝ))≤(r:ℝ)*L := sum_divisors_real_le hr hrN
  have hT : (T.card:ℝ)≤r := Nat.cast_le.mpr (card_divisors_le hr)
  have hSqrt : (∑ a∈T,Real.sqrt (a:ℝ))≤(r:ℝ)*L := by
    refine (Finset.sum_le_sum fun a ha => ?_).trans hS
    have h : (1:ℝ)≤a := Nat.one_le_cast.mpr
      (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 hr)
    apply (Real.sqrt_le_iff).mpr
    exact ⟨(zero_le_one.trans h), by nlinarith only [mul_nonneg (zero_le_one.trans h) (sub_nonneg.mpr h)]⟩
  have hprod : (r:ℝ)*U≤H := by
    refine (mul_le_mul_of_nonneg_right ?_ hU).trans hsmall
    have h : (1:ℝ)≤r := Nat.one_le_cast.mpr hr
    nlinarith only [mul_nonneg (zero_le_one.trans h) (sub_nonneg.mpr h)]
  have hsmallSum : (R:ℝ)*B*(∑ a∈T,(a:ℝ))≤2*C*(H*L^16) := by
    calc
      _ ≤ (2*((r:ℝ)*L^12))*B*((r:ℝ)*L) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hRhi hB) hS
          (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
      _ = 2*C*(((r:ℝ)^2*U)*L^15) := by dsimp only [B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul hsmall (pow_le_pow_right₀ hL (by decide : 15≤16))
          (by positivity) hH) (by positivity)
  have hfirst : (T.card:ℝ)*((N:ℝ)/R)≤(N:ℝ)/L^12 := by
    refine (mul_le_mul_of_nonneg_right hT (div_nonneg hn hRp.le)).trans ?_
    rw [← mul_div_assoc,div_le_div_iff₀ hRp (by positivity : 0<L^12)]
    simpa only [mul_comm,mul_left_comm,mul_assoc] using
      mul_le_mul_of_nonneg_left hRlo hn
  have hmiddle : (∑ a∈T,Real.sqrt (a:ℝ))*U≤H*L := by
    calc
      _ ≤ ((r:ℝ)*L)*U := mul_le_mul_of_nonneg_right hSqrt hU
      _ = ((r:ℝ)*U)*L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod hL₀
  have hlast : (∑ a∈T,(a:ℝ))*((D:ℝ)*Real.sqrt N)≤H*L := by
    calc
      _ ≤ ((r:ℝ)*L)*((D:ℝ)*Real.sqrt N) := mul_le_mul_of_nonneg_right hS (by positivity)
      _ = ((r:ℝ)*(D:ℝ)*Real.sqrt N)*L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hlarge hL₀
  have hlargeSum : 100000*L^2*((T.card:ℝ)*((N:ℝ)/R)+(∑ a∈T,Real.sqrt (a:ℝ))*U+
      (∑ a∈T,(a:ℝ))*((D:ℝ)*Real.sqrt N))≤200000*((N:ℝ)/L^7+H*L^16) := by
    have hx := pow_div_weaken hn hL
    have hy : L^2*(H*L)≤H*L^16 := by
      calc L^2*(H*L)=H*L^3 := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by decide : 3≤16)) hH
    have hnon : 0≤(N:ℝ)/L^7 := by positivity
    calc
      _ ≤ 100000*L^2*((N:ℝ)/L^12+H*L+H*L) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add hfirst hmiddle) hlast) (by positivity)
      _ ≤ _ := by linarith only [hx,hy,hnon]
  change (∑ a∈T,chenAPBoxBudget N a D R B)≤_
  calc
    _ = (R:ℝ)*B*(∑ a∈T,(a:ℝ))+
        100000*L^2*((T.card:ℝ)*((N:ℝ)/R)+(∑ a∈T,Real.sqrt (a:ℝ))*U+
          (∑ a∈T,(a:ℝ))*((D:ℝ)*Real.sqrt N)) := by
      simp only [chenAPBoxBudget,Finset.mul_sum,Finset.sum_mul,Finset.sum_add_distrib,L,U]
      congr 1
      · refine Finset.sum_congr rfl fun a _ => ?_
        ring
      · rw [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
        congr 2
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
    _ ≤ _ := by
      have hnL : 0≤(N:ℝ)/L^7 := by positivity
      nlinarith only [hsmallSum,hlargeSum,mul_nonneg hC hnL]

end FareyGoldbach
