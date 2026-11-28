import FareyGoldbach.TwinChenBoxErrors
import FareyGoldbach.PrimeNumberTheoremUnconditional

/-! # Unconditional shifted product distributions at modulus one -/

open Filter Finset
open scoped Classical

namespace FareyGoldbach

theorem twinChen_carrier_error_unconditional {θ ε : ℝ}
    (hθ : 11/24<θ) (hhalf : θ<1/2) (hε : 0<ε)
    {carrier : ℕ→ℕ→ℕ→Finset ℕ} (hboxes : TwinChenCarrierHasBoxes carrier) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ,
      let P := carrier N 1 b
      chenReducedError 2 (chenPowerLevel θ N) (chenAPError P P.card)≤ε*chenAPLogScale N 1 := by
  obtain ⟨C,hC,hsmallEvt⟩ :=
    chen_small_conductor_interval_bound smallConductorPrimeTwists_unconditional
  let β := max (15/16:ℝ) (θ+1/2)
  have hβ : β<1 := max_lt (by norm_num) (by linarith only [hhalf])
  have hBudget := chenSwitching_budget_small hβ
    (show (0:ℝ)≤4+6*(2*C+200000) by positivity) hε
  filter_upwards [hBudget,hsmallEvt,hboxes,
    eventually_ge_atTop (1:ℕ)] with N hBudget hsmall hboxes hN b
  obtain ⟨S,hcut,hCarrier⟩ := hboxes
  let L := chenSwitchLog N
  let y := S.cutoff
  let P := carrier N 1 b
  let D := chenPowerLevel θ N
  let R := chenAPConductorCut N 1
  let H := (N:ℝ)^β
  let B := C*((N:ℝ)/L^30+(N:ℝ)^(3/4:ℝ)*L)
  let J := (2*C+200000)*((N:ℝ)/L^7+H*L^16)
  have hn : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
  have hp : (0:ℝ)<N := zero_lt_one.trans_le hn
  have hL : 1≤L := one_le_chenSwitchLog hN
  have hH : 0≤H := Real.rpow_nonneg hp.le _
  have hB : 0≤B := by dsimp only [B]; positivity
  have hJ : 0≤J := by dsimp only [J]; positivity
  have hD : D≤N := chenPowerLevel_le_self (by linarith only [hhalf]) hN
  have hy : 0<y := Nat.cast_pos.mp
    ((by positivity : (0:ℝ)<(N:ℝ)^(1/16:ℝ)+1).trans_le hcut)
  obtain ⟨hR,hRlo,hRhi⟩ := chenAPConductorCut_bounds hN (r:=1) (by decide)
  simp only [Nat.cast_one,one_mul] at hRlo hRhi
  have hM : (N:ℝ)^(3/4:ℝ)≤H := Real.rpow_le_rpow_of_exponent_le hn
    ((by norm_num : (3/4:ℝ)≤15/16).trans (le_max_left ..))
  have hW : (N:ℝ)^(7/8:ℝ)≤H := Real.rpow_le_rpow_of_exponent_le hn
    ((by norm_num : (7/8:ℝ)≤15/16).trans (le_max_left ..))
  have hDpow : (D:ℝ)*Real.sqrt N≤H := by
    rw [Real.sqrt_eq_rpow]
    calc _ ≤ (N:ℝ)^θ*(N:ℝ)^(1/2:ℝ) := mul_le_mul_of_nonneg_right
          (Nat.floor_le (zero_le_one.trans (Real.one_le_rpow hn (by linarith only [hθ]))))
          (by positivity)
      _ = (N:ℝ)^(θ+1/2) := by rw [Real.rpow_add hp]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn (le_max_right ..)
  have hyPow : (N:ℝ)/(y:ℝ)≤H := by
    calc _ ≤ (N:ℝ)/(N:ℝ)^(1/16:ℝ) := div_le_div_of_nonneg_left hp.le
          (by positivity) (by change (N:ℝ)^(1/16:ℝ)≤(S.cutoff:ℝ); linarith only [hcut])
      _ = (N:ℝ)^(15/16:ℝ) := by
          rw [show (15/16:ℝ)=1-1/16 by norm_num,Real.rpow_sub hp,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn (le_max_left ..)
  have boxSmall {i k q : ℕ} (hk : k∈Finset.Ico 1 D) (hq : 2≤q) (hqR : q≤R)
      (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) : ‖S.sum i k χ‖≤B := by
    let _ : NeZero q := ⟨by omega⟩
    rcases S.boxShape i with ⟨_,_,hMW,hMbox,_⟩ | hempty
    · exact hsmall (chenSwitchBoxM i) (chenSwitchBoxW N i) k q χ
        (S.row i k) S.lo (chenSwitchBoxHi N i)
        hχ hq (by simpa [R,chenAPConductorCut] using hqR) (Finset.mem_Ico.mp hk).1
        ((Finset.mem_Ico.mp hk).2.le.trans hD) hMW hMbox
        (fun m _ => S.rowBound i k m) (fun m _ => S.loBound i k m) (fun m _ => chenSwitchBoxHi_le N i m)
    · have he : S.sum i k χ=0 := hempty q k χ
      rw [he,norm_zero]
      exact hB
  have boxBudget : chenAPBoxBudget N 1 D R B≤J := by
    unfold chenAPBoxBudget
    simp only [Nat.cast_one,mul_one,Real.sqrt_one,one_mul]
    apply le_trans _ (chenSwitchBox_budget_absorb hL hp.le hH
      (Nat.cast_pos.mpr hR) hC.le hRlo hRhi)
    exact add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hM (zero_le_one.trans hL))) hC.le)
      (Nat.cast_nonneg _)) (mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hW) hDpow)
        (by positivity))
  have hr := twinChen_error_le_of_boxes (r:=1) (b:=b) S (chenAPError P P.card) hN
    (by decide) hy hD (by simp) (hCarrier 1 b)
    (J:=fun _ => J) (fun _ _ => hJ) (by
      intro a ha k hk i _
      simp only [Nat.divisors_one,Finset.mem_singleton] at ha
      subst a
      have hh := twinChenBox_conductors_le (a:=1) (i:=i) (k:=k) S hN
        (by decide) hD hR hB (by
          intro q hq _ hqR χ hχ
          exact boxSmall (q:=1*q) (i:=i) hk (by simpa using hq) (by simpa using hqR) χ hχ)
      simpa only [Nat.div_one,one_mul] using hh.trans boxBudget)
  simp only [Nat.totient_one,Nat.cast_one,one_mul,Nat.mul_one,Nat.divisors_one,Finset.sum_singleton] at hr
  have hh := hr.trans ((add_le_add (mul_le_mul_of_nonneg_left hyPow (by positivity)) le_rfl).trans
    ((chenSwitchTotal_budget_absorb hL hp.le hH hC.le).trans hBudget))
  simpa only [chenAPLogScale,chenLogScale,Nat.totient_one,Nat.cast_one,one_mul] using hh

end FareyGoldbach
