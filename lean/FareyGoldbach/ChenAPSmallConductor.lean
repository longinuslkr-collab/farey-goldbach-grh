import FareyGoldbach.ChenSmallConductorInterval
import FareyGoldbach.ChenSwitchingBoxes
import FareyGoldbach.SharpPrimeCount

/-! # Uniform GRH twists in the small-conductor switching boxes -/

open Finset
open scoped Classical

namespace FareyGoldbach

private theorem log_products_le {N Q X : ℕ} (hN : 1≤N) (hQ : 1≤Q)
    (hX : 1≤X) (hQN : Q≤N^2) (hXN : X≤N) :
    Real.log (2*(Q:ℝ)*X)≤3*chenSwitchLog N := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hq : (0:ℝ)<Q := Nat.cast_pos.mpr hQ
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr hX
  have hu : (Q:ℝ)≤(N:ℝ)^2 := by exact_mod_cast hQN
  have hqL := Real.log_le_log hq hu
  rw [Real.log_pow] at hqL
  norm_num at hqL
  have hxL := Real.log_le_log hx (Nat.cast_le.mpr hXN)
  rw [Real.log_mul (by positivity) hx.ne', Real.log_mul (by norm_num) hq.ne']
  unfold chenSwitchLog
  rw [Real.log_mul (by norm_num) hn.ne']
  have ht := Real.log_nonneg (by norm_num : (1:ℝ)≤2)
  linarith only [hqL,hxL,ht]

private theorem ap_box_sqrt {N M W : ℕ} (hN : 0<N)
    (hMW : (M:ℝ)*W≤2*N) (hM : (M:ℝ)≤2*(N:ℝ)^(3/4:ℝ)) :
    (M:ℝ)*Real.sqrt W≤2*(N:ℝ)^(7/8:ℝ) := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have he : ((N:ℝ)^(7/8:ℝ))^2=(N:ℝ)*(N:ℝ)^(3/4:ℝ) := by
    rw [pow_two,←Real.rpow_add hn,show (7/8:ℝ)+7/8=1+3/4 by norm_num,
      Real.rpow_add hn,Real.rpow_one]
  have h := mul_le_mul hMW hM (Nat.cast_nonneg M) (by positivity : 0≤2*(N:ℝ))
  have hs := Real.sq_sqrt (Nat.cast_nonneg W : (0:ℝ)≤W)
  have hsq : ((M:ℝ)*Real.sqrt W)^2≤(2*(N:ℝ)^(7/8:ℝ))^2 := by
    rw [mul_pow,hs,mul_pow,he]
    nlinarith only [h]
  nlinarith only [hsq,show 0≤2*(N:ℝ)^(7/8:ℝ) by positivity,
    show 0≤(M:ℝ)*Real.sqrt W by positivity]

/-- A sharp prime twist in independently moving rows with a bounded first coefficient. -/
theorem chen_ap_interval_twist_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ B : ℝ, 0<B ∧ ∀ {N M W K Q : ℕ} [NeZero Q] (χ : DirichletCharacter ℂ Q)
      (a : ℕ→ℂ) (lo hi : ℕ→ℕ), 1≤N → 1≤W → W≤N →
      (M:ℝ)*W≤2*N → (M:ℝ)≤2*(N:ℝ)^(3/4:ℝ) →
      (∀ m, ‖a m‖≤1) → (∀ m, 1≤lo m) → (∀ m, hi m≤W) →
      1≤K → K≤N^2 → 1<Q → Q≤N^2 → χ≠1 →
      ‖∑ m∈Finset.Icc 1 M, a m*χ (m:ZMod Q)*
        ∑ w∈Finset.Icc (lo m) (hi m), chenSwitchBoxB K w*χ (w:ZMod Q)‖ ≤
          B*(N:ℝ)^(7/8:ℝ)*(chenSwitchLog N)^2 := by
  obtain ⟨C,hC,hGR⟩ := nonprincipal_prime_twist_of_dirichletGRH hGRH
  refine ⟨36*C+24,by positivity,?_⟩
  intro N M W K Q _ χ a lo hi hN hW hWN hMW hM ha hlo hhi hK hKN hQ hQN hχ'
  let L := chenSwitchLog N
  have hL : 1≤L := one_le_chenSwitchLog hN
  have hL₀ : 0≤L := zero_le_one.trans hL
  have hrootW : 1≤Real.sqrt (W:ℝ) := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hW)
  have hLsq : L≤L^2 := by nlinarith only [mul_nonneg hL₀ (sub_nonneg.mpr hL)]
  have hpref (X : ℕ) (hX : X≤W) :
      ‖∑ w∈Finset.Icc 1 X, chenSwitchBoxB K w*χ (w:ZMod Q)‖ ≤
        (9*C+6)*Real.sqrt (W:ℝ)*L^2 := by
    have hlK : Real.log (2*(K:ℝ))≤3*L := by
      simpa using log_products_le hN hK (le_refl 1) hKN hN
    have ht : ‖∑ w∈X.primesLE, χ (w:ZMod Q)‖≤9*C*Real.sqrt (W:ℝ)*L^2 := by
      by_cases hx : 2≤X
      · have hlog := log_products_le hN (by omega : 1≤Q) (by omega : 1≤X) hQN
          (hX.trans hWN)
        have hlog₀ : 0≤Real.log (2*(Q:ℝ)*X) := Real.log_nonneg (by
          have h1 : (1:ℝ)≤Q := by exact_mod_cast (show 1≤Q by omega)
          have h2 : (1:ℝ)≤X := by exact_mod_cast (show 1≤X by omega)
          nlinarith only [h1,h2,mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)])
        refine (hGR X Q χ hχ' hx).trans ?_
        calc
          _ ≤ C*Real.sqrt (W:ℝ)*(3*L)^2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.cast_le.mpr hX)) hC.le)
              (pow_le_pow_left₀ hlog₀ hlog _) (by positivity) (by positivity)
          _ = _ := by ring
      · have hEmpty : X.primesLE=∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro w hw
          obtain ⟨h1,h2⟩ := Nat.mem_primesLE.mp hw
          exact hx (h2.two_le.trans h1)
        rw [hEmpty,Finset.sum_empty,norm_zero]
        positivity
    have h6 : 2*Real.log (2*(K:ℝ))≤6*(Real.sqrt (W:ℝ)*L^2) := by
      have hle : L≤Real.sqrt (W:ℝ)*L^2 := by
        exact hLsq.trans (le_mul_of_one_le_left (by positivity) hrootW)
      linarith only [hlK,hle]
    refine (chen_masked_prime_prefix_le χ X K hK).trans ?_
    calc
      _ ≤ 9*C*Real.sqrt (W:ℝ)*L^2+6*(Real.sqrt (W:ℝ)*L^2) := add_le_add ht h6
      _ = _ := by ring
  have hrow (m : ℕ) :
      ‖∑ w∈Finset.Icc (lo m) (hi m),
          chenSwitchBoxB K w*χ (w:ZMod Q)‖≤(18*C+12)*Real.sqrt (W:ℝ)*L^2 := by
    by_cases hh : lo m≤hi m
    · rw [chen_sum_interval_eq_prefix_sub (hlo m) hh]
      have hhim := hhi m
      have hlom : lo m-1≤W := by omega
      refine (norm_sub_le ..).trans ((add_le_add (hpref _ hhim) (hpref _ hlom)).trans_eq ?_)
      ring
    · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hh),Finset.sum_empty,norm_zero]
      positivity
  have hmixed := ap_box_sqrt hN hMW hM
  change ‖∑ m∈Finset.Icc 1 M, _‖≤_
  calc
    _ ≤ ∑ _m∈Finset.Icc 1 M, (18*C+12)*Real.sqrt (W:ℝ)*L^2 := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [norm_mul, norm_mul]
      have hA : ‖a m‖*‖χ (m:ZMod Q)‖≤1 :=
        (mul_le_mul (ha m) (χ.norm_le_one _)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      exact mul_le_of_le_one_left (norm_nonneg _) hA |>.trans (hrow m)
    _ = (18*C+12)*((M:ℝ)*Real.sqrt (W:ℝ))*L^2 := by simp; ring
    _ ≤ _ := by
      have ht := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmixed (by positivity : 0≤18*C+12)) (sq_nonneg L)
      convert ht using 1
      ring

/-- A sharp prime twist at either endpoint of each row, with a uniform bound
for the primes omitted by the coprimality mask. -/
theorem chen_ap_switch_box_twist_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ B : ℝ, 0<B ∧ ∀ {N z y i K Q : ℕ} [NeZero Q]
      (χ : DirichletCharacter ℂ Q), 1≤N → (N:ℝ)^(1/4:ℝ)+1≤(y:ℝ) →
      1≤K → K≤N^2 → 1<Q → Q≤N^2 → χ≠1 →
        ‖chenSwitchBoxSum N z y i K χ‖≤B*(N:ℝ)^(7/8:ℝ)*(chenSwitchLog N)^2 := by
  obtain ⟨C,hC,H⟩ := chen_ap_interval_twist_of_dirichletGRH hGRH
  refine ⟨C,hC,?_⟩
  intro N z y i K Q _ χ hN hy hK hKN hQ hQN hχ
  by_cases he : (chenSwitchBoxPairs N z y i).Nonempty
  · obtain ⟨hW,hWN,hMW,hM,_⟩ := chenSwitchBox_ranges hy hN he
    exact H χ (chenSwitchBoxA z y i K) chenSwitchBoxLo (chenSwitchBoxHi N i)
      hN hW hWN hMW hM (chenSwitchBoxA_norm_le z y i K) chenSwitchBoxLo_pos
      (chenSwitchBoxHi_le N i) hK hKN hQ hQN hχ
  · rw [chenSwitchBoxSum_eq_zero_of_empty (Finset.not_nonempty_iff_eq_empty.mp he),norm_zero]
    positivity

end FareyGoldbach
