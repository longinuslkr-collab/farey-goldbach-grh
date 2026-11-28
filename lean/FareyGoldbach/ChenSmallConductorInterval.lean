import FareyGoldbach.ChenSmallConductor
import FareyGoldbach.ChenSwitchingScales

/-! # Small-conductor prime twists on exact switching intervals -/

open Filter
open scoped Classical BigOperators

namespace FareyGoldbach

private def maskedPrime (k w : ℕ) : ℂ :=
  if w.Prime ∧ w.Coprime k then 1 else 0

theorem chen_masked_prime_prefix_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X k : ℕ) (hk : 1≤k) :
    ‖∑ w ∈ Finset.Icc 1 X, maskedPrime k w * χ (w:ZMod q)‖ ≤
      ‖∑ w ∈ X.primesLE, χ (w:ZMod q)‖ + 2*Real.log (2*(k:ℝ)) := by
  let T := X.primesLE.filter (fun w => ¬w.Coprime k)
  have hP : (Finset.Icc 1 X).filter (fun w => w.Prime ∧ w.Coprime k) = X.primesLE \ T := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff, Nat.mem_primesLE, T]
    constructor
    · rintro ⟨⟨_,hx⟩,hp,hcop⟩
      exact ⟨⟨hx,hp⟩,fun h => h.2 hcop⟩
    · rintro ⟨⟨hx,hp⟩,hc⟩
      exact ⟨⟨hp.pos,hx⟩,hp, by by_contra h; exact hc ⟨⟨hx,hp⟩,h⟩⟩
  have ht : T ⊆ X.primesLE := Finset.filter_subset .. 
  have h_eq : (∑ w ∈ Finset.Icc 1 X, maskedPrime k w * χ (w:ZMod q)) =
      (∑ w ∈ X.primesLE, χ (w:ZMod q)) - ∑ w ∈ T, χ (w:ZMod q) := by
    rw [← Finset.sum_sdiff_eq_sub ht, ← hP, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro w _
    simp only [maskedPrime]
    split_ifs <;> simp
  have hsubset : T ⊆ k.primeFactors := by
    intro w hw
    obtain ⟨hP,hn⟩ := Finset.mem_filter.mp hw
    have hp := (Nat.mem_primesLE.mp hP).2
    exact Nat.mem_primeFactors.mpr ⟨hp, by simpa [hp.coprime_iff_not_dvd] using hn, by omega⟩
  have he : ‖∑ w ∈ T, χ (w:ZMod q)‖ ≤ 2*Real.log (2*(k:ℝ)) := by
    calc
      _ ≤ ∑ w ∈ T, ‖χ (w:ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _w ∈ T, (1:ℝ) := Finset.sum_le_sum fun w _ => χ.norm_le_one _
      _ = (T.card:ℝ) := by simp
      _ ≤ (k.primeFactors.card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsubset)
      _ ≤ _ := primeFactors_card_le_two_log hk
  rw [h_eq]
  exact (norm_sub_le (∑ w ∈ X.primesLE, χ (w:ZMod q)) (∑ w ∈ T, χ (w:ZMod q))).trans (add_le_add le_rfl he)

theorem chen_sum_interval_eq_prefix_sub {lo hi : ℕ} (hlo : 1≤lo) (hle : lo≤hi) (f : ℕ→ℂ) :
    (∑ w ∈ Finset.Icc lo hi, f w) =
      (∑ w ∈ Finset.Icc 1 hi, f w) - ∑ w ∈ Finset.Icc 1 (lo-1), f w := by
  have hs : Finset.Icc 1 (lo-1) ⊆ Finset.Icc 1 hi := by
    intro w hw
    simp only [Finset.mem_Icc] at hw ⊢
    omega
  have hset : Finset.Icc 1 hi \ Finset.Icc 1 (lo-1) = Finset.Icc lo hi := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    omega
  rw [← hset, Finset.sum_sdiff_eq_sub hs]

/-- A logarithmic-power saving in the prime twist for each small primitive
conductor. Excluding the prime divisors of k costs one term per such prime. -/
theorem chen_small_conductor_interval_bound (hSmall : SmallConductorPrimeTwists) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀ (M W k q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q) (a : ℕ→ℂ) (lo hi : ℕ→ℕ),
      χ.IsPrimitive → 1<q → q≤⌈(chenSwitchLog N)^12⌉₊ → 1≤k → k≤N →
      (M:ℝ)*W≤2*N → (M:ℝ)≤2*(N:ℝ)^(3/4:ℝ) →
      (∀ m∈Finset.Icc 1 M, ‖a m‖≤1) →
      (∀ m∈Finset.Icc 1 M, a m≠0 → (N:ℝ)^(1/4:ℝ)+1≤(lo m:ℝ)) →
      (∀ m∈Finset.Icc 1 M, hi m≤W) →
        ‖∑ m ∈ Finset.Icc 1 M, a m * χ (m:ZMod q) *
          (∑ w ∈ Finset.Icc (lo m) (hi m),
             (if w.Prime ∧ w.Coprime k then (1:ℂ) else 0)*χ (w:ZMod q))‖ ≤
        C*((N:ℝ)/(chenSwitchLog N)^30+(N:ℝ)^(3/4:ℝ)*chenSwitchLog N) := by
  obtain ⟨c,hc,H⟩ := hSmall 13 30
  let B := c*12^30
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨4*B+8,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (3:ℕ),
    chenSwitchLog_tendsto_atTop.eventually_ge_atTop (2*12^13:ℝ)] with N hN hBig
  intro M W k q _ χ a lo hi hprim hq hqL hk hkN hMW hM ha hlo hhi
  let L := chenSwitchLog N
  have hNreal : (1:ℝ)<N := by exact_mod_cast (by omega : 1<N)
  have hNp : (0:ℝ)<N := zero_lt_one.trans hNreal
  have hL₁ : 1 ≤ L := one_le_chenSwitchLog (by omega)
  have hL : 0<L := zero_lt_one.trans_le hL₁
  have hquarter := Real.one_lt_rpow hNreal (by norm_num : (0:ℝ)<1/4)
  have hqR : (q:ℝ) ≤ (L/12)^13 := by
    have hceil := Nat.ceil_lt_add_one (show 0≤L^12 by positivity)
    have hq₀ : (q:ℝ) ≤ (⌈L^12⌉₊:ℝ) := Nat.cast_le.mpr hqL
    have hpow : 1 ≤ L^12 := one_le_pow₀ hL₁
    have big : 2*12^13 ≤ L := hBig
    have hprod := mul_le_mul_of_nonneg_right big (pow_nonneg hL.le 12)
    rw [div_pow]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<12^13)).mpr
    have hq₂ : (q:ℝ) ≤ 2*L^12 := by linarith only [hq₀,hceil,hpow]
    calc _ ≤ (2*L^12)*12^13 := mul_le_mul_of_nonneg_right hq₂ (by norm_num)
         _ ≤ _ := by nlinarith only [hprod]
  have hpref (x : ℕ) (hsmall : (N:ℝ)^(1/4:ℝ) ≤ x) (hxW : x≤W) :
      ‖∑ w ∈ Finset.Icc 1 x, maskedPrime k w * χ (w:ZMod q)‖ ≤
        B*(W:ℝ)/L^30+2*L := by
    have hx : 2≤x := by exact_mod_cast (show (1:ℝ)<x from hquarter.trans_le hsmall)
    have hxp : (0:ℝ)<x := Nat.cast_pos.mpr (by omega)
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hsmall
    rw [Real.log_rpow hNp] at hlog
    have hscale : L/12 ≤ Real.log x := by
      have hs := chenSwitchLog_le_three_log hN
      change L ≤ _ at hs
      linarith only [hs,hlog]
    have hxpLog : 0<L/12 := by positivity
    have hlk : Real.log (2*(k:ℝ)) ≤ L := by
      have hk' : (0:ℝ)<k := Nat.cast_pos.mpr hk
      have Hk := Real.log_le_log (show 0<2*(k:ℝ) by positivity)
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hkN) (by norm_num : (0:ℝ)≤2))
      dsimp [L,chenSwitchLog]
      linarith only [Hk]
    have ht := H x q χ hprim hq hx (hqR.trans (pow_le_pow_left₀ hxpLog.le hscale 13))
    apply (chen_masked_prime_prefix_le χ x k hk).trans (add_le_add (ht.trans ?_) (by linarith only [hlk]))
    calc
      _ ≤ c*(W:ℝ)/(L/12)^30 := div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hxW) hc.le) (by positivity)
        (pow_le_pow_left₀ hxpLog.le hscale 30)
      _ = _ := by dsimp [B]; rw [div_pow]; ring
  have hrow (m : ℕ) (hm : m∈Finset.Icc 1 M) :
      ‖a m * χ (m:ZMod q) * (∑ w ∈ Finset.Icc (lo m) (hi m),
        maskedPrime k w * χ (w:ZMod q))‖ ≤ 2*(B*(W:ℝ)/L^30+2*L) := by
    by_cases haz : a m=0
    · simp only [haz,zero_mul,norm_zero]; positivity
    by_cases hempty : hi m < lo m
    · simp only [Finset.Icc_eq_empty_of_lt hempty, Finset.sum_empty, mul_zero, norm_zero]
      positivity
    have hlo' := hlo m hm haz
    have hlpos : 1≤lo m := by exact_mod_cast (show (1:ℝ) ≤ lo m by linarith only [hlo',hquarter])
    have hlow : (N:ℝ)^(1/4:ℝ) ≤ ((lo m-1:ℕ):ℝ) := by
      rw [Nat.cast_sub hlpos,Nat.cast_one]
      linarith only [hlo']
    have hupper : (N:ℝ)^(1/4:ℝ) ≤ hi m :=
      hlow.trans (Nat.cast_le.mpr (by omega))
    have hA : ‖a m * χ (m:ZMod q)‖ ≤ 1 :=
      (norm_mul ..).le.trans ((mul_le_mul (ha m hm) (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans
        (by norm_num))
    rw [chen_sum_interval_eq_prefix_sub hlpos (by omega), norm_mul]
    have hineq := (norm_sub_le ..).trans (add_le_add (hpref (hi m) hupper (hhi m hm))
      (hpref (lo m-1) hlow (by have := hhi m hm; omega)))
    have Hrow := mul_le_mul hA hineq (norm_nonneg _) zero_le_one
    linarith only [Hrow]
  change ‖∑ m ∈ Finset.Icc 1 M, a m * χ (m:ZMod q) *
      (∑ w ∈ Finset.Icc (lo m) (hi m), maskedPrime k w * χ (w:ZMod q))‖ ≤ _
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ‖a m * χ (m:ZMod q) *
      (∑ w ∈ Finset.Icc (lo m) (hi m), maskedPrime k w * χ (w:ZMod q))‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 M, 2*(B*(W:ℝ)/L^30+2*L) := Finset.sum_le_sum hrow
    _ = (M:ℝ)*(2*(B*(W:ℝ)/L^30+2*L)) := by simp
    _ ≤ (4*B+8)*((N:ℝ)/L^30+(N:ℝ)^(3/4:ℝ)*L) := by
      have h1 := mul_le_mul_of_nonneg_right hMW (show 0≤B/L^30 by positivity)
      have h2 := mul_le_mul_of_nonneg_right hM hL.le
      have h3 : 0≤(N:ℝ)/L^30 := by positivity
      have h4 : 0≤B*((N:ℝ)^(3/4:ℝ)*L) := by positivity
      simp only [div_eq_mul_inv] at h1 h3 ⊢
      nlinarith only [h1,h2,h3,h4]

end FareyGoldbach
