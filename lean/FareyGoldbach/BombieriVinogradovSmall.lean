import FareyGoldbach.ChenSmallConductor
import FareyGoldbach.ChenSwitchingScales

/-! # The small primitive conductors in the von Mangoldt mean value -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

theorem bv_cutoff_bounds {N : ℕ} (hN : 1 ≤ N) :
    let L := chenSwitchLog N
    let R := ⌈L^12⌉₊
    1 ≤ R ∧ L^12 ≤ (R:ℝ) ∧ (R:ℝ) ≤ 2*L^12 := by
  let L := chenSwitchLog N
  have h₁ : (1:ℝ) ≤ L^12 := one_le_pow₀ (one_le_chenSwitchLog hN)
  have h₂ : L^12 ≤ (⌈L^12⌉₊:ℝ) := Nat.le_ceil _
  have h₃ : (⌈L^12⌉₊:ℝ) < L^12+1 := Nat.ceil_lt_add_one (by positivity)
  exact ⟨by exact_mod_cast h₁.trans h₂,h₂,by linarith only [h₁,h₃]⟩

private theorem bv_weighted_prefix {X : ℕ} (g : ℕ → ℂ) (w : ℕ → ℝ) {B : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hm : Monotone w) (hB : 0 ≤ B)
    (hg : ∀ j ≤ X, ‖∑ i ∈ range (j+1), g i‖ ≤ B) :
    ‖∑ i ∈ range (X+1), w i • g i‖ ≤ 2*w X*B := by
  rw [Finset.sum_range_by_parts]
  simp only [Nat.add_sub_cancel]
  calc
    _ ≤ ‖w X • (∑ i ∈ range (X+1), g i)‖ +
      ‖∑ i ∈ range X, (w (i+1)-w i) • (∑ j ∈ range (i+1),g j)‖ :=
        norm_sub_le ..
    _ ≤ w X*B + ∑ i ∈ range X, (w (i+1)-w i)*B := by
      apply add_le_add
      · simpa [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hw X)] using
          mul_le_mul_of_nonneg_left (hg X le_rfl) (hw X)
      · apply (norm_sum_le ..).trans
        apply sum_le_sum
        intro i hi
        have hd := sub_nonneg.mpr (hm (Nat.le_succ i))
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_left (hg i (Nat.le_of_lt (mem_range.mp hi))) hd
    _ = w X*B + (w X - w 0)*B := by rw [←sum_mul,Finset.sum_range_sub]
    _ ≤ 2*w X*B := by
      linarith only [mul_nonneg (hw 0) hB]

private theorem bv_primeWeight_sum_bound {X N q : ℕ} [NeZero q]
    (hN : 1 ≤ N) (hXN : X ≤ N) {B : ℝ} (hB : 0 ≤ B)
    (χ : DirichletCharacter ℂ q)
    (hg : ∀ x ≤ X, ‖∑ p ∈ x.primesLE, χ (p:ZMod q)‖ ≤ B) :
    ‖∑ n ∈ Icc 1 X, (primeWeight n : ℂ) * χ (n:ZMod q)‖ ≤
      2*chenSwitchLog N*B := by
  let w (n : ℕ) := Real.log (max 1 n : ℕ)
  let g (n : ℕ) := if n.Prime then χ (n:ZMod q) else 0
  have hw (n : ℕ) : 0 ≤ w n := Real.log_nonneg (by
    exact_mod_cast le_max_left 1 n)
  have hm : Monotone w := fun a b hab =>
    Real.log_le_log (by positivity) (by exact_mod_cast max_le_max_left 1 hab)
  have hpr (j : ℕ) : (range (j + 1)).filter Nat.Prime = j.primesLE := by
    ext p
    simp [Nat.mem_primesLE]
  have H := bv_weighted_prefix g w hw hm hB (fun j hj => by
    simpa only [g,←Finset.sum_filter,hpr] using hg j hj)
  have hterm (n : ℕ) : w n • g n = (primeWeight n : ℂ)*χ (n:ZMod q) := by
    by_cases hp : n.Prime
    · simp only [g,w,primeWeight,hp,ite_true,max_eq_right hp.one_le,Complex.real_smul]
    · simp [g,primeWeight,hp]
  simp_rw [hterm] at H
  have hsplit : range (X+1) = insert 0 (Icc 1 X) := by
    ext n
    simp only [mem_range,mem_insert,mem_Icc]
    omega
  rw [hsplit,sum_insert (by simp),show primeWeight 0=0 by simp [primeWeight],
    Complex.ofReal_zero,zero_mul,zero_add] at H
  apply H.trans
  have hlog : w X ≤ Real.log (N:ℝ) := Real.log_le_log (by positivity)
    (by exact_mod_cast max_le hN hXN)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hlog.trans (log_le_chenSwitchLog hN)) (by norm_num)) hB

private theorem bv_weight_error {X N q : ℕ} [NeZero q] (hN : 1 ≤ N) (hXN : X ≤ N)
    (χ : DirichletCharacter ℂ q) :
    ‖(∑ n ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*χ (n:ZMod q)) -
      ∑ n ∈ Icc 1 X, (primeWeight n : ℂ)*χ (n:ZMod q)‖ ≤
      Real.sqrt (N:ℝ)*chenSwitchLog N := by
  by_cases hX : 1 ≤ X
  · rw [←Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ Icc 1 X, ‖(ArithmeticFunction.vonMangoldt n:ℂ)*χ (n:ZMod q)-
          (primeWeight n:ℂ)*χ (n:ZMod q)‖ := norm_sum_le ..
      _ ≤ ∑ n ∈ Icc 1 X, |ArithmeticFunction.vonMangoldt n-primeWeight n| := by
        apply sum_le_sum
        intro n _
        rw [←sub_mul,←Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _)
      _ ≤ Real.sqrt (X:ℝ)*Real.log (X:ℝ) := primePowerMass_le X hX
      _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt (Nat.cast_le.mpr hXN))
        ((Real.log_le_log (by positivity) (Nat.cast_le.mpr hXN)).trans (log_le_chenSwitchLog hN))
        (Real.log_nonneg (Nat.one_le_cast.mpr hX)) (Real.sqrt_nonneg _)
  · have : X=0 := by omega
    subst X
    simp only [Icc_eq_empty_of_lt (by norm_num : (0:ℕ)<1),sum_empty,sub_self,norm_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans (one_le_chenSwitchLog hN))

/-- The small-conductor assumption supplies a uniform Mangoldt estimate for
all prefixes up to N. For prefixes below the fourth root, the trivial bound
is absorbed by the secondary term. -/
theorem bv_small_conductor_mangoldt (hSmall : SmallConductorPrimeTwists) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (X q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), X ≤ N →
        χ.IsPrimitive → 2 ≤ q → q ≤ ⌈(chenSwitchLog N)^12⌉₊ →
        ‖∑ n ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*χ (n:ZMod q)‖
        ≤ C * ((N:ℝ)/(chenSwitchLog N)^29 + Real.sqrt (N:ℝ)*chenSwitchLog N) := by
  obtain ⟨c,hc,H⟩ := hSmall 13 30
  let B := c*12^30
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨2*B+3,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (3:ℕ),
    chenSwitchLog_tendsto_atTop.eventually_ge_atTop (2*12^13:ℝ)] with N hN hBig
  intro X q _ χ hXN hprim hq hqL
  let L := chenSwitchLog N
  have hN₁ : 1 ≤ N := by omega
  have hNp : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hNreal : (1:ℝ)<N := by exact_mod_cast (by omega : 1<N)
  have hL₁ : 1 ≤ L := one_le_chenSwitchLog hN₁
  have hL : 0 < L := zero_lt_one.trans_le hL₁
  have hqR : (q:ℝ) ≤ (L/12)^13 := by
    have hq₂ : (q:ℝ) ≤ 2*L^12 := (Nat.cast_le.mpr hqL).trans (bv_cutoff_bounds hN₁).2.2
    change 2*12^13 ≤ L at hBig
    rw [div_pow]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<12^13)).mpr
    calc
      _ ≤ (2*L^12)*12^13 := mul_le_mul_of_nonneg_right hq₂ (by norm_num)
      _ = (2*12^13)*L^12 := by ring
      _ ≤ L*L^12 := mul_le_mul_of_nonneg_right hBig (by positivity)
      _ = _ := by ring
  have hsqrt : (N:ℝ)^(1/4:ℝ) ≤ Real.sqrt (N:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hNreal.le (by norm_num)
  have hpref (x : ℕ) (hx : x≤X) :
      ‖∑ p ∈ x.primesLE, χ (p:ZMod q)‖ ≤ B*(N:ℝ)/L^30 + Real.sqrt (N:ℝ) := by
    by_cases hbig : (N:ℝ)^(1/4:ℝ) ≤ x
    · have hquarter := Real.one_lt_rpow hNreal (by norm_num : (0:ℝ)<1/4)
      have hx₂ : 2≤x := by exact_mod_cast hquarter.trans_le hbig
      have hlog := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hbig
      rw [Real.log_rpow hNp] at hlog
      have hlog' : L/12 ≤ Real.log (x:ℝ) := by
        have ht := chenSwitchLog_le_three_log hN
        change L ≤ _ at ht
        linarith only [ht,hlog]
      have hLD : 0 < L/12 := by positivity
      have ht := H x q χ hprim hq hx₂ (hqR.trans (pow_le_pow_left₀ hLD.le hlog' 13))
      refine ht.trans (le_trans ?_ (le_add_of_nonneg_right (Real.sqrt_nonneg _)))
      calc
        _ ≤ c*(N:ℝ)/(L/12)^30 := div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hx.trans hXN)) hc.le)
          (by positivity) (pow_le_pow_left₀ hLD.le hlog' 30)
        _ = _ := by dsimp [B]; rw [div_pow]; ring
    · have hsub : x.primesLE ⊆ Icc 1 x := by
        intro p hp
        have hh := Nat.mem_primesLE.mp hp
        exact mem_Icc.mpr ⟨hh.2.pos,hh.1⟩
      have hcard : x.primesLE.card ≤ x := (Finset.card_le_card hsub).trans (by simp)
      calc
        _ ≤ ∑ p ∈ x.primesLE, ‖χ (p:ZMod q)‖ := norm_sum_le ..
        _ ≤ ∑ _p ∈ x.primesLE, (1:ℝ) := sum_le_sum fun p _ => χ.norm_le_one _
        _ = (x.primesLE.card:ℝ) := by simp
        _ ≤ (x:ℝ) := Nat.cast_le.mpr hcard
        _ ≤ Real.sqrt (N:ℝ) := (le_of_not_ge hbig).trans hsqrt
        _ ≤ _ := le_add_of_nonneg_left (by positivity)
  have ha := bv_primeWeight_sum_bound hN₁ hXN (by positivity) χ hpref
  have he := bv_weight_error hN₁ hXN χ
  calc
    _ ≤ ‖(∑ n ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt n:ℂ)*χ (n:ZMod q)) -
        ∑ n ∈ Icc 1 X, (primeWeight n:ℂ)*χ (n:ZMod q)‖ +
        ‖∑ n ∈ Icc 1 X, (primeWeight n:ℂ)*χ (n:ZMod q)‖ := norm_le_norm_sub_add ..
    _ ≤ Real.sqrt (N:ℝ)*L + 2*L*(B*(N:ℝ)/L^30+Real.sqrt (N:ℝ)) := add_le_add he ha
    _ = 2*B*((N:ℝ)/L^29)+3*(Real.sqrt (N:ℝ)*L) := by
      field_simp [hL.ne']
      ring
    _ ≤ _ := by
      change _ ≤ (2*B+3)*((N:ℝ)/L^29+Real.sqrt (N:ℝ)*L)
      nlinarith only [div_nonneg hNp.le (show 0≤L^29 by positivity),
        mul_nonneg (mul_nonneg hB.le (Real.sqrt_nonneg (N:ℝ))) hL.le]

end FareyGoldbach
