import FareyGoldbach.PolyaVinogradov
import FareyGoldbach.ChenSwitchingAssembly

/-! # Explicit Type I bounds for Vaughan's identity -/

open Finset
open scoped Classical BigOperators

namespace FareyGoldbach

private theorem pv_range_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 2≤q) (Y : ℕ) :
    (∑ n∈range (Y+1), χ (n:ZMod q)) = ∑ n∈Icc 1 Y, χ (n:ZMod q) := by
  let : Fact (1<q) := ⟨hq⟩
  have hI : (range (Y+1)).erase 0 = Icc 1 Y := by ext n; simp; omega
  rw [← hI]
  symm
  apply Finset.sum_erase
  simpa only [Nat.cast_zero] using χ.map_zero

theorem polya_vinogradov_log {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2≤q) (Y : ℕ) :
    ‖∑ n∈Icc 1 Y, (Real.log (n:ℝ):ℂ)*χ (n:ZMod q)‖ ≤
      8*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ))*Real.log (Y:ℝ) := by
  let w (j : ℕ) := Real.log (j:ℝ)
  let g (j : ℕ) := χ (j:ZMod q)
  let B := 4*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ))
  have hw (n : ℕ) : 0≤w n := by
    rcases n with _ | n
    · simp [w]
    · apply Real.log_nonneg; exact_mod_cast (by omega : 1≤n+1)
  have hmono (n : ℕ) : w n ≤ w (n+1) := by
    rcases n with _ | n
    · simp [w]
    · apply Real.log_le_log (by positivity)
      exact_mod_cast (Nat.le_succ (n+1))
  have hb (n : ℕ) : ‖∑ j∈range (n+1), g j‖≤B := by
    dsimp only [g,B]
    rw [pv_range_eq χ hq]
    exact polya_vinogradov χ hχ hq n
  have he : (∑ n∈Icc 1 Y, (Real.log (n:ℝ):ℂ)*χ (n:ZMod q)) = ∑ n∈range (Y+1), w n • g n := by
    have hI : (range (Y+1)).erase 0 = Icc 1 Y := by ext n; simp; omega
    rw [← hI, ← Finset.sum_erase (s:=range (Y+1)) (f:=fun n => w n • g n) (a:=0) (by simp [w])]
    exact Finset.sum_congr rfl fun _ _ => rfl
  rw [he,Finset.sum_range_by_parts]
  simp only [Nat.add_sub_cancel]
  calc
    _ ≤ ‖w Y • (∑ i ∈ range (Y+1), g i)‖ +
        ‖∑ i∈range Y,(w (i+1)-w i) • (∑ j∈range (i+1),g j)‖ := norm_sub_le .. 
    _ ≤ w Y*B + ∑ i∈range Y,(w (i+1)-w i)*B := by
      apply add_le_add
      · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hw _)]
        exact mul_le_mul_of_nonneg_left (hb _) (hw _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hmono i))]
        exact mul_le_mul_of_nonneg_left (hb _) (sub_nonneg.mpr (hmono i))
    _ = _ := by
      rw [← Finset.sum_mul,Finset.sum_range_sub]
      simp only [w,Nat.cast_zero,Real.log_zero,sub_zero,B]
      ring

private theorem typeI_rows {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (U : ℕ)
    (a f : ℕ→ℂ) (B T : ℝ) (hB : 0≤B)
    (ha : ∀ m∈Icc 1 U, ‖a m‖≤B) (hf : ∀ m∈Icc 1 U, ‖f m‖≤T) :
    ‖∑ m∈Icc 1 U, a m*χ (m:ZMod q)*f m‖ ≤ (U:ℝ)*B*T := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _m∈Icc 1 U,B*T := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul,norm_mul]
      apply mul_le_mul _ (hf m hm) (norm_nonneg _) hB
      simpa only [mul_one] using mul_le_mul (ha m hm) (χ.norm_le_one _) (norm_nonneg _) hB
    _ = _ := by simp [mul_assoc]

theorem vaughan_typeI_prefix {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2≤q) (U : ℕ) (r : ℕ→ℕ) (a : ℕ→ℂ) (B : ℝ) (hB : 0≤B)
    (ha : ∀ m∈Icc 1 U, ‖a m‖≤B) :
    ‖∑ m∈Icc 1 U, a m*χ (m:ZMod q)*(∑ w∈Icc 1 (r m), χ (w:ZMod q))‖ ≤
       (U:ℝ)*B*(4*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ))) :=
  typeI_rows χ U a _ B _ hB ha fun m _ => polya_vinogradov χ hχ hq (r m)

theorem vaughan_typeI_log_prefix {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2≤q) (U : ℕ) (r : ℕ→ℕ) (a : ℕ→ℂ) (B : ℝ) (hB : 0≤B)
    (ha : ∀ m∈Icc 1 U, ‖a m‖≤B) (N : ℕ) (hN : 1≤N) (hr : ∀ m∈Icc 1 U, r m≤N) :
    ‖∑ m∈Icc 1 U, a m*χ (m:ZMod q)*
      (∑ w∈Icc 1 (r m), (Real.log (w:ℝ):ℂ)*χ (w:ZMod q))‖ ≤
       (U:ℝ)*B*(8*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ))*Real.log (N:ℝ)) := by
  apply typeI_rows χ U a _ B _ hB ha
  intro m hm
  apply (polya_vinogradov_log χ hχ hq (r m)).trans
  have hlq : 0≤Real.log (2*(q:ℝ)) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤2*q))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  by_cases h : r m = 0
  · simp only [h,Nat.cast_zero,Real.log_zero]
    exact Real.log_nonneg (Nat.one_le_cast.mpr hN)
  · exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)) (Nat.cast_le.mpr (hr m hm))


/-- The three short pieces of Vaughan's identity, averaged over all primitive
conductors in (R,D]. The power 19/20 is uniform up to D ≤ √N. -/
theorem vaughan_typeI_mean_bound (N U R D : ℕ) (r : ℕ→ℕ) (a₀ a₁ a₂ : ℕ→ℂ)
    (hN : 1≤N) (hR : 1≤R) (hD : 1≤D) (hDN : D≤N)
    (hU : (U:ℝ)≤(N:ℝ)^(1/5:ℝ)) (hDpow : (D:ℝ)≤Real.sqrt N)
    (hr : ∀ m∈Icc 1 U, r m≤N)
    (ha₀ : ∀ m∈Icc 1 U, ‖a₀ m‖≤chenSwitchLog N)
    (ha₁ : ∀ m∈Icc 1 U, ‖a₁ m‖≤chenSwitchLog N)
    (ha₂ : ∀ m∈Icc 1 U, ‖a₂ m‖≤1) :
    (∑ q∈Ioc R D, chenPrimitiveNorm q (fun χ =>
       (∑ m∈Icc 1 U, a₀ m*χ (m:ZMod q)) -
       (∑ m∈Icc 1 U, a₁ m*χ (m:ZMod q)*(∑ w∈Icc 1 (r m),χ (w:ZMod q))) +
       (∑ m∈Icc 1 U, a₂ m*χ (m:ZMod q)*(∑ w∈Icc 1 (r m),(Real.log (w:ℝ):ℂ)*χ (w:ZMod q))))
       / (q:ℝ)) ≤ 13*(chenSwitchLog N)^2*(N:ℝ)^(19/20:ℝ) := by
  let L := chenSwitchLog N
  let E := (U:ℝ)*Real.sqrt D*L^2
  have hL₁ : 1≤L := one_le_chenSwitchLog hN
  have hL : 0≤L := zero_le_one.trans hL₁
  have hD₁ : 1≤Real.sqrt D := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hD)
  have hDp : 0≤Real.sqrt D := Real.sqrt_nonneg _
  have he : 0≤E := by dsimp [E]; positivity
  have hper (q : ℕ) (hm : q∈Ioc R D) :
      chenPrimitiveNorm q (fun χ =>
       (∑ m∈Icc 1 U, a₀ m*χ (m:ZMod q)) -
       (∑ m∈Icc 1 U, a₁ m*χ (m:ZMod q)*(∑ w∈Icc 1 (r m),χ (w:ZMod q))) +
       (∑ m∈Icc 1 U, a₂ m*χ (m:ZMod q)*(∑ w∈Icc 1 (r m),(Real.log (w:ℝ):ℂ)*χ (w:ZMod q))))
       / (q:ℝ) ≤ 13*E := by
    obtain ⟨hql,hqu⟩ := Finset.mem_Ioc.mp hm
    have hq : 2≤q := by omega
    let : NeZero q := ⟨by omega⟩
    apply chenPrimitiveNorm_div_le_of_bound _ (by positivity)
    intro χ hχ
    have hs : Real.sqrt q ≤ Real.sqrt D := Real.sqrt_le_sqrt (Nat.cast_le.mpr hqu)
    have hq' : (0:ℝ)<q := Nat.cast_pos.mpr (by omega)
    have hlq : 0≤Real.log (2*(q:ℝ)) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤2*q))
    have hlog : Real.log (2*(q:ℝ))≤L := by
      have h := Real.log_le_log (by positivity : 0<2*(q:ℝ))
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hqu.trans hDN)) (by norm_num : (0:ℝ)≤2))
      dsimp [L,chenSwitchLog]
      linarith only [h]
    have h0 : ‖∑ m∈Icc 1 U,a₀ m*χ (m:ZMod q)‖ ≤ E := by
      have hbase : ‖∑ m∈Icc 1 U,a₀ m*χ (m:ZMod q)‖ ≤ (U:ℝ)*L := by
        simpa using typeI_rows χ U a₀ (fun _=>1) L 1 hL ha₀ (by simp)
      apply hbase.trans
      have h1 : 1 ≤ Real.sqrt D*L := one_le_mul_of_one_le_of_one_le hD₁ hL₁
      have ht := mul_le_mul_of_nonneg_left h1 (mul_nonneg (Nat.cast_nonneg (α:=ℝ) U) hL)
      dsimp [E]
      nlinarith only [ht]
    have h1 : ‖∑ m∈Icc 1 U,a₁ m*χ (m:ZMod q)*(∑ w∈Icc 1 (r m),χ (w:ZMod q))‖ ≤ 4*E := by
      apply (vaughan_typeI_prefix χ hχ hq U r a₁ L hL ha₁).trans
      have hg := mul_le_mul hs hlog hlq hDp
      have hh := mul_le_mul_of_nonneg_left hg (mul_nonneg (Nat.cast_nonneg (α:=ℝ) U) hL)
      dsimp [E]
      nlinarith only [hh]
    have h2 : ‖∑ m∈Icc 1 U,a₂ m*χ (m:ZMod q)*
        (∑ w∈Icc 1 (r m),(Real.log (w:ℝ):ℂ)*χ (w:ZMod q))‖ ≤ 8*E := by
      apply (vaughan_typeI_log_prefix χ hχ hq U r a₂ 1 zero_le_one ha₂ N hN hr).trans
      have hg := mul_le_mul hs hlog hlq hDp
      have hh := mul_le_mul hg (log_le_chenSwitchLog hN) (Real.log_nonneg (Nat.one_le_cast.mpr hN))
        (mul_nonneg hDp hL)
      have hw := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α:=ℝ) U)
      dsimp [E]
      nlinarith only [hw]
    exact (norm_add_le ..).trans ((add_le_add (norm_sub_le ..) le_rfl).trans
      ((add_le_add (add_le_add h0 h1) h2).trans (by linarith only)))
  have hp : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hd : (D:ℝ)≤(N:ℝ)^(1/2:ℝ) := by simpa only [←Real.sqrt_eq_rpow] using hDpow
  have hqtr : Real.sqrt (D:ℝ)≤(N:ℝ)^(1/4:ℝ) := by
    apply (Real.sqrt_le_sqrt hd).trans_eq
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hp.le]
    norm_num
  have hpow : (D:ℝ)*U*Real.sqrt D≤(N:ℝ)^(19/20:ℝ) := by
    calc _ ≤ (N:ℝ)^(1/2:ℝ)*(N:ℝ)^(1/5:ℝ)*(N:ℝ)^(1/4:ℝ) :=
              mul_le_mul (mul_le_mul hd hU (Nat.cast_nonneg _) (by positivity)) hqtr hDp (by positivity)
         _ = _ := by rw [←Real.rpow_add hp,←Real.rpow_add hp]; norm_num
  calc
    _ ≤ ∑ _q∈Ioc R D, 13*E := Finset.sum_le_sum hper
    _ ≤ (D:ℝ)*(13*E) := by
      simp only [Finset.sum_const, nsmul_eq_mul,Nat.card_Ioc]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le ..)) (by positivity)
    _ ≤ _ := by
      change _ ≤ 13*L^2*_
      dsimp only [E]
      nlinarith only [mul_le_mul_of_nonneg_left hpow (show 0≤L^2 by positivity)]

end FareyGoldbach
