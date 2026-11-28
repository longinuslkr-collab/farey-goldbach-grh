import FareyGoldbach.ChenSieveNormalization
import FareyGoldbach.MertensClassical

/-! # Mertens normalization at the exact Chen cutoffs -/

open Filter
open scoped Topology Classical

namespace FareyGoldbach

private theorem primesLE_eq_Ioc_filter (n : ℕ) :
    n.primesLE=(Finset.Ioc 0 n).filter Nat.Prime := by
  ext p
  rw [Nat.mem_primesLE,Finset.mem_filter,Finset.mem_Ioc]
  exact ⟨fun h ↦ ⟨⟨h.2.pos,h.1⟩,h.2⟩, fun h ↦ ⟨h.1.2,h.2⟩⟩

/-- Mertens' second theorem for real arguments with an inclusive floor endpoint. -/
theorem chen_prime_reciprocal_mertens :
    ∃ B : ℝ, Tendsto (fun x : ℝ ↦ (∑ p∈(⌊x⌋₊).primesLE,1/(p:ℝ))-Real.log (Real.log x))
      atTop (𝓝 B) := by
  refine ⟨Mertens.M,?_⟩
  have hE := (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'
  have h : Tendsto (fun x : ℝ ↦ Mertens.M+Mertens.E₂p x) atTop (𝓝 Mertens.M) := by
    simpa only [add_zero] using (tendsto_const_nhds (x:=Mertens.M)).add hE
  apply h.congr'
  filter_upwards with x
  rw [primesLE_eq_Ioc_filter,Mertens.sum_prime_div_eq]
  ring

private theorem chenPrimesBelow_eq_range (z : ℕ) :
    chenPrimesBelow z = (Finset.range z).filter Nat.Prime := by
  ext p
  simp only [chenPrimesBelow,Finset.mem_filter,Finset.mem_Icc,Finset.mem_range]
  constructor
  · rintro ⟨⟨h₁,h₂⟩,hp⟩
    exact ⟨by omega,hp⟩
  · rintro ⟨h,hp⟩
    exact ⟨⟨hp.pos,by omega⟩,hp⟩

private theorem chenMertensProduct_succ (n : ℕ) :
    chenMertensProduct (n+1) = (if n.Prime then 1-1/(n:ℝ) else 1)*chenMertensProduct n := by
  simp only [chenMertensProduct,chenPrimesBelow_eq_range,Finset.prod_filter,Finset.prod_range_succ]
  ring

private theorem chenMertensProduct_inclusive :
    Tendsto (fun n : ℕ ↦ Real.log (n:ℝ)*chenMertensProduct (n+1)) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have hE := ((Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₃.bound').comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlim := (tendsto_const_nhds (x:=Real.exp (-Real.eulerMascheroniConstant))).mul hE.rexp
  simp only [Real.exp_zero,mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  have he := Mertens.prod_one_minus_div_prime_eq (x:=(n:ℝ)) (by exact_mod_cast (show 1<n by omega))
  rw [Nat.floor_natCast] at he
  have hprod : chenMertensProduct (n+1) = ∏ p∈(Finset.Ioc 0 n).filter Nat.Prime,(1-1/(p:ℝ)) := by
    unfold chenMertensProduct chenPrimesBelow
    rfl
  rw [hprod,he]
  have hlog : Real.log (n:ℝ)≠0 := (Real.log_pos (by exact_mod_cast (show 1<n by omega))).ne'
  change _ = Real.log (n:ℝ)*(_/Real.log (n:ℝ))
  field_simp
  rfl

/-- Mertens' product theorem for primes strictly below the natural cutoff. -/
theorem chenMertensProduct_tendsto :
    Tendsto (fun z : ℕ ↦ Real.log (z:ℝ)*chenMertensProduct z) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  let f (z : ℕ) : ℝ := if z.Prime then 1-1/(z:ℝ) else 1
  have hi := (tendsto_const_nhds (x:=(1:ℝ))).div_atTop (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlo : Tendsto (fun z : ℕ ↦ 1-1/(z:ℝ)) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x:=(1:ℝ))).sub hi
  have hf : Tendsto f atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    · filter_upwards with z
      dsimp only [f]
      split <;> linarith [show 0≤1/(z:ℝ) by positivity]
    · filter_upwards with z
      dsimp only [f]
      split <;> linarith [show 0≤1/(z:ℝ) by positivity]
  have hlim := chenMertensProduct_inclusive.div hf (by norm_num)
  rw [div_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with z hz
  have hz' : (1:ℝ)<z := by exact_mod_cast (show 1<z by omega)
  have hf' : f z≠0 := by
    dsimp only [f]
    split
    · exact (sub_pos.mpr ((one_div_lt (by linarith) zero_lt_one).mpr (by simpa using hz'))).ne'
    · norm_num
  change Real.log (z:ℝ)*chenMertensProduct (z+1)/f z=_
  rw [chenMertensProduct_succ]
  change Real.log (z:ℝ)*(f z*chenMertensProduct z)/f z=_
  field_simp

end FareyGoldbach
