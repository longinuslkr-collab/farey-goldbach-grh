import FareyGoldbach.SmallConductorFiniteRange
import FareyGoldbach.BVPrimeAbel
import FareyGoldbach.ChenSmallConductor

/-! # From uniform small-conductor Mangoldt sums to prime counting and prime twists -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

def SmallConductorMangoldtTwists : Prop :=
  ∀ A B : ℕ, ∃ C : ℝ, 0<C ∧ ∀ (X q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → 2≤X → (q:ℝ)≤(Real.log (X:ℝ))^A →
      ‖(∑ n∈Icc 1 X,(ArithmeticFunction.vonMangoldt n:ℂ)*χ (n:ZMod q))-
        (if χ=1 then (X:ℂ) else 0)‖ ≤ C*(X:ℝ)/(Real.log (X:ℝ))^B

theorem primeCounting_ratio_of_smallConductorMangoldt (h : SmallConductorMangoldtTwists) :
    Tendsto (fun N : ℕ => (N.primeCounting:ℝ)/((N:ℝ)/Real.log (N:ℝ))) atTop (𝓝 1) := by
  obtain ⟨C,_,hb⟩ := h 0 1
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hlog := Real.tendsto_log_atTop.comp hn
  have herr {N : ℕ} (hN : 2≤N) : |Chebyshev.psi (N:ℝ)-N|≤C*N/Real.log N := by
    have H := hb N 1 1 DirichletCharacter.isPrimitive_one_level_one hN (by simp)
    have he (n : ℕ) : (1:DirichletCharacter ℂ 1) (n:ZMod 1)=1 :=
      (congrArg _ (Subsingleton.elim (n:ZMod 1) 1)).trans (map_one _)
    have hset : Ioc 0 N=Icc 1 N := by ext i; simp; omega
    rw [Chebyshev.psi,Nat.floor_natCast,hset,←Real.norm_eq_abs,←Complex.norm_real]
    push_cast
    simpa only [he,mul_one,ite_true,pow_one] using H
  have hz : Tendsto (fun n : ℕ => (Chebyshev.psi n-n)/(n:ℝ)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hu := (tendsto_const_nhds (x:=C)).div_atTop hlog
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hu
    filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn'
    have hp : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hp]
    calc _ ≤ (C*n/Real.log n)/n := div_le_div_of_nonneg_right (herr hn') hp.le
      _ = _ := by change _=C/Real.log (n:ℝ); field_simp
  have htheta : Tendsto (fun n : ℕ => (Chebyshev.psi n-Chebyshev.theta n)/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Pi.sub_apply,id_eq] using
      Chebyshev.isLittleO_psi_sub_theta_id.tendsto_div_nhds_zero.comp hn
  have hpi : Tendsto (fun n : ℕ => ((n.primeCounting:ℝ)*Real.log n-Chebyshev.theta n)/(n:ℝ))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using Chebyshev.isLittleO_primeCounting_mul_log_sub_theta.tendsto_div_nhds_zero.comp hn
  have hall := ((hpi.add hz).sub htheta).add (tendsto_const_nhds (x:=(1:ℝ)))
  simp only [zero_add,sub_zero] at hall
  apply hall.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hh
  have hp : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hl : 0<Real.log (n:ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hh)
  field_simp
  ring

private theorem smallPrime_card_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ‖∑ p∈N.primesLE,χ p‖≤(N:ℝ) := by
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum (fun p (_ : p∈N.primesLE) => χ.norm_le_one (p:ZMod q))).trans
  simp only [sum_const,nsmul_eq_mul,mul_one]
  exact Nat.cast_le.mpr (by
    have hs : N.primesLE⊆Icc 1 N := fun p hp =>
      mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos,(Nat.mem_primesLE.mp hp).1⟩
    simpa using Finset.card_le_card hs)

/-- For long prefixes the conductor is at most log(j)^(2A). For the remaining
prefixes the elementary bound j log(N) suffices. -/
theorem smallConductorPrimeTwists_of_smallConductorMangoldt (h : SmallConductorMangoldtTwists) :
    SmallConductorPrimeTwists := by
  intro A B
  obtain ⟨C,hC,hb⟩ := h (2*A) B
  let D := (2:ℝ)^(B+1)*((B+1).factorial:ℝ)
  let F := (4:ℝ)^B+C*2^B+4*D
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨F,by dsimp only [F]; positivity,?_⟩
  intro N q _ χ hprim hq hN hcond
  let L := Real.log (N:ℝ)
  have hNp : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hL : 0<L := Real.log_pos (Nat.one_lt_cast.mpr hN)
  have hχ : χ≠1 := fun hh => (Nat.ne_of_gt hq) (eq_one_of_isPrimitive_of_eq_one hprim hh)
  by_cases hbig : 4≤L
  · let U := C*2^B*(N:ℝ)/L^B
    let R := Real.sqrt N*L
    have hU : 0≤U := by dsimp [U]; positivity
    have hR : 0≤R := by dsimp [R]; positivity
    have hprefix (j : ℕ) (hj : j≤N) :
        ‖∑ n∈Icc 1 j,(ArithmeticFunction.vonMangoldt n:ℂ)*χ n‖≤U+R := by
      by_cases hjr : Real.sqrt (N:ℝ)≤j
      · have hj₂ : 2≤j := by
          have h₁ : (1:ℝ)<Real.sqrt N := by
            have h' : (1:ℝ)<N := Nat.one_lt_cast.mpr hN
            nlinarith only [h',Real.sq_sqrt hNp.le,Real.sqrt_nonneg (N:ℝ)]
          exact Nat.one_lt_cast.mp (h₁.trans_le hjr)
        have hjlog := Real.log_le_log (Real.sqrt_pos.mpr hNp) hjr
        rw [Real.log_sqrt hNp.le] at hjlog
        change L/2≤Real.log (j:ℝ) at hjlog
        have hs : L≤(Real.log j)^2 := by nlinarith only [hbig,hjlog,sq_nonneg (Real.log j-2)]
        have hqj : (q:ℝ)≤Real.log j^(2*A) := by
          rw [pow_mul]
          exact hcond.trans (pow_le_pow_left₀ hL.le hs _)
        have ht := hb j q χ hprim hj₂ hqj
        simp only [hχ,ite_false,sub_zero] at ht
        apply ht.trans
        refine le_add_of_le_of_nonneg ?_ hR
        calc _ ≤ C*(N:ℝ)/(L/2)^B :=
              div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hj) hC.le)
                (by positivity) (pow_le_pow_left₀ (by positivity) hjlog B)
          _ = U := by dsimp only [U]; rw [div_pow,div_div_eq_mul_div]; ring
      · apply (norm_mangoldt_prefix_le_log χ hj).trans
        apply le_add_of_nonneg_of_le hU
        exact mul_le_mul_of_nonneg_right (le_of_not_ge hjr) hL.le
    have hw := bvWeight_bounds (show 2≤Real.log (N:ℝ) by linarith only [hbig])
    have ha := abel_prime_bound (bvPrimeWeight N) (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)*χ n)
      (U+R) (fun i => (hw.1 i).1) hw.2.1 (fun j hj => by rw [bv_range_mangoldt]; exact hprefix j hj)
    have hap := bvPrimeWeight_approx χ (by change 2≤L; linarith only [hbig]) (by omega : 1≤N)
    have hsup := ha.trans (mul_le_of_le_one_left (add_nonneg hU hR) (hw.1 0).2)
    have htriangle (s t : ℂ) : ‖s‖≤‖s-t‖+‖t‖ := by
      simpa only [sub_add_cancel] using norm_add_le (s-t) t
    have ht := htriangle (∑ p∈N.primesLE,χ p) (∑ n∈range (N+1),bvPrimeWeight N n •
      ((ArithmeticFunction.vonMangoldt n:ℂ)*χ n))
    have hroot := Real.sqrt_nonneg (N:ℝ)
    have hrL : Real.sqrt N≤R := le_mul_of_one_le_right hroot (by linarith only [hbig])
    have hsum : ‖∑ p∈N.primesLE,χ p‖≤U+4*R := by
      change _≤Real.sqrt (N:ℝ)+2*Real.sqrt N*L at hap
      change Real.sqrt N≤Real.sqrt N*L at hrL
      dsimp only [R] at hsup ⊢
      linarith only [ht,hap,hsup,hrL]
    have hlogpow := log_pow_le_sqrt (B+1) (x:=(N:ℝ)) (Nat.one_le_cast.mpr (by omega))
    change L^(B+1)≤D*Real.sqrt N at hlogpow
    have hrem : R*L^B≤D*(N:ℝ) := by
      calc _ = Real.sqrt N*L^(B+1) := by dsimp only [R]; rw [pow_succ]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlogpow hroot
        _ = D*(Real.sqrt N)^2 := by ring
        _ = _ := by rw [Real.sq_sqrt hNp.le]
    apply (le_div_iff₀ (pow_pos hL B)).mpr
    apply (mul_le_mul_of_nonneg_right hsum (pow_nonneg hL.le B)).trans
    rw [add_mul,show U*L^B=C*2^B*(N:ℝ) by dsimp only [U]; field_simp]
    dsimp only [F]
    nlinarith only [hrem,mul_nonneg (show 0≤(4:ℝ)^B by positivity) hNp.le]
  · apply (le_div_iff₀ (pow_pos hL B)).mpr
    calc _ ≤ (N:ℝ)*4^B := mul_le_mul (smallPrime_card_bound χ N)
            (pow_le_pow_left₀ hL.le (le_of_not_ge hbig) B) (pow_nonneg hL.le _) hNp.le
      _ ≤ F*N := by
        dsimp only [F]
        nlinarith only [mul_nonneg (show 0≤C*2^B by positivity) hNp.le,
          mul_nonneg hD.le hNp.le]

end FareyGoldbach
