import FareyGoldbach.LocalLogDerivative

/-! # Nonnegative Dirichlet series for the Estermann products -/

open Complex ArithmeticFunction
open scoped ComplexOrder

namespace FareyGoldbach

private noncomputable def charAF {q : ℕ} (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  toArithmeticFunction (fun n : ℕ => χ (n : ZMod q))

private theorem charAF_apply_of_pos {q : ℕ} (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 0<n) :
    charAF χ n = χ (n : ZMod q) := by
  simp [charAF,toArithmeticFunction,hn.ne']

private theorem charAF_prime_pow {q : ℕ} (χ : DirichletCharacter ℂ q) {p : ℕ} (hp : p.Prime)
    (k : ℕ) : charAF χ (p^k) = (χ (p : ZMod q))^k := by
  rw [charAF_apply_of_pos χ (Nat.pow_pos hp.pos),Nat.cast_pow,map_pow]

private theorem zeta_prime_pow_complex {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (zeta : ArithmeticFunction ℂ) (p^k) = 1 := by
  rw [ArithmeticFunction.natCoe_apply,zeta_apply_ne (Nat.pow_pos hp.pos).ne',Nat.cast_one]

private theorem conv_congr_prime_pow {p : ℕ} (hp : p.Prime)
    {a b c d : ArithmeticFunction ℂ}
    (h₁ : ∀ k : ℕ, a (p^k) = c (p^k)) (h₂ : ∀ k : ℕ, b (p^k) = d (p^k)) (k : ℕ) :
    (a*b) (p^k) = (c*d) (p^k) := by
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨i,_,hi⟩ := (Nat.dvd_prime_pow hp).mp
    (Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx))
  obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow hp).mp
    (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx))
  rw [hi,hj,h₁ i,h₂ j]

/-- Coefficients of ζ times the three character series at a common level. -/
noncomputable def estermannFourCoeffs {q : ℕ} (χ ψ : DirichletCharacter ℂ q) :
    ArithmeticFunction ℂ :=
  χ.zetaMul * (charAF ψ * charAF (χ*ψ))

set_option maxHeartbeats 500000 in
private theorem estermannFour_prime_pow_nonneg {q : ℕ} (χ ψ : DirichletCharacter ℂ q)
    (hχ : χ^2=1) (hψ : ψ^2=1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0≤estermannFourCoeffs χ ψ (p^k) := by
  let A : ArithmeticFunction ℂ := zeta
  let B := charAF χ
  let C := charAF ψ
  let D := charAF (χ*ψ)
  change 0 ≤ ((A*B)*(C*D)) (p^k)
  have hA (j : ℕ) : A (p^j)=1 := zeta_prime_pow_complex hp j
  have hB (j : ℕ) : B (p^j)=(χ (p:ZMod q))^j := charAF_prime_pow χ hp j
  have hC (j : ℕ) : C (p^j)=(ψ (p:ZMod q))^j := charAF_prime_pow ψ hp j
  have hD (j : ℕ) : D (p^j)=((χ (p:ZMod q))*(ψ (p:ZMod q)))^j := by
    rw [show D (p^j) = _ from charAF_prime_pow (χ*ψ) hp j, MulChar.mul_apply]
  have hPosB (n : ℕ) : 0≤(A*B) n := DirichletCharacter.zetaMul_nonneg hχ n
  have hPosC (n : ℕ) : 0≤(A*C) n := DirichletCharacter.zetaMul_nonneg hψ n
  have conv_nonneg (f : ArithmeticFunction ℂ) (hf : ∀ n, 0 ≤ f n) :
      0 ≤ (f*f) (p^k) := by
    rw [ArithmeticFunction.mul_apply]
    exact Finset.sum_nonneg (fun _ _ => mul_nonneg (hf _) (hf _))
  by_cases hunit : IsUnit (p:ZMod q)
  · have hx : χ (p:ZMod q)=1 ∨ χ (p:ZMod q)= -1 := by
      have h := MulChar.isQuadratic_iff_sq_eq_one.mpr hχ (p : ZMod q)
      exact h.resolve_left ((MulChar.apply_ne_zero_iff).mpr hunit)
    have hy : ψ (p:ZMod q)=1 ∨ ψ (p:ZMod q)= -1 := by
      have h := MulChar.isQuadratic_iff_sq_eq_one.mpr hψ (p : ZMod q)
      exact h.resolve_left ((MulChar.apply_ne_zero_iff).mpr hunit)
    rcases hx with hx | hx
    · have hrep : (A*B)*(C*D) = (A*C)*(B*D) := by ring
      have e (j : ℕ) : (B*D) (p^j)=(A*C) (p^j) :=
        conv_congr_prime_pow hp
          (fun i => by rw [hB,hx,one_pow,hA])
          (fun i => by rw [hD,hx,one_mul,hC]) j
      rw [hrep,conv_congr_prime_pow hp (c:=A*C) (fun _ => rfl) e k]
      exact conv_nonneg _ hPosC
    · rcases hy with hy | hy
      · have e (j : ℕ) : (C*D) (p^j)=(A*B) (p^j) :=
          conv_congr_prime_pow hp
            (fun i => by rw [hC,hy,one_pow,hA])
            (fun i => by rw [hD,hy,mul_one,hB]) j
        rw [conv_congr_prime_pow hp (c:=A*B) (fun _ => rfl) e k]
        exact conv_nonneg _ hPosB
      · have e (j : ℕ) : (D*C) (p^j)=(A*B) (p^j) :=
          conv_congr_prime_pow hp
            (fun i => by rw [hD,hx,hy,hA]; norm_num)
            (fun i => by rw [hC,hB,hy,hx]) j
        rw [mul_comm C D,conv_congr_prime_pow hp (c:=A*B) (fun _ => rfl) e k]
        exact conv_nonneg _ hPosB
  · have hx : χ (p:ZMod q)=0 := MulChar.map_nonunit _ hunit
    have hy : ψ (p:ZMod q)=0 := MulChar.map_nonunit _ hunit
    have hone (j : ℕ) : (1 : ArithmeticFunction ℂ) (p^j) = (0:ℂ)^j := by
      cases j with
      | zero => simp
      | succ j =>
        rw [zero_pow (Nat.succ_ne_zero j), ArithmeticFunction.one_apply_ne]
        exact (one_lt_pow₀ hp.one_lt (Nat.succ_ne_zero j)).ne'
    have hEq : ((A*B)*(C*D)) (p^k) = ((A*1)*(1*1)) (p^k) :=
      conv_congr_prime_pow hp
        (fun j => conv_congr_prime_pow hp (fun _ => rfl)
          (fun i => by rw [hB,hx,hone]) j)
        (fun j => conv_congr_prime_pow hp
          (fun i => by rw [hC,hy,hone])
          (fun i => by rw [hD,hx,zero_mul,hone]) j) k
    rw [hEq,mul_one,mul_one,mul_one,hA]
    exact zero_le_one

private theorem isMultiplicative_estermannFour {q : ℕ} (χ ψ : DirichletCharacter ℂ q) :
    (estermannFourCoeffs χ ψ).IsMultiplicative :=
  χ.isMultiplicative_zetaMul.mul ((DirichletCharacter.isMultiplicative_toArithmeticFunction ψ).mul
    (DirichletCharacter.isMultiplicative_toArithmeticFunction (χ*ψ)))

theorem estermannFourCoeffs_apply_one {q : ℕ} (χ ψ : DirichletCharacter ℂ q) :
    estermannFourCoeffs χ ψ 1 = 1 := (isMultiplicative_estermannFour χ ψ).map_one

theorem estermannFourCoeffs_nonneg {q : ℕ} (χ ψ : DirichletCharacter ℂ q)
    (hχ : χ^2=1) (hψ : ψ^2=1) (n : ℕ) : 0 ≤ estermannFourCoeffs χ ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero,le_rfl]
  · rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization
      (estermannFourCoeffs χ ψ) (isMultiplicative_estermannFour χ ψ) hn]
    exact Finset.prod_nonneg (fun p hp =>
      estermannFour_prime_pow_nonneg χ ψ hχ hψ (Nat.prime_of_mem_primeFactors hp) _)

private theorem charAF_LSeriesSummable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) : LSeriesSummable (charAF χ) s := by
  exact (LSeriesSummable_congr (f:=charAF χ) (g:=fun n : ℕ => χ (n : ZMod q)) _
    (fun hn => charAF_apply_of_pos χ (Nat.pos_of_ne_zero hn))).mpr
      (ZMod.LSeriesSummable_of_one_lt_re χ hs)

private theorem charAF_LSeries_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) : LSeries (charAF χ) s = χ.LFunction s := by
  rw [χ.LFunction_eq_LSeries hs]
  exact LSeries_congr (fun hn => charAF_apply_of_pos χ (Nat.pos_of_ne_zero hn)) _

theorem estermannTwo_LSeries_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : LSeries χ.zetaMul s = riemannZeta s * χ.LFunction s := by
  change LSeries (↑((zeta : ArithmeticFunction ℂ)*charAF χ)) s = _
  have he : (⇑(zeta : ArithmeticFunction ℂ)) = (fun n => ((zeta n:ℕ):ℂ)) :=
    funext (fun _ => ArithmeticFunction.natCoe_apply)
  have hζ : LSeriesSummable (⇑(zeta : ArithmeticFunction ℂ)) s := by
    rw [he]
    exact LSeriesSummable_zeta_iff.mpr hs
  have hζ' : LSeries (⇑(zeta : ArithmeticFunction ℂ)) s = riemannZeta s := by
    rw [he]
    exact LSeries_zeta_eq_riemannZeta hs
  rw [←ArithmeticFunction.coe_mul,LSeries_convolution' hζ
    (charAF_LSeriesSummable χ hs),hζ',charAF_LSeries_eq χ hs]

theorem estermannFourCoeffs_summable {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) : LSeriesSummable (estermannFourCoeffs χ ψ) s :=
  ArithmeticFunction.LSeriesSummable_mul (χ.LSeriesSummable_zetaMul hs)
    (ArithmeticFunction.LSeriesSummable_mul (charAF_LSeriesSummable ψ hs)
      (charAF_LSeriesSummable (χ*ψ) hs))

theorem estermannFour_LSeries_eq {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    LSeries (estermannFourCoeffs χ ψ) s =
      riemannZeta s * (χ.LFunction s * ψ.LFunction s * (χ*ψ).LFunction s) := by
  unfold estermannFourCoeffs
  have hψ := charAF_LSeriesSummable ψ hs
  have hprod := charAF_LSeriesSummable (χ*ψ) hs
  rw [←ArithmeticFunction.coe_mul,LSeries_convolution' (χ.LSeriesSummable_zetaMul hs)
    (ArithmeticFunction.LSeriesSummable_mul hψ hprod),←ArithmeticFunction.coe_mul,
    LSeries_convolution' hψ hprod,estermannTwo_LSeries_eq χ hs,
    charAF_LSeries_eq ψ hs,charAF_LSeries_eq (χ*ψ) hs]
  ring

end FareyGoldbach
