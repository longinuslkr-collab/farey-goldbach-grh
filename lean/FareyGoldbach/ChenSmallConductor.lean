import FareyGoldbach.SharpPrimeCount

/-! # Small-conductor prime twists for the switching sequence -/

open scoped Classical

namespace FareyGoldbach

/-- The prime-twist input used on the small conductors in the switched sum.
It is stated separately from the large sieve and from the PNT. -/
def SmallConductorPrimeTwists : Prop :=
  ∀ A B : ℕ, ∃ C : ℝ, 0<C ∧ ∀ (X q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → 1<q → 2≤X → (q:ℝ)≤(Real.log (X:ℝ))^A →
      ‖∑ p ∈ X.primesLE, χ (p:ZMod q)‖ ≤ C*(X:ℝ)/(Real.log (X:ℝ))^B

theorem log_pow_le_sqrt (b : ℕ) {x : ℝ} (hx : 1≤x) :
    Real.log x^b ≤ (2:ℝ)^b*(b.factorial:ℝ)*Real.sqrt x := by
  have hx₀ : 0<x := zero_lt_one.trans_le hx
  have hL := Real.log_nonneg hx
  have hb : 0<(b.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos b)
  have hsq : Real.exp (Real.log x/2) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx₀]
    congr 1
    ring
  have h := (div_le_iff₀ hb).mp
    (Real.pow_div_factorial_le_exp (Real.log x/2) (show 0≤Real.log x/2 by positivity) b)
  rw [hsq,div_pow] at h
  have h₂ : 0<(2:ℝ)^b := by positivity
  calc Real.log x^b ≤ ((Real.sqrt x)*(b.factorial:ℝ))*2^b := (div_le_iff₀ h₂).mp h
    _ = _ := by ring

/-- GRH implies uniform log-power savings at every fixed log-power conductor
range. This instantiates the input without changing the switching proof. -/
theorem smallConductorPrimeTwists_of_dirichletGRH : DirichletGRH → SmallConductorPrimeTwists := by
  intro hGRH A B
  obtain ⟨C,hC,hsharp⟩ := nonprincipal_prime_twist_of_dirichletGRH hGRH
  let c := C*((A:ℝ)+2)^2*((2:ℝ)^(B+2)*((B+2).factorial:ℝ))
  refine ⟨c,by dsimp [c]; positivity,?_⟩
  intro X q _ χ hprim hq hX hcond
  have hχ : χ≠1 := fun h => by
    have hq₁ : q=1 := eq_one_of_isPrimitive_of_eq_one hprim h
    omega
  have hXr : (2:ℝ)≤X := Nat.cast_le.mpr hX
  have hXp : (0:ℝ)<X := by linarith
  have hq₀ : (0:ℝ)<q := Nat.cast_pos.mpr (by omega)
  have hl : 0<Real.log (X:ℝ) := Real.log_pos (by linarith)
  have hlX : Real.log (X:ℝ)≤X := le_trans (Real.log_le_sub_one_of_pos hXp) (sub_le_self _ zero_le_one)
  have hqX : (q:ℝ)≤(X:ℝ)^A := hcond.trans (pow_le_pow_left₀ hl.le hlX _)
  have hXprod : 2*(q:ℝ)*(X:ℝ)≤(X:ℝ)^(A+2) := by
    calc _ ≤ (X:ℝ)*((X:ℝ)^A)*(X:ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hXr hqX hq₀.le hXp.le) hXp.le
      _ = _ := by rw [pow_add]; ring
  have hlog : Real.log (2*(q:ℝ)*(X:ℝ))≤((A:ℝ)+2)*Real.log (X:ℝ) := by
    have hh := Real.log_le_log (by positivity : 0<2*(q:ℝ)*(X:ℝ)) hXprod
    simpa only [Real.log_pow,Nat.cast_add,Nat.cast_ofNat] using hh
  have hlog₀ : 0≤Real.log (2*(q:ℝ)*(X:ℝ)) := Real.log_nonneg (by
    have hq₁ : (1:ℝ)≤q := Nat.one_le_cast.mpr (by omega)
    nlinarith only [hq₁,hXr,mul_nonneg (sub_nonneg.mpr hq₁) (sub_nonneg.mpr hXr)])
  let L := Real.log (X:ℝ)
  have hB : 0<L^B := by dsimp [L]; positivity
  apply (le_div_iff₀ hB).mpr
  calc ‖∑ p∈X.primesLE, χ (p:ZMod q)‖ * L^B ≤
      (C*Real.sqrt X*(((A:ℝ)+2)*L)^2)*L^B := by
          apply mul_le_mul_of_nonneg_right _ hB.le
          exact (hsharp X q χ hχ hX).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog₀ hlog 2) (by positivity))
    _ = (C*((A:ℝ)+2)^2*Real.sqrt X)*L^(B+2) := by rw [pow_add]; ring
    _ ≤ (C*((A:ℝ)+2)^2*Real.sqrt X)*((2:ℝ)^(B+2)*((B+2).factorial:ℝ)*Real.sqrt X) :=
      mul_le_mul_of_nonneg_left (log_pow_le_sqrt _ (by linarith)) (by positivity)
    _ = c*(X:ℝ) := by
      dsimp only [c]
      calc _ = (C*((A:ℝ)+2)^2*((2:ℝ)^(B+2)*((B+2).factorial:ℝ)))*(Real.sqrt X)^2 := by ring
        _ = _ := by rw [Real.sq_sqrt hXp.le]

end FareyGoldbach
