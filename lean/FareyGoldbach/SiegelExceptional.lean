import FareyGoldbach.SiegelFinite
import FareyGoldbach.SiegelInduction

/-! # Siegel's comparison with a fixed real zero -/

namespace FareyGoldbach

private theorem siegel_log_cube_le {η X : ℝ} (hη : 0<η) (hX : 1≤X) :
    Real.log X^3 ≤ (6/η^3)*X^η := by
  have hp := zero_lt_one.trans_le hX
  have h := Real.pow_div_factorial_le_exp (η*Real.log X) (mul_nonneg hη.le (Real.log_nonneg hX)) 3
  rw [mul_comm,←Real.rpow_def_of_pos hp] at h
  norm_num at h
  calc Real.log X^3 ≤ (6*X^η)/η^3 :=
        (le_div_iff₀ (pow_pos hη 3)).mpr (by nlinarith only [h])
    _ = _ := by ring

private theorem siegel_absorb_log_cube {X ε α d v : ℝ} (hε : 0<ε) (hX : 1≤X)
    (hα : α≤ε/2) (hd : 0≤d) (hv : 0≤v)
    (h : d*X^(-α) ≤ 512*Real.log X^3*v) :
    d/(512*(6/(ε/2)^3))*X^(-ε) ≤ v := by
  let η := ε/2
  let K := 6/η^3
  have hη : 0<η := by dsimp [η]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  have hp := zero_lt_one.trans_le hX
  have hA : d*X^(-η)≤512*K*X^η*v := by
    apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX (neg_le_neg hα)) hd).trans
    apply h.trans
    calc 512*Real.log X^3*v ≤ 512*(K*X^η)*v := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (siegel_log_cube_le hη hX) (by norm_num)) hv
      _ = _ := by ring
  have hpow : X^(-ε)*X^η=X^(-η) := by
    rw [←Real.rpow_add hp]
    congr 1
    dsimp only [η]
    ring
  change d/(512*K)*X^(-ε)≤v
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0<512*K*X^η)).mp
  calc _ = d*(X^(-ε)*X^η) := by field_simp [hK.ne']
    _ ≤ _ := by rw [hpow]; simpa only [mul_comm v] using hA

/-- A fixed quadratic character with a real zero controls every higher
conductor through the four-factor residue. The lower conductors form a finite set. -/
theorem siegel_lower_of_reference_zero {ε C β : ℝ} (hε : 0<ε) (hβ : 7/8≤β)
    (hβ' : β<1) (hsmall : C*(1-β)≤ε/2)
    {q₁ : ℕ} [NeZero q₁] {χ₁ : DirichletCharacter ℂ q₁}
    (hprim₁ : χ₁.IsPrimitive) (hq₁ : 1<q₁) (hquad₁ : χ₁^2=1)
    (hzero : χ₁.LFunction (β:ℂ)=0)
    (hFour : ∀ (q : ℕ) [NeZero q] (χ ψ : DirichletCharacter ℂ q),
      χ≠1 → ψ≠1 → χ*ψ≠1 → χ^2=1 → ψ^2=1 →
      ∀ x : ℝ, 7/8≤x → x<1 → χ.LFunction (x:ℂ)=0 →
        (1-x)/2*(2*(q:ℝ))^(-(C*(1-x))) ≤
        ‖χ.LFunction 1‖*‖ψ.LFunction 1‖*‖(χ*ψ).LFunction 1‖) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 1<q → χ^2=1 → c*(q:ℝ)^(-ε)≤‖χ.LFunction 1‖ := by
  obtain ⟨c₀,hc₀,hfin⟩ := siegel_small_moduli_L_one_lower q₁
  let d := (1-β)/2
  let c₁ := d/(512*(6/(ε/2)^3))*(2*(q₁:ℝ))^(-ε)
  have hd : 0<d := by dsimp only [d]; linarith only [hβ']
  have hc₁ : 0<c₁ := by dsimp only [c₁]; positivity
  refine ⟨min c₀ c₁,lt_min hc₀ hc₁,?_⟩
  intro q _ χ hprim hq hquad
  have hqR : (1:ℝ)≤q := Nat.one_le_cast.mpr hq.le
  have hqP := zero_lt_one.trans_le hqR
  have hχ : χ≠1 := fun h => (Nat.ne_of_gt hq) (eq_one_of_isPrimitive_of_eq_one hprim h)
  by_cases hlo : q≤q₁
  · calc _ ≤ c₀*(q:ℝ)^(-ε) := mul_le_mul_of_nonneg_right (min_le_left ..) (by positivity)
      _ ≤ c₀ := mul_le_of_le_one_right hc₀.le (Real.rpow_le_one_of_one_le_of_nonpos hqR (neg_nonpos.mpr hε.le))
      _ ≤ _ := hfin q χ hlo hχ
  have hgt := lt_of_not_ge hlo
  let Q := q₁*q
  let d₁ : q₁∣Q := Nat.dvd_mul_right q₁ q
  let d₂ : q∣Q := Nat.dvd_mul_left q q₁
  let ξ₁ := χ₁.changeLevel d₁
  let ξ₂ := χ.changeLevel d₂
  let X := 2*(Q:ℝ)
  let L := Real.log X
  have hQ : 1<Q := hq₁.trans_le (Nat.le_mul_of_pos_right q₁ (NeZero.pos q))
  have hQR : (1:ℝ)≤Q := Nat.one_le_cast.mpr hQ.le
  have hX : 1≤X := by dsimp [X]; linarith only [hQR]
  have hL : 0≤L := Real.log_nonneg hX
  have hχ₁ : χ₁≠1 := fun h => (Nat.ne_of_gt hq₁) (eq_one_of_isPrimitive_of_eq_one hprim₁ h)
  obtain ⟨hn₁,hn₂,he₁,he₂,hnprod,_⟩ := siegel_lifted_pair d₁ d₂ χ₁ χ hprim₁ hprim hq₁ hgt hquad₁ hquad
  have hz : ξ₁.LFunction (β:ℂ)=0 := by
    rw [show ξ₁=χ₁.changeLevel d₁ from rfl,DirichletCharacter.LFunction_changeLevel d₁ χ₁ (Or.inl hχ₁),hzero,zero_mul]
  have hres := hFour Q ξ₁ ξ₂ hn₁ hn₂ hnprod he₁ he₂ β hβ hβ' hz
  have h0 (φ : DirichletCharacter ℂ Q) (hn : φ≠1) : ‖φ.LFunction 1‖≤16*L :=
    siegel_L_on_closedBall_le_of_ne_one φ hn hQ (Metric.mem_closedBall_self (by positivity))
  have he : ‖ξ₂.LFunction 1‖≤2*L*‖χ.LFunction 1‖ := norm_LFunction_one_changeLevel_le d₂ χ hχ
  have hupper : d*X^(-(C*(1-β)))≤512*L^3*‖χ.LFunction 1‖ := by
    apply hres.trans
    calc _ ≤ (16*L)*(2*L*‖χ.LFunction 1‖)*(16*L) :=
          mul_le_mul (mul_le_mul (h0 ξ₁ hn₁) he (norm_nonneg _) (by positivity))
            (h0 (ξ₁*ξ₂) hnprod) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hmain := siegel_absorb_log_cube hε hX hsmall hd.le (norm_nonneg _) hupper
  apply (mul_le_mul_of_nonneg_right (min_le_right c₀ c₁) (by positivity : 0≤(q:ℝ)^(-ε))).trans
  calc _ = (d/(512*(6/(ε/2)^3)))*X^(-ε) := by
          change _ = _*(2*((q₁*q:ℕ):ℝ))^(-ε)
          rw [Nat.cast_mul,←mul_assoc,Real.mul_rpow (by positivity) hqP.le]
          dsimp only [c₁]
          ring
    _ ≤ _ := hmain

end FareyGoldbach
