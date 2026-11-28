import FareyGoldbach.ShortIntervalExceptions

/-! # Geometry of the frequency window and the modulus-one consequence -/

open Filter
open scoped Topology

namespace FareyGoldbach

/-- A centered interval of frequencies maps strictly inside the translated target
interval. The factor two in the upper bound on the center avoids rounding 3X/2. -/
theorem short_window_center {X Δ r b₁ b₂ : ℕ} (hr : 0<r) (hb₁ : b₁<r) (hb₂ : b₂<r)
    {M A : ℝ} (hA : 0<A) (hMA : 8*M≤A) (hΔ : 8*r≤Δ) (hΔX : Δ≤X) :
    ∃ k₀ : ℕ, X<r*k₀+b₁+b₂ ∧ 2*(r*k₀+b₁+b₂)≤3*X ∧
      ∀ m : ℕ, |(m:ℝ)-(k₀:ℝ)| ≤ M/(A*(r:ℝ)/(Δ:ℝ)) →
        r*m+b₁+b₂ ∈ Finset.Ioc X (X+Δ) := by
  let t := X+Δ/2-(b₁+b₂)
  let k₀ := t/r
  let n₀ := r*k₀+b₁+b₂
  have hrec : r*k₀+t%r=t := Nat.div_add_mod t r
  have hrem := Nat.mod_lt t hr
  have hts : t+b₁+b₂ = X+Δ/2 := by dsimp [t]; omega
  have hlo : 2*X+Δ ≤ 2*(n₀+r) := by dsimp only [n₀]; omega
  have hhi : 2*n₀ ≤ 2*X+Δ := by dsimp only [n₀]; omega
  refine ⟨k₀,by change X<n₀; omega,by change 2*n₀≤3*X; omega,?_⟩
  intro m hm
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hd : (0:ℝ)<Δ := Nat.cast_pos.mpr (by omega)
  have hscale : (r:ℝ)*(M/(A*(r:ℝ)/(Δ:ℝ))) ≤ (Δ:ℝ)/8 := by
    calc _ = (Δ:ℝ)*(M/A) := by field_simp
         _ ≤ (Δ:ℝ)*(1/8) := mul_le_mul_of_nonneg_left ((div_le_iff₀ hA).2 (by linarith)) hd.le
         _ = _ := by ring
  obtain ⟨hleft,hright⟩ := abs_le.mp hm
  have hl := mul_le_mul_of_nonneg_left hleft hr'.le
  have hh := mul_le_mul_of_nonneg_left hright hr'.le
  have hlo' : 2*(X:ℝ)+(Δ:ℝ) ≤ 2*((r:ℝ)*(k₀:ℝ)+(b₁:ℝ)+(b₂:ℝ)+(r:ℝ)) := by exact_mod_cast hlo
  have hhi' : 2*((r:ℝ)*(k₀:ℝ)+(b₁:ℝ)+(b₂:ℝ)) ≤ 2*(X:ℝ)+(Δ:ℝ) := by exact_mod_cast hhi
  have hgap : 8*(r:ℝ) ≤ (Δ:ℝ) := by exact_mod_cast hΔ
  apply Finset.mem_Ioc.mpr
  constructor
  · exact_mod_cast (show (X:ℝ)<(r:ℝ)*(m:ℝ)+(b₁:ℝ)+(b₂:ℝ) by nlinarith only [hl,hscale,hlo',hgap,hd])
  · exact_mod_cast (show (r:ℝ)*(m:ℝ)+(b₁:ℝ)+(b₂:ℝ)≤(X:ℝ)+(Δ:ℝ) by nlinarith only [hh,hscale,hhi',hd])

/-- On the chosen scale the continuous character estimate is available. -/
theorem short_window_bandwidth {X Δ r : ℕ} (hr : 0<r) (hΔ : 0<Δ) (hΔX : Δ≤X)
    {A : ℝ} (hA : 1≤A) (hwide : 2*A*(r:ℝ)≤Δ) :
    (r:ℝ)/(2*(X:ℝ)) ≤ A*(r:ℝ)/(Δ:ℝ) ∧ A*(r:ℝ)/(Δ:ℝ) ≤ 1/2 := by
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hd : (0:ℝ)<Δ := Nat.cast_pos.mpr hΔ
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr (hΔ.trans_le hΔX)
  constructor
  · apply (div_le_div_iff₀ (by positivity) hd).2
    have h := mul_le_mul_of_nonneg_right hA hr'.le
    have hh := mul_le_mul h (show (Δ:ℝ) ≤ 2*(X:ℝ) by linarith [Nat.cast_le (α:=ℝ).mpr hΔX]) hd.le (by positivity)
    simpa only [one_mul] using hh
  · apply (div_le_iff₀ hd).2
    linarith

/-- Existence for prescribed classes in natural-number windows. -/
def ShortFixedPairExistsBound : Prop :=
  ∃ c₀ : ℝ, 0<c₀ ∧ ∃ C₀ : ℝ, 0<C₀ ∧ ∀ (P : Progressions) {X Δ : ℕ}, 2≤X →
    C₀*(P.r.totient:ℝ)^2*Real.log (2*(X:ℝ))^2 ≤ (Δ:ℝ) → (Δ:ℝ) ≤ c₀*(X:ℝ) →
    ∃ n ∈ Finset.Ioc X (X+Δ), Even n ∧ (primeRepresentations P n).Nonempty

private theorem tendsto_log_two_sq_div :
    Tendsto (fun X : ℕ => Real.log (2*(X:ℝ))^2/(X:ℝ)) atTop (𝓝 0) := by
  have harg : Tendsto (fun X : ℕ => 2*(X:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ)<2)
  have hh := (Real.tendsto_pow_log_div_mul_add_atTop (1/2) 0 2 (by norm_num)).comp harg
  simpa only [Function.comp_def,add_zero,show ∀ t:ℝ,1/2*(2*t)=t by intro t; ring] using hh

/-- The actual target endpoint is real-valued. Rounding the construction up adds
at most one, which can be absorbed in the constant multiplying the logarithm. -/
theorem shortGoldbachLogSquared_of_fixedPairExists (bound : ShortFixedPairExistsBound) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ X : ℕ in atTop, ∃ n : ℕ, X<n ∧ (n:ℝ)≤(X:ℝ)+C*Real.log (2*(X:ℝ))^2 ∧
      Even n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n := by
  obtain ⟨c,hc,C,hC,hbound⟩ := bound
  let P : Progressions := ⟨1,by decide,0,0,by decide,by decide,by decide,by decide⟩
  refine ⟨C+1,by linarith,?_⟩
  have hsmall := (tendsto_log_two_sq_div.const_mul (C+1)).eventually_lt_const (show (C+1)*0<c by simpa using hc)
  filter_upwards [hsmall,eventually_ge_atTop (2:ℕ)] with X hsmall hX
  let L := Real.log (2*(X:ℝ))
  let Δ := ⌈C*L^2⌉₊
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have hL : 1≤L := one_le_log_two_mul hX
  have hs : 1≤L^2 := one_le_pow₀ hL
  have hd : C*L^2≤(Δ:ℝ) := Nat.le_ceil _
  have hceil := (Nat.ceil_lt_add_one (show 0≤C*L^2 by positivity)).le
  have hdu : (Δ:ℝ)≤(C+1)*L^2 := by
    change ((⌈C*L^2⌉₊:ℕ):ℝ)≤(C+1)*L^2
    linarith only [hceil,hs]
  change (C+1)*(L^2/(X:ℝ))<c at hsmall
  rw [←mul_div_assoc,div_lt_iff₀ hx] at hsmall
  have hd' : C*(P.r.totient:ℝ)^2*L^2 ≤ (Δ:ℝ) := by
    simpa only [P,Nat.totient_one,Nat.cast_one,one_pow,mul_one] using hd
  obtain ⟨n,hn,he,⟨⟨p,q⟩,hpq⟩⟩ := hbound P hX hd' (hdu.trans hsmall.le)
  obtain ⟨hl,hu⟩ := Finset.mem_Ioc.mp hn
  have hupper : (n:ℝ)≤(X:ℝ)+(Δ:ℝ) := by exact_mod_cast hu
  have hpr := (Finset.mem_filter.mp hpq).2
  exact ⟨n,hl,hupper.trans (add_le_add (le_refl _) hdu),he,p,q,hpr.1,hpr.2.1,hpr.2.2.1⟩

end FareyGoldbach
