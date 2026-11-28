import FareyGoldbach.C1WindowGeometry
import FareyGoldbach.TriangleProductComparison
import FareyGoldbach.TriangleFrequencyTail
import FareyGoldbach.LocalTwistedMeanSquareOfGRH

/-! # An even Goldbach number in every sufficiently long short window

The proof uses the triangular average on one arc around zero. Uniform bounds
for its translates control the part of the average outside the target interval.
-/

open Filter MeasureTheory
open scoped Topology Classical

namespace FareyGoldbach

private theorem modulus_le_totient_sq {r : ℕ} (hr : 0<r) :
    (r:ℝ)≤32*(r.totient:ℝ)^2 := by
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hp : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hs := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (show 0<2*(r:ℝ) by positivity))
  rw [Real.log_sqrt (by positivity : 0≤2*(r:ℝ))] at hs
  have hκ := div_totient_le_two_log hr
  have hκbound : (r:ℝ)/r.totient≤4*Real.sqrt (2*(r:ℝ)) := by linarith only [hs,hκ]
  have hsquare := pow_le_pow_left₀ (by positivity : 0≤ (r:ℝ)/r.totient) hκbound 2
  rw [div_pow,div_le_iff₀ (sq_pos_of_pos hp),mul_pow,Real.sq_sqrt (by positivity)] at hsquare
  apply (le_of_mul_le_mul_left ?_ hr')
  nlinarith only [hsquare]

private theorem log_four_le_twice {X : ℕ} (hX : 2≤X) :
    Real.log (2*((2*X:ℕ):ℝ)) ≤ 2*Real.log (2*(X:ℝ)) := by
  have hX' : (1:ℝ)≤X := Nat.one_le_cast.mpr (by omega)
  have hpositive : 0<2*(X:ℝ) := by positivity
  have hlog : Real.log (2:ℝ)≤Real.log (2*(X:ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith only [hX'])
  push_cast
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hpositive.ne']
  linarith only [hlog]

private theorem triangle_exists_core (P : Progressions) {Y k : ℕ}
    (hrY : P.r≤Y) (hY : 1≤Y) {η : ℝ} (hη : 0<η) (hηh : η≤1/2)
    (hnlo : Y≤2*(P.r*k+P.b₁+P.b₂)) (hnhi : P.r*k+P.b₁+P.b₂≤Y)
    (hlarge : (2:ℝ)^28≤((Y:ℝ)/P.r)*η)
    (herror : ∀ x : ℝ, ‖trianglePrimeCoefficient P Y η x -
        triangleModelCoefficient P.r P.b₁ P.b₂ Y η x‖ ≤
      (1/65536:ℝ)*η⁻¹*((P.r:ℝ)/P.r.totient)^2*((Y:ℝ)/P.r)) :
    ∃ m : ℕ, |(m:ℝ)-(k:ℝ)|≤(2:ℝ)^40/η ∧ 0<oddPrimeConvWeight P Y m := by
  let E := η⁻¹*((P.r:ℝ)/P.r.totient)^2*((Y:ℝ)/P.r)
  let s := Finset.range (2*(Y/P.r)+1)
  let a := oddPrimeConvWeight P Y
  let W := triangleFrequency η
  let M : ℕ := 2^40
  have hE : 0<E := by
    have hr := P.r_pos
    have hφ : (0:ℝ)<P.r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
    dsimp [E]; positivity
  have hident (x : ℝ) : (trianglePrimeCoefficient P Y η x).re =
      ∑ j ∈ s, a j*W ((j:ℝ)-x) := by rw [trianglePrimeCoefficient_eq_sum P Y hη x,Complex.ofReal_re]
  have hdiff (x : ℝ) : |(trianglePrimeCoefficient P Y η x).re -
      (triangleModelCoefficient P.r P.b₁ P.b₂ Y η x).re| ≤ (1/65536:ℝ)*E := by
    rw [←Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans ((herror x).trans_eq (by dsimp [E]; ring))
  have hlow := triangleModelCoefficient_re_lower P.r_pos hrY hY hη hηh hnlo hnhi hlarge
  have hpeak : (1/65536:ℝ)*E ≤ ∑ j ∈ s, a j*W ((j:ℝ)-(k:ℝ)) := by
    rw [←hident]
    have hb := (abs_le.mp (hdiff k)).1
    have hl : (1/32768:ℝ)*E≤(triangleModelCoefficient P.r P.b₁ P.b₂ Y η k).re :=
      (show (1/32768:ℝ)*E=(1/32768:ℝ)*η⁻¹*((P.r:ℝ)/P.r.totient)^2*((Y:ℝ)/P.r) by
        dsimp [E]; ring).le.trans hlow
    linarith only [hb,hl]
  have hconv (x : ℝ) : (∑ j ∈ s, a j*W ((j:ℝ)-x)) ≤ 4097*E := by
    rw [←hident]
    have hb := (abs_le.mp (hdiff x)).2
    have hn := triangleModelCoefficient_norm_le P.r_pos hrY hY hη hηh P.b₁ P.b₂ x
    have hm : (triangleModelCoefficient P.r P.b₁ P.b₂ Y η x).re ≤ 4096*E := calc
      _ ≤ _ := le_abs_self _
      _ ≤ _ := Complex.abs_re_le_norm _
      _ ≤ _ := hn.trans_eq (by dsimp [E]; ring)
    linarith only [hb,hm,hE]
  have htail := triangleFrequency_tail s a hη (fun j _ => oddPrimeConvWeight_nonneg P Y j)
    hconv M (by norm_num [M]) (k:ℝ)
  let t := s.filter (fun j : ℕ => (M:ℝ)/η≤|(j:ℝ)-(k:ℝ)|)
  change (∑ j ∈ t, a j*W ((j:ℝ)-(k:ℝ)))≤16*(4097*E)/(M:ℝ) at htail
  have hupper : (∑ j ∈ t, a j*W ((j:ℝ)-(k:ℝ))) ≤ (1/131072:ℝ)*E := by
    refine htail.trans ?_
    have hn : 16*(4097*E)/(M:ℝ) = (16*4097/(2:ℝ)^40)*E := by dsimp [M]; norm_num; ring
    rw [hn]
    exact mul_le_mul_of_nonneg_right (by norm_num) hE.le
  have hp : (∑ j ∈ t, a j*W ((j:ℝ)-(k:ℝ))) < (trianglePrimeCoefficient P Y η k).re := by
    rw [hident]
    linarith only [hpeak,hupper,hE]
  obtain ⟨m,hm,hpos⟩ := exists_oddPrimeConvWeight_pos_of_tail_lt P Y hη (k:ℝ) ((M:ℝ)/η) hp
  exact ⟨m,hm.le.trans_eq (by norm_num [M]),hpos⟩

private theorem triangle_scale_error {C A L d p r Y η : ℝ}
    (hC : 0<C) (hA : 0<A) (hd : 0<d) (hp : 0<p) (hr : 0<r)
    (hY : 0<Y) (hη : η=A*r/d) {L' : ℝ} (hL' : 0≤L') (hlog : L'≤2*L)
    (hbudget : (2:ℝ)^62*C*A*p^2*L^2≤d) :
    C*Y*η*(L')^2≤ (1/(2:ℝ)^60)*(r/p)^2*(Y/r) := by
  have hq := pow_le_pow_left₀ hL' hlog 2
  calc
    _ ≤ C*Y*η*(2*L)^2 := mul_le_mul_of_nonneg_left hq (by rw [hη]; positivity)
    _ = Y*r/( (2:ℝ)^60*p^2 ) * (((2:ℝ)^62*C*A*p^2*L^2)/d) := by rw [hη]; field_simp
    _ ≤ Y*r/((2:ℝ)^60*p^2)*1 := mul_le_mul_of_nonneg_left ((div_le_one hd).2 hbudget) (by positivity)
    _ = _ := by field_simp

/-- Given the uniform twisted mean square, every sufficiently long window
contains an even sum of primes in the prescribed two reduced classes. -/
theorem short_fixed_pair_exists_of_localTwistedMeanSquare (h : LocalTwistedMeanSquare) :
    ShortFixedPairExistsBound := by
  obtain ⟨C,hC,hremainder⟩ := oddPrimeWindow_remainder_l2 h
  let M : ℝ := (2:ℝ)^40
  let A := 8*M
  let C₀ := 64*A+(2:ℝ)^62*C*A
  have hM : 0<M := by dsimp [M]; positivity
  have hA : 1≤A := by norm_num [A,M]
  have hApos : 0<A := zero_lt_one.trans_le hA
  refine ⟨1,zero_lt_one,C₀,by dsimp [C₀]; positivity,?_⟩
  intro P X Δ hX hΔ hdX
  let Y := 2*X
  let η := A*(P.r:ℝ)/(Δ:ℝ)
  let p := (P.r.totient:ℝ)
  let L := Real.log (2*(X:ℝ))
  let L' := Real.log (2*(Y:ℝ))
  have hr : 0<P.r := P.r_pos
  have hr' : (0:ℝ)<P.r := Nat.cast_pos.mpr hr
  have hp : 0<p := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hL : 1≤L := one_le_log_two_mul hX
  have hDD : Δ≤X := by exact_mod_cast (show (Δ:ℝ)≤(X:ℝ) by simpa using hdX)
  have hcoef₁ : 64*A≤C₀ := le_add_of_nonneg_right (by positivity)
  have hcoef₂ : (2:ℝ)^62*C*A≤C₀ := le_add_of_nonneg_left (by positivity)
  have hwide : 2*A*(P.r:ℝ)≤(Δ:ℝ) := calc
    _ ≤ 64*A*p^2 := by
      have hm := mul_le_mul_of_nonneg_left (modulus_le_totient_sq hr) (show 0≤2*A by positivity)
      change _ ≤ _ at hm
      linarith only [hm]
    _ ≤ 64*A*p^2*L^2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL)
    _ ≤ _ := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef₁ (sq_nonneg p))
      (sq_nonneg L)).trans hΔ
  have hdpos : (0:ℝ)<Δ := (show (0:ℝ)<2*A*(P.r:ℝ) by positivity).trans_le hwide
  have hd8 : 8*P.r≤Δ := by
    have hAb : (8:ℝ)≤2*A := by norm_num [A,M]
    have hb := (mul_le_mul_of_nonneg_right hAb hr'.le).trans hwide
    exact_mod_cast hb
  have hY : 2≤Y := by dsimp [Y]; omega
  have hrY : P.r≤Y := by dsimp [Y]; omega
  obtain ⟨hηraw,hηh⟩ := short_window_bandwidth hr (Nat.cast_pos.mp hdpos) hDD hA hwide
  have hη : (P.r:ℝ)/Y≤η := by simpa [Y,η] using hηraw
  change η≤1/2 at hηh
  have hηpos : 0<η := (show 0<(P.r:ℝ)/Y by positivity).trans_le hη
  have hscale : (2:ℝ)^28≤((Y:ℝ)/P.r)*η := by
    have hAY : (2:ℝ)^28≤A := by norm_num [A,M]
    have hDY : (Δ:ℝ)≤Y := Nat.cast_le.mpr (by dsimp [Y]; omega)
    have hEq : ((Y:ℝ)/P.r)*η=A*((Y:ℝ)/(Δ:ℝ)) := by dsimp [η]; field_simp
    rw [hEq]
    exact hAY.trans (le_mul_of_one_le_right hApos.le ((one_le_div hdpos).2 hDY))
  obtain ⟨k,hklo,hkhi,hkin⟩ := short_window_center hr P.b₁_lt P.b₂_lt (M:=M) (A:=A) hApos (le_refl _) hd8 hDD
  have hlo : Y≤2*(P.r*k+P.b₁+P.b₂) := by dsimp [Y]; omega
  have hhi : P.r*k+P.b₁+P.b₂≤Y := by dsimp [Y]; omega
  have hremBudget : C*(Y:ℝ)*η*(L')^2 ≤ (1/(2:ℝ)^60)*((P.r:ℝ)/p)^2*((Y:ℝ)/P.r) :=
    triangle_scale_error hC hApos hdpos hp hr' (by positivity) rfl
      (zero_le_one.trans (one_le_log_two_mul hY)) (log_four_le_twice hX)
      ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef₂ (sq_nonneg p))
        (sq_nonneg L)).trans hΔ)
  have hR₁ := (hremainder hr hrY hY P.b₁_lt P.coprime₁ hη hηh).trans hremBudget
  have hR₂ := (hremainder hr hrY hY P.b₂_lt P.coprime₂ hη hηh).trans hremBudget
  have herror := triangle_prime_model_norm_sub_le P hrY (by omega) hηpos hηh hR₁ hR₂
  obtain ⟨m,hm,ha⟩ := triangle_exists_core P hrY (by omega) hηpos hηh hlo hhi hscale herror
  exact ⟨P.r*m+P.b₁+P.b₂,hkin m hm,even_and_rep_of_oddPrimeConvWeight_pos ha⟩

/-- The prescribed-class short-window existence theorem under Dirichlet GRH. -/
theorem short_fixed_pair_exists_of_dirichletGRH (h : DirichletGRH) : ShortFixedPairExistsBound :=
  short_fixed_pair_exists_of_localTwistedMeanSquare (localTwistedMeanSquare_of_dirichletGRH h)

/-- Under Dirichlet GRH, every sufficiently large starting point has an even
Goldbach number within a constant times the square of its logarithm. -/
theorem short_goldbach_exists_log_sq_of_dirichletGRH (h : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℕ, ∀ X≥X₀, ∃ n : ℕ, X<n ∧
      (n:ℝ)≤(X:ℝ)+C*Real.log (2*(X:ℝ))^2 ∧ Even n ∧
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n := by
  obtain ⟨C,hC,hX⟩ := shortGoldbachLogSquared_of_fixedPairExists (short_fixed_pair_exists_of_dirichletGRH h)
  exact ⟨C,hC,eventually_atTop.mp hX⟩

end FareyGoldbach
