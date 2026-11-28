import FareyGoldbach.ChenQuarterRosser
import FareyGoldbach.ChenQuarterDistribution
import FareyGoldbach.ChenQuarterMass41
import FareyGoldbach.ChenQuarterTripleMass

/-! # The rational margin and count assembly for quarter-power switching -/

open Filter
open scoped Topology

namespace FareyGoldbach

private theorem chen_quarter_positive_margin :
    (1:ℝ)/250 < chenQuarterLowerCoeff (4999/10000) (4/25) -
      (1/2)*chenQuarterMediumCoeff (4999/10000) (4/25) -
      (2/(4999/10000)) * ((149/1000) + (1/2)*(441/1000) + (1/2)*(3/250)) := by
  let d : ℝ := 4999/10000
  let a : ℝ := 4/25
  let x : ℝ := d/a-1
  let t : ℝ := (1/4)/(d-1/4)
  let R : ℝ := x/t
  have hx : 0<x := by norm_num [x,d,a]
  have ht : 0<t := by norm_num [t,d]
  have hR : 0<R := div_pos hx ht
  have hm : ((1/4:ℝ)/(d-1/4))/(a/(d-a)) = x*t := by norm_num [x,t,d,a]
  have hr : 2*Real.log x - Real.log (x*t) = Real.log R := by
    dsimp [R]
    rw [Real.log_mul hx.ne' ht.ne',Real.log_div hx.ne' ht.ne']
    ring
  have h₀ : 0≤R/2-1 := by norm_num [R,x,t,d,a]
  have hl := chen_log_lower_six h₀
  rw [show 1+(R/2-1)=R/2 by ring,Real.log_div hR.ne' (by norm_num : (2:ℝ)≠0)] at hl
  have hb : (751:ℝ)/1000 + d/250 < Real.log R := by
    have ht₂ := Real.log_two_gt_d9
    norm_num [R,x,t,d,a] at hl ⊢
    linarith only [hl,ht₂]
  change 1/250 < chenQuarterLowerCoeff d a - (1/2)*chenQuarterMediumCoeff d a -
    (2/d)*((149/1000)+(1/2)*(441/1000)+(1/2)*(3/250))
  have heq : chenQuarterLowerCoeff d a - (1/2)*chenQuarterMediumCoeff d a -
      (2/d)*((149/1000)+(1/2)*(441/1000)+(1/2)*(3/250)) =
      (Real.log R - 751/1000)/d := by
    unfold chenQuarterLowerCoeff chenQuarterMediumCoeff
    rw [hm,←hr]
    change (2/d)*Real.log x - (1/2)*(2/d*Real.log (x*t)) - _ = _
    ring
  rw [heq]
  apply (lt_div_iff₀ (show 0<d by norm_num [d])).2
  linarith only [hb]

private noncomputable abbrev quarterB30 (N : ℕ) :=
  chenQuarterB30 N (chenPowerLevel (1/4) N)

private noncomputable abbrev quarterB31 (N : ℕ) :=
  chenQuarterB31 N (chenPowerLevel (4/25) N) (chenPowerLevel (1/4) N)

private noncomputable abbrev quarterB41 (N : ℕ) :=
  chenQuarterB41 N (chenPowerLevel (4/25) N) (chenPowerLevel (1/4) N)

private def QuarterMassBound (B : ℕ→Finset ℕ) (C : ℝ) : Prop :=
  ∀ e : ℝ, 0<e → ∀ᶠ N : ℕ in atTop, Even N →
    ((B N).card:ℝ) ≤ (C+e)*((N:ℝ)/Real.log (N:ℝ))

private def QuarterReducedBound (B : ℕ→Finset ℕ) : Prop :=
  ∀ e : ℝ, 0<e → ∀ᶠ N : ℕ in atTop, Even N →
    chenReducedError N (chenPowerLevel (4999/10000) N) (chenAPError (B N) (B N).card) ≤ e*chenLogScale N

private theorem chen_quarter_count_of_bounds
    (hM30 : QuarterMassBound quarterB30 (149/1000)) (hR30 : QuarterReducedBound quarterB30)
    (hM31 : QuarterMassBound quarterB31 (441/1000)) (hR31 : QuarterReducedBound quarterB31)
    (hM41 : QuarterMassBound quarterB41 (3/250)) (hR41 : QuarterReducedBound quarterB41) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (1:ℝ)/1000*(N:ℝ)/Real.log (N:ℝ)^2 ≤
        ((chenRoughRepresentations N (chenPowerLevel (4/25) N)).card:ℝ) := by
  let a : ℝ := 4/25
  let d : ℝ := 4999/10000
  let η : ℝ := 1/10000
  have hd₁ : 11/24<d := by norm_num [d]
  have hd₂ : d<1/2 := by norm_num [d]
  have he : 0<η := by norm_num [η]
  have ha₁ : 1/8≤a := by norm_num [a]
  have ha₂ : a<1/4 := by norm_num [a]
  have hP := chen_quarter_prime_sieve_terms hd₁ hd₂ ha₁ ha₂ (by norm_num [a,d]) (by norm_num [a,d]) he
  have h30 := chen_quarter_switched_sieve_bound hd₁ hd₂ (by norm_num) he quarterB30 hM30 hR30
  have h31 := chen_quarter_switched_sieve_bound hd₁ hd₂ (by norm_num) he quarterB31 hM31 hR31
  have h41 := chen_quarter_switched_sieve_bound hd₁ hd₂ (by norm_num) he quarterB41 hM41 hR41
  filter_upwards [hP,h30,h31,h41,chen_power_error_eventually_le η he,
    eventually_ge_atTop (2^24:ℕ)] with N hP h30 h31 h41 hE hN hEven
  have hU := chenCanonicalU_ge_half hEven (show 2≤N by omega)
  have hU₀ : 0≤chenCanonicalU N := by linarith
  let T := chenSieveScale chenCanonicalU N
  have hT : 0≤T := by dsimp [T,chenSieveScale]; positivity
  have hmargin := mul_le_mul_of_nonneg_right chen_quarter_positive_margin.le hT
  have hF := chen_quarter_switching_floor hN ha₁
  obtain ⟨hL,hM⟩ := hP hEven
  have hE' := hE chenCanonicalU hU
  have hcount : (1:ℝ)/500*T ≤ ((chenRoughRepresentations N (chenPowerLevel a N)).card:ℝ) := by
    change (1:ℝ)/250*T ≤ (chenQuarterLowerCoeff d a - (1/2)*chenQuarterMediumCoeff d a -
      (2/d)*((149/1000)+(1/2)*(441/1000)+(1/2)*(3/250)))*T at hmargin
    dsimp only [a,d,η,T,quarterB30,quarterB31,quarterB41] at hL hM h30 h31 h41 hE' hF hmargin hT ⊢
    linarith only [hL,hM,h30 hEven,h31 hEven,h41 hEven,hE',hF,hmargin,hT]
  refine le_trans ?_ hcount
  unfold T chenSieveScale
  rw [←mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  nlinarith only [mul_le_mul_of_nonneg_right hU (Nat.cast_nonneg (α:=ℝ) N)]

private theorem quarter_mass_weaken {B : ℕ→Finset ℕ} {C : ℝ}
    (hMass : ∀ᶠ N : ℕ in atTop, ((B N).card:ℝ) ≤ C*((N:ℝ)/Real.log (N:ℝ))) :
    QuarterMassBound B C := by
  intro e he
  filter_upwards [hMass,eventually_ge_atTop (2:ℕ)] with N hMass hN _
  have hL : 0≤Real.log (N:ℝ) := Real.log_nonneg
    (Nat.one_le_cast.mpr (by omega))
  exact hMass.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right he.le) (by positivity))

/-- Quantitative unconditional rough P₂ Goldbach with the floored exponent 4/25. -/
theorem chen_rough_four_twentyfifths_count_lower_unconditional :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      c*(N:ℝ)/Real.log (N:ℝ)^2 ≤
        ((chenRoughRepresentations N (chenPowerLevel (4/25) N)).card:ℝ) := by
  have hR (e : ℝ) (he : 0<e) :=
    chen_quarter_reduced_errors_unconditional (a:=4/25) (θ:=4999/10000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) e he
  refine ⟨1/1000,by norm_num,chen_quarter_count_of_bounds
    (quarter_mass_weaken chen_quarter_B30_mass) ?_
    (quarter_mass_weaken chen_quarter_B31_mass_four_twentyfifths) ?_
    (quarter_mass_weaken chen_quarter_B41_mass) ?_⟩
  · intro e he
    exact (hR e he).mono (fun _ h _ ↦ h.1)
  · intro e he
    exact (hR e he).mono (fun _ h _ ↦ h.2.1)
  · intro e he
    exact (hR e he).mono (fun _ h _ ↦ h.2.2)

/-- A nontrivial squarefree P₂ complement at the floored exponent 4/25. -/
theorem chen_rough_four_twentyfifths_theorem_unconditional :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ 1<m ∧ Squarefree m ∧ m.Coprime N ∧
        IsRough (chenPowerLevel (4/25) N) m ∧ p+m=N := by
  obtain ⟨c,hc,hcount⟩ := chen_rough_four_twentyfifths_count_lower_unconditional
  filter_upwards [hcount,eventually_ge_atTop (2:ℕ)] with N hcount hN he
  have hL : 0<Real.log (N:ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hN)
  have hN₀ : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hpos : 0<c*(N:ℝ)/Real.log (N:ℝ)^2 := by positivity
  obtain ⟨m,hm⟩ := Finset.card_pos.mp (Nat.cast_pos.mp (hpos.trans_le (hcount he)))
  obtain ⟨p,hp⟩ := mem_chenRoughRepresentations_iff.mp hm
  exact ⟨p,m,hp⟩

/-- A real-power rough P₂ representation at every fixed exponent below 4/25. -/
theorem chen_rough_four_twentyfifths_rpow_theorem_unconditional {θ : ℝ} (hθ : θ<4/25) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ 1<m ∧ Squarefree m ∧ m.Coprime N ∧
        (∀ q∈m.primeFactors, (N:ℝ)^θ≤(q:ℝ)) ∧ p+m=N := by
  have hcut := eventually_rpow_add_one_le_powerLevel (le_max_right θ 0)
    (max_lt hθ (by norm_num : (0:ℝ)<4/25))
  filter_upwards [chen_rough_four_twentyfifths_theorem_unconditional, hcut,
    eventually_ge_atTop (1:ℕ)] with N hrep hcut hN he
  obtain ⟨p,m,hp,hP,hm,hsq,hcop,hr,heq⟩ := hrep he
  refine ⟨p,m,hp,hP,hm,hsq,hcop,?_,heq⟩
  intro q hq
  calc
    (N:ℝ)^θ ≤ (N:ℝ)^(max θ 0) :=
      Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hN) (le_max_left θ 0)
    _ ≤ (N:ℝ)^(max θ 0)+1 := le_add_of_nonneg_right zero_le_one
    _ ≤ (chenPowerLevel (4/25) N:ℝ) := hcut
    _ ≤ (q:ℝ) := Nat.cast_le.mpr (hr q hq)

end FareyGoldbach
