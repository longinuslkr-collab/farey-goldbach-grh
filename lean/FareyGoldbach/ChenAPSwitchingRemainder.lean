import FareyGoldbach.ChenAPSwitchingMass
import FareyGoldbach.ChenAPSwitchingCharacters
import FareyGoldbach.ChenAPSwitchingBoxBounds
import FareyGoldbach.ChenAPSwitchingBudgets
import FareyGoldbach.ChenSwitchingAsymptotics

/-! # Uniform distribution for the switched sequence under GRH -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

theorem chen_ap_pair_box_weights_le {N r D : ℕ} (hN : 1≤N) (hr : 0<r) (hD : D≤N)
    (P : Finset (ℕ×ℕ)) (F : ∀ q : ℕ, ℕ → ℕ → DirichletCharacter ℂ q → ℂ)
    (hdecomp : ∀ q k (χ : DirichletCharacter ℂ q),
      (∑ x∈P,chenMaskedChar χ k x.1*chenMaskedChar χ k x.2) =
        ∑ i∈Finset.range (N.log2+1),F q i k χ)
    {J : ℕ→ℝ} (hJ : ∀ a∈r.divisors, 0≤J a)
    (hbox : ∀ a∈r.divisors, ∀ k∈Finset.Ico 1 D, ∀ i∈Finset.range (N.log2+1),
      (∑ q∈(Finset.Ico 2 D).filter (fun q => a.Coprime q),
        chenPrimitiveNorm (a*q) (F (a*q) i
          ((r/a)*k))/(q:ℝ))≤J a) :
    (∑ a∈r.divisors, ∑ k∈Finset.Ico 1 D, (1/(k.totient:ℝ))*
      ∑ q∈(Finset.Ico 2 D).filter (fun q => a.Coprime q),
        chenMaskedPrimitiveMass P
          (a*q) ((r/a)*k)/(q.totient:ℝ))≤
        6*(chenSwitchLog N)^3*∑ a∈r.divisors,J a := by
  let I := Finset.range (N.log2+1)
  let S := Finset.Ico 1 D
  let L := chenSwitchLog N
  have hL : 0≤L := zero_le_one.trans (one_le_chenSwitchLog hN)
  have hS : S⊆Finset.Icc 1 N := fun k hk =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hk).1,(Finset.mem_Ico.mp hk).2.le.trans hD⟩
  have hw : (∑ k∈S,1/(k.totient:ℝ))≤2*L^2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)).trans
      (chen_sum_inv_totient_le hN)
  have hrow (a : ℕ) (ha : a∈r.divisors) (k : ℕ) (hk : k∈S) :
      (∑ q∈(Finset.Ico 2 D).filter (fun q => a.Coprime q),
        chenMaskedPrimitiveMass P (a*q) ((r/a)*k)/(q.totient:ℝ))≤
          3*L*J a := by
    let Q := (Finset.Ico 2 D).filter (fun q => a.Coprime q)
    have hap : 0<a := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 hr
    calc
      _ ≤ ∑ q∈Q,∑ i∈I,chenPrimitiveNorm (a*q)
          (F (a*q) i ((r/a)*k))/(q:ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        obtain ⟨hq',hc⟩ := Finset.mem_filter.mp hq
        exact chen_ap_masked_mass_le_of_sum_boxes hap (by have := (Finset.mem_Ico.mp hq').1; omega)
          hc P ((r/a)*k) I (fun i => F (a*q) i ((r/a)*k)) (hdecomp (a*q) ((r/a)*k))
      _ ≤ ∑ _i∈I,J a := by
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum fun i hi => hbox a ha k hk i hi
      _ ≤ _ := by
        rw [Finset.sum_const,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (chen_log2_range_card_le hN) (hJ a ha)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hJa := hJ a ha
  calc
    _ ≤ ∑ k∈S,(1/(k.totient:ℝ))*(3*L*J a) := by
      exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hrow a ha k hk) (by positivity)
    _ ≤ (2*L^2)*(3*L*J a) := by
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hw (by positivity)
    _ = _ := by dsimp only [L]; ring

/-- The numerical conductor budget is independent of the switched carrier. -/
theorem chen_ap_remainder_finite_bound {δ θ C E : ℝ}
    (hθ : 0<θ) (hsum : δ+θ<1/2) (hC : 0≤C)
    {N r z : ℕ} (hN : 1≤N) (hr : 0<r) (hrpow : (r:ℝ)≤(N:ℝ)^δ)
    (hz : (N:ℝ)^(1/16:ℝ)+1≤(z:ℝ))
    (hbase : (r.totient:ℝ)*E ≤
      (r.totient:ℝ)*(4*(chenSwitchLog N)^3*((N:ℝ)/z)) +
      6*(chenSwitchLog N)^3*∑ a∈r.divisors,
        chenAPBoxBudget N a (chenPowerLevel θ N) (chenAPConductorCut N r)
          (C*(N:ℝ)^(7/8:ℝ)*(chenSwitchLog N)^2)) :
    let β := max (δ+15/16) (max (2*δ+7/8) (δ+θ+1/2))
    (r.totient:ℝ)*E ≤
      (4+6*(2*C+200000))*((N:ℝ)/(chenSwitchLog N)^4+(N:ℝ)^β*(chenSwitchLog N)^20) := by
  let D := chenPowerLevel θ N
  let L := chenSwitchLog N
  let β := max (δ+15/16) (max (2*δ+7/8) (δ+θ+1/2))
  let H := (N:ℝ)^β
  have hn : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
  have hp : (0:ℝ)<N := zero_lt_one.trans_le hn
  have hL := one_le_chenSwitchLog hN
  have hDpow : (D:ℝ)≤(N:ℝ)^θ := Nat.floor_le (by positivity)
  have hrN : r≤N := Nat.cast_le.mp (hrpow.trans
    (by simpa using Real.rpow_le_rpow_of_exponent_le hn (show δ≤1 by linarith only [hθ,hsum])))

  have hsmall : (r:ℝ)^2*(N:ℝ)^(7/8:ℝ)≤H := by
    calc
      _ ≤ ((N:ℝ)^δ)^2*(N:ℝ)^(7/8:ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hrpow _) (by positivity)
      _ = (N:ℝ)^(2*δ+7/8) := by
        rw [sq,←Real.rpow_add hp,←Real.rpow_add hp,show δ+δ=2*δ by ring]
      _ ≤ H := Real.rpow_le_rpow_of_exponent_le hn
        ((le_max_left _ _).trans (le_max_right (δ+15/16) _))
  have hlarge : (r:ℝ)*(D:ℝ)*Real.sqrt N≤H := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ ≤ (N:ℝ)^δ*(N:ℝ)^θ*(N:ℝ)^(1/2:ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hrpow hDpow (Nat.cast_nonneg _) (by positivity)) (by positivity)
      _ = (N:ℝ)^(δ+θ+1/2) := by rw [Real.rpow_add hp, Real.rpow_add hp δ θ]
      _ ≤ H := Real.rpow_le_rpow_of_exponent_le hn
        ((le_max_right _ _).trans (le_max_right (δ+15/16) _))
  have hprincipal : (r.totient:ℝ)*((N:ℝ)/(z:ℝ))≤H := by
    have hz' : (N:ℝ)^(1/16:ℝ)≤z := by linarith only [hz]
    calc
      _ ≤ (N:ℝ)^δ*((N:ℝ)/(N:ℝ)^(1/16:ℝ)) :=
        mul_le_mul ((Nat.cast_le.mpr (Nat.totient_le r)).trans hrpow)
          (div_le_div_of_nonneg_left hp.le (by positivity) hz') (by positivity) (by positivity)
      _ = (N:ℝ)^(δ+15/16) := by
        rw [show (15/16:ℝ)=1-1/16 by norm_num,Real.rpow_add hp,Real.rpow_sub hp,Real.rpow_one]
      _ ≤ H := Real.rpow_le_rpow_of_exponent_le hn (le_max_left ..)
  have hH : 0≤H := by dsimp only [H]; positivity
  have hBgt := chen_ap_sum_box_budget hN hr hrN hC hH hsmall hlarge
  have hpc : (r.totient:ℝ)*(4*L^3*((N:ℝ)/z))≤4*L^3*H := by
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left hprincipal (by positivity)
  have ht := hbase.trans (add_le_add hpc (mul_le_mul_of_nonneg_left hBgt (by positivity)))
  exact ht.trans (chenSwitchTotal_budget_absorb hL hp.le hH hC)

private theorem chen_ap_switching_finite_budget {δ θ C : ℝ}
    (hδ : 0<δ) (hθ : 0<θ) (hsum : δ+θ<1/2) (hC : 0≤C)
    {N r b : ℕ} (hN : 1≤N) (hr : 0<r) (hrpow : (r:ℝ)≤(N:ℝ)^δ) (hb : b.Coprime r)
    (hy : (N:ℝ)^(1/4:ℝ)+1≤(chenUpperCutoff N:ℝ))
    (hz : (N:ℝ)^(1/16:ℝ)+1≤(chenLowerCutoff N:ℝ))
    (htwist : ∀ {N z y i K Q : ℕ} [NeZero Q] (χ : DirichletCharacter ℂ Q),
      1≤N → (N:ℝ)^(1/4:ℝ)+1≤(y:ℝ) → 1≤K → K≤N^2 → 1<Q → Q≤N^2 →
      χ≠1 → ‖chenSwitchBoxSum N z y i K χ‖≤C*(N:ℝ)^(7/8:ℝ)*(chenSwitchLog N)^2) :
    let β := max (δ+15/16) (max (2*δ+7/8) (δ+θ+1/2))
    (r.totient:ℝ)*chenReducedError (r*N) (chenPowerLevel θ N) (chenAPSwitchedError N r b)≤
      (4+6*(2*C+200000))*((N:ℝ)/(chenSwitchLog N)^4+(N:ℝ)^β*(chenSwitchLog N)^20) := by
  let D := chenPowerLevel θ N
  let z := chenLowerCutoff N
  let y := chenUpperCutoff N
  let L := chenSwitchLog N
  let R := chenAPConductorCut N r
  let B := C*(N:ℝ)^(7/8:ℝ)*L^2
  let J (a : ℕ) := chenAPBoxBudget N a D R B
  have hn : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
  have hp : (0:ℝ)<N := zero_lt_one.trans_le hn
  have hR := (chenAPConductorCut_bounds hN hr).1
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hDpow : (D:ℝ)≤(N:ℝ)^θ := Nat.floor_le (by positivity)
  have hD : D≤N := chenPowerLevel_le_self (by linarith only [hδ,hsum]) hN
  have hrD : r*D≤N := by
    suffices ((r*D:ℕ):ℝ)≤(N:ℝ) by exact_mod_cast this
    rw [Nat.cast_mul]
    calc
      _ ≤ (N:ℝ)^δ*(N:ℝ)^θ := mul_le_mul hrpow hDpow (Nat.cast_nonneg _) (by positivity)
      _ = (N:ℝ)^(δ+θ) := (Real.rpow_add hp _ _).symm
      _ ≤ (N:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by linarith only [hsum])
      _ = _ := Real.rpow_one _
  have hNZ : 0<z := Nat.cast_pos.mp ((by positivity : (0:ℝ)<(N:ℝ)^(1/16:ℝ)+1).trans_le hz)
  have hB : 0≤B := by dsimp only [B]; positivity
  have hbox (a : ℕ) (ha : a∈r.divisors) (k : ℕ) (hk : k∈Finset.Ico 1 D)
      (i : ℕ) (_hi : i∈Finset.range (N.log2+1)) :
      (∑ q∈(Finset.Ico 2 D).filter (fun q => a.Coprime q),
        chenPrimitiveNorm (a*q) (chenSwitchBoxSum N z y i ((r/a)*k))/(q:ℝ))≤J a := by
    have had := (Nat.mem_divisors.mp ha).1
    have hap := Nat.pos_of_dvd_of_pos had hr
    have har := Nat.le_of_dvd hr had
    apply chen_ap_switch_box_conductors_le hB hN hy hap hD hR
    intro q hq₂ hqD _ χ hχ
    have hk₁ := (Finset.mem_Ico.mp hk).1
    have hkD := (Finset.mem_Ico.mp hk).2.le
    have hK : 1≤(r/a)*k := Nat.mul_pos (Nat.div_pos har hap) hk₁
    have hKN : (r/a)*k≤N^2 := ((Nat.mul_le_mul (Nat.div_le_self r a) hkD).trans hrD).trans
      (by simpa only [pow_two,one_mul] using Nat.mul_le_mul_right N hN)
    have hQ : 1<a*q := hq₂.trans (Nat.le_mul_of_pos_left q hap)
    have hQN : a*q≤N^2 := ((Nat.mul_le_mul har hqD.le).trans hrD).trans
      (by simpa only [pow_two,one_mul] using Nat.mul_le_mul_right N hN)
    let _ : NeZero (a*q) := ⟨by omega⟩
    have hnon : χ≠1 := by
      intro he
      have hc := (DirichletCharacter.eq_one_iff_conductor_eq_one (χ:=χ)).mp he
      have hprim : χ.conductor=a*q := hχ
      omega
    exact htwist χ hN hy hK hKN hQ hQN hnon
  have hsumJ := chen_ap_pair_box_weights_le hN hr hD (chenSwitchPairs N z y)
    (fun _ i k => chenSwitchBoxSum N z y i k)
    (fun _ k χ => chenSwitch_masked_sum_eq_sum_boxes N z y k χ) (J:=J)
    (fun a _ => by dsimp [J,chenAPBoxBudget]; positivity) hbox
  have hchar := chenAP_switching_error_le_conductors hN hr hNZ hD hb
  refine chen_ap_remainder_finite_bound hθ hsum hC hN hr hrpow hz ?_
  have hh := mul_le_mul_of_nonneg_left hchar hφ.le
  rw [mul_add] at hh
  have hcancel : (r.totient:ℝ)*(1/(r.totient:ℝ))=1 := by field_simp
  rw [←mul_assoc (r.totient:ℝ) (1/(r.totient:ℝ)),hcancel,one_mul] at hh
  exact hh.trans (add_le_add le_rfl hsumJ)

/-- GRH supplies both the switched mass and the reduced AP switching error
uniformly for every modulus below the fixed polynomial cutoff. -/
theorem chenAPSwitchingDistribution_of_dirichletGRH {δ θ : ℝ}
    (hδ : 0<δ) (hθ : 11/24<θ) (hsum : δ+θ<1/2) (hGRH : DirichletGRH) :
    ChenAPSwitchingDistributionAt δ θ := by
  intro ε hε
  have hδ' : δ<1/8 := by linarith only [hθ,hsum]
  have hθp : 0<θ := by linarith only [hθ]
  obtain ⟨C,hC,htwist⟩ := chen_ap_switch_box_twist_of_dirichletGRH hGRH
  let β := max (δ+15/16) (max (2*δ+7/8) (δ+θ+1/2))
  have hβ : β<1 := max_lt (by linarith only [hθ,hsum])
    (max_lt (by linarith only [hθ,hsum]) (by linarith only [hsum]))
  have hbudget := chenSwitching_budget_small hβ
    (show (0:ℝ)≤4+6*(2*C+200000) by positivity) hε
  filter_upwards [chenAP_switching_mass_of_dirichletGRH hδ hδ' hGRH hε,
    hbudget,chenSwitching_cutoffs_eventually,eventually_ge_atTop (2:ℕ)] with
      N hmass hbudget hcuts hN hEven
  intro r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  refine ⟨hmass hEven r b₁ b₂ hr hrpow hb₁ hb₂ hcompat,?_⟩
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have he := chen_ap_switching_finite_budget hδ hθp hsum hC.le (by omega : 1≤N) hr hrpow hb₂
    hcuts.1 hcuts.2 (fun χ => htwist χ)
  have ht := he.trans hbudget
  have hb := (le_div_iff₀ hφ).mpr ((mul_comm (r.totient:ℝ) _).ge.trans ht)
  have hscale : ε*chenLogScale N/(r.totient:ℝ)=ε*chenAPLogScale N r := by
    unfold chenAPLogScale chenLogScale
    rw [div_mul_eq_div_div]
    ring
  exact hb.trans_eq hscale

end FareyGoldbach
