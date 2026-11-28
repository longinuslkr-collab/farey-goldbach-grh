import FareyGoldbach.ChenBalancedRemainderCore

/-! # Uniform AP distribution of the balanced carrier under GRH -/

open Filter Finset
open scoped Classical Topology

namespace FareyGoldbach

private theorem balanced_finite_budget {δ θ C : ℝ}
    (hδ : 0<δ) (hθ : 0<θ) (hsum : δ+θ<1/2) (hC : 0≤C)
    {N r b L : ℕ} (hN : 1≤N) (hr : 0<r) (hrpow : (r:ℝ)≤(N:ℝ)^δ) (hb : b.Coprime r)
    (hL : (N:ℝ)^(1/4:ℝ)+1≤(L:ℝ))
    (htwist : ∀ {N M W K Q : ℕ} [NeZero Q] (χ : DirichletCharacter ℂ Q)
      (a : ℕ→ℂ) (lo hi : ℕ→ℕ), 1≤N → 1≤W → W≤N →
      (M:ℝ)*W≤2*N → (M:ℝ)≤2*(N:ℝ)^(3/4:ℝ) →
      (∀ m, ‖a m‖≤1) → (∀ m, 1≤lo m) → (∀ m, hi m≤W) →
      1≤K → K≤N^2 → 1<Q → Q≤N^2 → χ≠1 →
      ‖∑ m∈Finset.Icc 1 M, a m*χ (m:ZMod Q)*
        ∑ w∈Finset.Icc (lo m) (hi m), chenSwitchBoxB K w*χ (w:ZMod Q)‖ ≤
          C*(N:ℝ)^(7/8:ℝ)*(chenSwitchLog N)^2) :
    let β := max (δ+15/16) (max (2*δ+7/8) (δ+θ+1/2))
    (r.totient:ℝ)*chenReducedError (r*N) (chenPowerLevel θ N) (chenAPBalancedError N r b L)≤
      (4+6*(2*C+200000))*((N:ℝ)/(chenSwitchLog N)^4+(N:ℝ)^β*(chenSwitchLog N)^20) := by
  let D := chenPowerLevel θ N
  let R := chenAPConductorCut N r
  let B := C*(N:ℝ)^(7/8:ℝ)*(chenSwitchLog N)^2
  have hR := (chenAPConductorCut_bounds hN hr).1
  have hD : D≤N := chenPowerLevel_le_self (by linarith only [hδ,hsum]) hN
  have hn : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
  have hp : (0:ℝ)<N := zero_lt_one.trans_le hn
  have hrD : r*D≤N := by
    suffices ((r*D:ℕ):ℝ)≤(N:ℝ) by exact_mod_cast this
    rw [Nat.cast_mul]
    calc
      _ ≤ (N:ℝ)^δ*(N:ℝ)^θ :=
        mul_le_mul hrpow (Nat.floor_le (by positivity)) (Nat.cast_nonneg _) (by positivity)
      _ = (N:ℝ)^(δ+θ) := (Real.rpow_add hp _ _).symm
      _ ≤ (N:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by linarith only [hsum])
      _ = _ := Real.rpow_one _
  have hz : (N:ℝ)^(1/16:ℝ)+1≤(L:ℝ) :=
    (add_le_add (Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (1/16:ℝ)≤1/4))
      (le_refl (1:ℝ))).trans hL
  have hLp : 0<L := Nat.cast_pos.mp ((by positivity : (0:ℝ)<(N:ℝ)^(1/16:ℝ)+1).trans_le hz)
  apply chen_ap_remainder_finite_bound hθ hsum hC hN hr hrpow hz
  apply chen_balanced_remainder_of_box_bounds hN hr hLp hD hb
    (J:=fun a => chenAPBoxBudget N a D R B)
    (fun a _ => by unfold chenAPBoxBudget; dsimp only [B]; positivity)
  intro a ha k hk i _
  have had := (Nat.mem_divisors.mp ha).1
  have hap := Nat.pos_of_dvd_of_pos had hr
  have har := Nat.le_of_dvd hr had
  apply chen_balanced_box_conductors_le hN hL hap hD hR (by dsimp only [B]; positivity)
  intro q hq₂ hqD _ χ hχ
  let K := (r/a)*k
  have hk₁ := (Finset.mem_Ico.mp hk).1
  have hkD := (Finset.mem_Ico.mp hk).2.le
  have hNN : N≤N^2 := by simpa only [pow_two,one_mul] using Nat.mul_le_mul_right N hN
  have hK : 1≤K := Nat.mul_pos (Nat.div_pos har hap) hk₁
  have hKN : K≤N^2 := ((Nat.mul_le_mul (Nat.div_le_self r a) hkD).trans hrD).trans hNN
  have hQ : 1<a*q := hq₂.trans (Nat.le_mul_of_pos_left q hap)
  have hQN : a*q≤N^2 := ((Nat.mul_le_mul har hqD.le).trans hrD).trans hNN
  let _ : NeZero (a*q) := ⟨by omega⟩
  have hnon : χ≠1 := by
    intro h
    have hc := (DirichletCharacter.eq_one_iff_conductor_eq_one (χ:=χ)).mp h
    have hprim : χ.conductor=a*q := hχ
    omega
  by_cases hne : (chenBalancedBoxPairs N L i).Nonempty
  · obtain ⟨hW,hWN,hMW,hM,_⟩ := chenBalancedBox_ranges hL hN hne
    exact htwist χ (chenBalancedBoxA L i K) chenBalancedBoxLo (chenSwitchBoxHi N i)
      hN hW hWN hMW hM (chenBalancedBoxA_norm_le L i K) chenBalancedBoxLo_pos
      (chenSwitchBoxHi_le N i) hK hKN hQ hQN hnon
  · rw [chenBalancedBoxSum_eq_zero_of_empty (Finset.not_nonempty_iff_eq_empty.mp hne),norm_zero]
    positivity

theorem chen_ap_balanced_reduced_error_of_dirichletGRH {δ θ η : ℝ}
    (hδ : 0<δ) (hθ : 11/24<θ) (hsum : δ+θ<1/2) (hη : η<1/6) (hGRH : DirichletGRH)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ r b : ℕ, 0<r → (r:ℝ)≤(N:ℝ)^δ → b.Coprime r →
      chenReducedError (r*N) (chenPowerLevel θ N)
        (chenAPBalancedError N r b (chenPowerLevel (1/2-η) N))≤ε*chenAPLogScale N r := by
  have hθp : 0<θ := by linarith only [hθ]
  obtain ⟨C,hC,htwist⟩ := chen_ap_interval_twist_of_dirichletGRH hGRH
  let β := max (δ+15/16) (max (2*δ+7/8) (δ+θ+1/2))
  have hβ : β<1 := max_lt (by linarith only [hθ,hsum])
    (max_lt (by linarith only [hθ,hsum]) (by linarith only [hsum]))
  have hbudget := chenSwitching_budget_small hβ
    (show (0:ℝ)≤4+6*(2*C+200000) by positivity) hε
  filter_upwards [hbudget,chen_balanced_cutoff_eventually hη,eventually_ge_atTop (1:ℕ)] with
    N hbudget hcut hN r b hr hrpow hb
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have he := balanced_finite_budget hδ hθp hsum hC.le hN hr hrpow hb hcut (fun χ => htwist χ)
  have ht := he.trans hbudget
  have hh := (le_div_iff₀ hφ).mpr ((mul_comm (r.totient:ℝ) _).ge.trans ht)
  have hscale : ε*chenLogScale N/(r.totient:ℝ)=ε*chenAPLogScale N r := by
    unfold chenAPLogScale chenLogScale
    rw [div_mul_eq_div_div]
    ring
  exact hh.trans_eq hscale

end FareyGoldbach
