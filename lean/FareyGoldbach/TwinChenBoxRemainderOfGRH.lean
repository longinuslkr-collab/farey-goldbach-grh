import FareyGoldbach.TwinChenBoxErrors

/-! # Uniform GRH remainder estimates for the shifted product carriers -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

theorem twinChen_carrier_error_of_dirichletGRH {δ θ ε : ℝ}
    (hδ : 0<δ) (hθ : 11/24<θ) (hsum : δ+θ<1/2) (hGRH : DirichletGRH) (hε : 0<ε)
    {carrier : ℕ→ℕ→ℕ→Finset ℕ} (hboxes : TwinChenCarrierHasBoxes carrier) :
    ∀ᶠ M : ℕ in atTop, ∀ r b : ℕ, 0<r → (r:ℝ)≤(M:ℝ)^δ → (b+2).Coprime r →
      let P := carrier M r b
      chenReducedError (2*r) (chenPowerLevel θ M) (chenAPError P P.card)≤ε*chenAPLogScale M r := by
  have hθp : 0<θ := by linarith only [hθ]
  obtain ⟨C,hC,htwist⟩ := chen_ap_interval_twist_of_dirichletGRH hGRH
  let β := max (δ+15/16) (max (2*δ+7/8) (δ+θ+1/2))
  have hβ : β<1 := max_lt (by linarith only [hθ,hsum])
    (max_lt (by linarith only [hθ,hsum]) (by linarith only [hsum]))
  have hbudget := chenSwitching_budget_small hβ
    (show (0:ℝ)≤4+6*(2*C+200000) by positivity) hε
  filter_upwards [hbudget,hboxes,eventually_ge_atTop (1:ℕ)] with M hbudget hboxes hM r b hr hrpow hb
  obtain ⟨B,hCut,hCarrier⟩ := hboxes
  let D := chenPowerLevel θ M
  let R := chenAPConductorCut M r
  let T := C*(M:ℝ)^(7/8:ℝ)*(chenSwitchLog M)^2
  let P := carrier M r b
  let E := chenReducedError (2*r) D (chenAPError P P.card)
  have hn : (1:ℝ)≤M := Nat.one_le_cast.mpr hM
  have hp : (0:ℝ)<M := zero_lt_one.trans_le hn
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hR := (chenAPConductorCut_bounds hM hr).1
  have hD : D≤M := chenPowerLevel_le_self (by linarith only [hδ,hsum]) hM
  have hrD : r*D≤M := by
    suffices ((r*D:ℕ):ℝ)≤(M:ℝ) by exact_mod_cast this
    rw [Nat.cast_mul]
    calc
      _ ≤ (M:ℝ)^δ*(M:ℝ)^θ :=
        mul_le_mul hrpow (Nat.floor_le (by positivity)) (Nat.cast_nonneg _) (by positivity)
      _ = (M:ℝ)^(δ+θ) := (Real.rpow_add hp _ _).symm
      _ ≤ (M:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by linarith only [hsum])
      _ = _ := Real.rpow_one _
  have hcutpos : 0<B.cutoff :=
    Nat.cast_pos.mp ((by positivity : (0:ℝ)<(M:ℝ)^(1/16:ℝ)+1).trans_le hCut)
  have hmain : (r.totient:ℝ)*E≤
      (4+6*(2*C+200000))*((M:ℝ)/(chenSwitchLog M)^4+(M:ℝ)^β*(chenSwitchLog M)^20) := by
    apply chen_ap_remainder_finite_bound hθp hsum hC.le hM hr hrpow hCut
    apply twinChen_error_le_of_boxes B _ hM hr hcutpos hD hb (hCarrier r b)
      (J:=fun a => chenAPBoxBudget M a D R T)
      (fun a _ => by unfold chenAPBoxBudget; dsimp only [T]; positivity)
    intro a ha k hk i _
    have had := (Nat.mem_divisors.mp ha).1
    have hap := Nat.pos_of_dvd_of_pos had hr
    have har := Nat.le_of_dvd hr had
    apply twinChenBox_conductors_le B hM hap hD hR (by dsimp only [T]; positivity)
    intro q hq₂ hqD _ χ hχ
    let K := (r/a)*k
    have hk₁ := (Finset.mem_Ico.mp hk).1
    have hkD := (Finset.mem_Ico.mp hk).2.le
    have hMM : M≤M^2 := by simpa only [pow_two,one_mul] using Nat.mul_le_mul_right M hM
    have hK : 1≤K := Nat.mul_pos (Nat.div_pos har hap) hk₁
    have hKN : K≤M^2 := ((Nat.mul_le_mul (Nat.div_le_self r a) hkD).trans hrD).trans hMM
    have hQ : 1<a*q := hq₂.trans (Nat.le_mul_of_pos_left q hap)
    have hQN : a*q≤M^2 := ((Nat.mul_le_mul har hqD.le).trans hrD).trans hMM
    let _ : NeZero (a*q) := ⟨by omega⟩
    have hnon : χ≠1 := by
      intro h
      have hc := (DirichletCharacter.eq_one_iff_conductor_eq_one (χ:=χ)).mp h
      have hprim : χ.conductor=a*q := hχ
      omega
    rcases B.boxShape i with ⟨hW,hWM,hMW,hMe,_⟩ | hempty
    · exact htwist χ (B.row i K) B.lo (chenSwitchBoxHi M i) hM hW hWM hMW hMe
        (B.rowBound i K) B.loPos (chenSwitchBoxHi_le M i) hK hKN hQ hQN hnon
    · have he : B.sum i K χ=0 := hempty (a*q) K χ
      rw [he,norm_zero]
      dsimp only [T]
      positivity
  have ht := hmain.trans hbudget
  have hh := (le_div_iff₀ hφ).mpr ((mul_comm (r.totient:ℝ) _).ge.trans ht)
  have hscale : ε*chenLogScale M/(r.totient:ℝ)=ε*chenAPLogScale M r := by
    unfold chenAPLogScale chenLogScale
    rw [div_mul_eq_div_div]
    ring
  exact hh.trans_eq hscale

end FareyGoldbach
