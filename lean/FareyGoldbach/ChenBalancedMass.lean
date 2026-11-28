import FareyGoldbach.ChenBalancedPrimeMass
import FareyGoldbach.ChenBalancedPairs
import FareyGoldbach.ChenAPSwitchingPower
import FareyGoldbach.SharpPrimeCount

/-! # Upper mass estimates for balanced semiprime complements -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

private theorem balanced_first_mem {N L : ℕ} {x : ℕ×ℕ} (hx : x∈chenBalancedPairs N L) :
    x.1∈chenBalancedFirstBand N L := by
  obtain ⟨hps,hl,hle,hprod⟩ := mem_filter.mp hx
  have hpn := Nat.mem_primesLE.mp (mem_product.mp hps).1
  have hs : x.1*x.1≤N := (Nat.mul_le_mul_left x.1 hle).trans hprod.le
  have hf : x.1≤chenPowerLevel (1/2) N := by
    apply Nat.le_floor
    rw [←Real.sqrt_eq_rpow]
    apply Real.le_sqrt_of_sq_le
    rw [pow_two]; exact_mod_cast hs
  exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hl.le,Nat.lt_succ_of_le hf⟩,hpn.2⟩

/-- On any occupied row the second coordinate of a witness supplies its residue.
Cancellation of the fixed first prime identifies the class of every other entry. -/
theorem chenBalanced_card_le_prime_majorant {N L r b : ℕ} {E : ℝ}
    (hb : b.Coprime r) (hE : 0≤E)
    (hprime : ∀ p∈chenBalancedFirstBand N L, ∀ a : ℕ, a.Coprime r →
      ((((N/p).primesLE.filter fun q => q%r=a%r).card:ℝ)) ≤ ((N/p).primeCounting:ℝ)/(r.totient:ℝ)+E) :
    ((chenAPBalancedB N r b L).card:ℝ) ≤
      chenBalancedPrimeMajorant N L/(r.totient:ℝ)+((chenBalancedFirstBand N L).card:ℝ)*E := by
  let S := chenBalancedFirstBand N L
  let P := (chenBalancedPairs N L).filter (fun x => (x.1*x.2)%r=b%r)
  let R (p : ℕ) := P.filter (fun x => x.1=p)
  have hm : (P:Set (ℕ×ℕ)).MapsTo Prod.fst S := fun _ hx => balanced_first_mem (mem_filter.mp hx).1
  have he : P.card=∑ p∈S,(R p).card := card_eq_sum_card_fiberwise hm
  have hr (p : ℕ) (hp : p∈S) : ((R p).card:ℝ)≤((N/p).primeCounting:ℝ)/(r.totient:ℝ)+E := by
    by_cases h : (R p).Nonempty
    swap
    · rw [not_nonempty_iff_eq_empty.mp h,card_empty,Nat.cast_zero]
      positivity
    obtain ⟨w,hw⟩ := h
    obtain ⟨hwP,hpw⟩ := mem_filter.mp hw
    have hb₀ : p*w.2 ≡ b [MOD r] := by
      have := (mem_filter.mp hwP).2
      change (p*w.2)%r=b%r
      simpa only [show w.1=p from hpw] using this
    have hcop : (p*w.2).Coprime r := by
      rw [Nat.Coprime,hb₀.gcd_eq]; exact hb
    obtain ⟨hpc,hwc⟩ := Nat.coprime_mul_iff_left.mp hcop
    have hpr := (mem_filter.mp hp).2
    apply le_trans _ (hprime p hp w.2 hwc)
    apply Nat.cast_le.mpr
    apply card_le_card_of_injOn Prod.snd
    · intro x hx
      obtain ⟨hxP,hxp⟩ := mem_filter.mp hx
      obtain ⟨hxpair,hxmod⟩ := mem_filter.mp hxP
      obtain ⟨hps,_,_,hlt⟩ := mem_filter.mp hxpair
      have hq := (Nat.mem_primesLE.mp (mem_product.mp hps).2).2
      have hxp' : x.1=p := hxp
      rw [hxp'] at hlt hxmod
      apply mem_filter.mpr
      exact ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_div_iff_mul_le hpr.pos).mpr
        (by simpa only [Nat.mul_comm x.2] using hlt.le),hq⟩,
        Nat.ModEq.cancel_left_of_coprime hpc.symm ((show p*x.2 ≡ b [MOD r] from hxmod).trans hb₀.symm)⟩
    · intro x hx x' hx' hqq
      have h₁ : x.1=p := (mem_filter.mp hx).2
      have h₂ : x'.1=p := (mem_filter.mp hx').2
      exact Prod.ext (h₁.trans h₂.symm) hqq
  rw [chenAPBalancedB_card_eq_pair_filter]
  change (P.card:ℝ)≤_
  rw [he,Nat.cast_sum]
  exact (sum_le_sum hr).trans_eq (by rw [sum_add_distrib,←sum_div,sum_const,nsmul_eq_mul]; rfl)

theorem chen_balanced_mass_unconditional {η : ℝ} (hη : 0<η) (hη' : η<1/6) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ((chenBalancedB N (chenPowerLevel (1/2-η) N)).card:ℝ)≤
      (2*Real.log (1/(1-2*η))+ε)*((N:ℝ)/Real.log (N:ℝ)) := by
  filter_upwards [chen_balanced_prime_majorant hη hη' hε] with N h
  let z := chenPowerLevel (1/2-η) N
  have h₀ := chenBalanced_card_le_prime_majorant (N:=N) (L:=z) (r:=1) (b:=0) (E:=0)
    (by simp) le_rfl (fun p _ _ _ => by simp [Nat.mod_one,Nat.primesLE_card_eq_primeCounting])
  exact (show ((chenBalancedB N z).card:ℝ)≤chenBalancedPrimeMajorant N z by
    simpa [chenAPBalancedB,Nat.mod_one] using h₀).trans h

theorem chen_ap_balanced_product_mass_of_dirichletGRH {η δ : ℝ} (hη : 0<η) (hη' : η<1/6)
    (hδ : 0<δ) (hδ' : δ<1/8) (hGRH : DirichletGRH) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ r b₂ : ℕ, 0<r → (r:ℝ)≤(N:ℝ)^δ →
      b₂.Coprime r →
      ((chenAPBalancedB N r b₂ (chenPowerLevel (1/2-η) N)).card:ℝ)≤
        (2*Real.log (1/(1-2*η))+ε)*chenAPMassScale N r := by
  obtain ⟨C,hC,hprime⟩ := primeAP_count_of_dirichletGRH hGRH
  have he := half_pos hε
  have hbudget := chenAP_log_power_absorb (δ:=δ) (β:=7/8) 2 1 (by linarith) hC.le he
  have hz := eventually_rpow_add_one_le_powerLevel (a:=1/4) (b:=1/2-η) (by norm_num) (by linarith)
  have hy := eventually_rpow_add_one_le_powerLevel (a:=δ) (b:=1/2) hδ.le (by linarith)
  have hy₂ := (chenPowerLevel_tendsto_atTop (by norm_num : (0:ℝ)<1/2)).eventually_ge_atTop 2
  filter_upwards [chen_balanced_prime_majorant hη hη' he,hbudget,hz,hy,hy₂,
    eventually_ge_atTop (2:ℕ)] with N hmain hbudget hz hy hy₂ hN r b₂ hr hrN hb
  let z := chenPowerLevel (1/2-η) N
  let y := chenPowerLevel (1/2) N
  let S := chenBalancedFirstBand N z
  let L := chenSwitchLog N
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hL := zero_lt_one.trans_le (one_le_chenSwitchLog (by omega : 1≤N))
  have hrroot : r≤y := (Nat.cast_le (α:=ℝ)).mp (by dsimp only [y]; linarith only [hrN,hy])
  have hφ := Nat.cast_nonneg (α:=ℝ) r.totient
  let E := C*(N:ℝ)^(3/8:ℝ)*L^2
  have hE : 0≤E := by dsimp [E]; positivity
  have hrow (p : ℕ) (hp : p∈S) (b : ℕ) (hb : b.Coprime r) :
      ((((N/p).primesLE.filter fun q => q%r=b%r).card:ℝ))≤((N/p).primeCounting:ℝ)/(r.totient:ℝ)+E := by
    obtain ⟨hI,hpr⟩ := mem_filter.mp hp
    obtain ⟨hzp,hpy⟩ := mem_Ico.mp hI
    have hq := chenBalanced_root_le_quot hpr.pos (Nat.lt_succ_iff.mp hpy)
    have hq₂ := hy₂.trans hq
    have h := (abs_le.mp (hprime hq₂ hr (hrroot.trans hq) hb)).2
    have hpx : (N:ℝ)^(1/4:ℝ)≤p := by
      have hzp' : (z:ℝ)≤p := Nat.cast_le.mpr hzp
      change (N:ℝ)^(1/4:ℝ)+1≤(z:ℝ) at hz
      linarith only [hz,hzp']
    have hxr : (((N/p:ℕ):ℝ))≤(N:ℝ)^(3/4:ℝ) := by
      refine Nat.cast_div_le.trans ((div_le_iff₀ (Nat.cast_pos.mpr hpr.pos : (0:ℝ)<p)).mpr ?_)
      calc _ = (N:ℝ)^(3/4:ℝ)*(N:ℝ)^(1/4:ℝ) := by rw [←Real.rpow_add hn]; norm_num
           _ ≤ _ := mul_le_mul_of_nonneg_left hpx (by positivity)
    have hsq : Real.sqrt ((N/p:ℕ):ℝ)≤(N:ℝ)^(3/8:ℝ) := by
      calc _ ≤ Real.sqrt ((N:ℝ)^(3/4:ℝ)) := Real.sqrt_le_sqrt hxr
           _ = _ := by rw [Real.sqrt_eq_rpow,←Real.rpow_mul hn.le]; norm_num
    have hqn : (2:ℝ)≤(N/p:ℕ) := Nat.cast_le.mpr hq₂
    have hlog₀ : 0≤Real.log (2*((N/p:ℕ):ℝ)) := Real.log_nonneg (by linarith)
    have hlog : Real.log (2*((N/p:ℕ):ℝ))≤L := by
      have h := Real.log_le_log (by linarith : 0<2*((N/p:ℕ):ℝ))
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.div_le_self N p) : ((N/p:ℕ):ℝ)≤N) (by norm_num : (0:ℝ)≤2))
      dsimp [L,chenSwitchLog]; linarith only [h]
    have hh : C*Real.sqrt ((N/p:ℕ):ℝ)*Real.log (2*((N/p:ℕ):ℝ))^2≤E :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsq hC.le) (pow_le_pow_left₀ hlog₀ hlog 2) (by positivity) (by positivity)
    linarith only [h,hh]
  have hcard : (S.card:ℝ)≤(N:ℝ)^(1/2:ℝ) := by
    apply (Nat.cast_le.mpr (chenBalancedFirstBand_card_le N z)).trans
    simpa [Real.sqrt_eq_rpow] using chenBalanced_root_floor (N:=N)
  have herror := mul_le_mul_of_nonneg_right hcard hE
  have hid : (N:ℝ)^(1/2:ℝ)*E=C*(N:ℝ)^(7/8:ℝ)*L^2 := by
    dsimp only [E]; rw [show (7/8:ℝ)=1/2+3/8 by norm_num,Real.rpow_add hn]; ring
  rw [hid] at herror
  have hsmall := hbudget r hr hrN
  rw [pow_one] at hsmall
  apply (chenBalanced_card_le_prime_majorant hb hE hrow).trans
  calc _ ≤ ((2*Real.log (1/(1-2*η))+ε/2)*((N:ℝ)/Real.log (N:ℝ)))/(r.totient:ℝ)+
             (ε/2)*chenAPMassScale N r :=
             add_le_add (div_le_div_of_nonneg_right hmain hφ) (herror.trans hsmall)
       _ = _ := by unfold chenAPMassScale; ring

theorem chen_ap_balanced_mass_of_dirichletGRH {η δ : ℝ} (hη : 0<η) (hη' : η<1/6)
    (hδ : 0<δ) (hδ' : δ<1/8) (hGRH : DirichletGRH) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ r b₁ b₂ : ℕ, 0<r → (r:ℝ)≤(N:ℝ)^δ →
      b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
      ((chenAPBalancedB N r b₂ (chenPowerLevel (1/2-η) N)).card:ℝ)≤
        (2*Real.log (1/(1-2*η))+ε)*chenAPMassScale N r := by
  filter_upwards [chen_ap_balanced_product_mass_of_dirichletGRH hη hη' hδ hδ' hGRH hε] with N h _ r _ b₂ hr hrN _ hb₂ _
  exact h r b₂ hr hrN hb₂

end FareyGoldbach
