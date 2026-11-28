import FareyGoldbach.ChenAPSwitchingFibers
import FareyGoldbach.ChenAPSwitchingTwists
import FareyGoldbach.ChenAPSwitchingPower
import FareyGoldbach.ChenSwitchingMass
import FareyGoldbach.ChenConductorExpansion

/-! # Switched mass in one reduced residue class under GRH -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

/-- Orthogonality on a single modulus and GRH on each last-prime fiber give a
power-saving error uniformly in the prescribed reduced residue class. -/
theorem chenAP_switching_mass_discrepancy_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ K : ℝ, 0<K ∧ ∀ {N z y r b : ℕ}, 1≤N → 0<r → r≤N → r<z → b.Coprime r →
      (N:ℝ)^(1/4:ℝ)+1≤(y:ℝ) →
      |((chenAPUnrestrictedB N r b z y).card:ℝ)-
        ((chenUnrestrictedB N z y).card:ℝ)/(r.totient:ℝ)| ≤ K*(N:ℝ)^(7/8:ℝ)*(chenSwitchLog N)^3 := by
  obtain ⟨C,hC,hbox⟩ := chenAP_switching_box_twist_of_dirichletGRH hGRH
  refine ⟨3*C,by positivity,?_⟩
  intro N z y r b hN hr hrN hrz hbr hy
  let _ : NeZero r := ⟨hr.ne'⟩
  let P := chenSwitchPairs N z y
  let L := chenSwitchLog N
  let S := (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ≠1)
  let E := (3*C)*(N:ℝ)^(7/8:ℝ)*L^3
  have hL : 0<L := zero_lt_one.trans_le (one_le_chenSwitchLog hN)
  have hE : 0≤E := by dsimp [E]; positivity
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hs (χ : DirichletCharacter ℂ r) (hχ : χ∈S) :
      ‖∑ x∈P, χ ((x.1*x.2:ℕ):ZMod r)‖≤E := by
    have hn := (mem_filter.mp hχ).2
    have he : (∑ x∈P, χ ((x.1*x.2:ℕ):ZMod r))=
        ∑ i∈range (N.log2+1),chenSwitchBoxSum N z y i 1 χ := by
      simpa [P] using chenSwitch_masked_sum_eq_sum_boxes N z y 1 χ
    rw [he]
    calc _ ≤ ∑ i∈range (N.log2+1), ‖chenSwitchBoxSum N z y i 1 χ‖ := norm_sum_le _ _
         _ ≤ ∑ _i∈range (N.log2+1), C*(N:ℝ)^(7/8:ℝ)*L^2 :=
           sum_le_sum fun _ _ => hbox χ hN hrN hy hn
         _ = ((range (N.log2+1)).card:ℝ)*(C*(N:ℝ)^(7/8:ℝ)*L^2) := by rw [sum_const,nsmul_eq_mul]
         _ ≤ (3*L)*(C*(N:ℝ)^(7/8:ℝ)*L^2) :=
           mul_le_mul_of_nonneg_right (chen_log2_range_card_le hN) (by positivity)
         _ = E := by dsimp only [E]; ring
  have hS : S.card≤r.totient := by
    apply (card_le_card (filter_subset ..)).trans_eq
    rw [card_univ,←Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ r
  have havg : (∑ χ∈S, ‖∑ x∈P, χ ((x.1*x.2:ℕ):ZMod r)‖)/(r.totient:ℝ)≤E := by
    apply (div_le_iff₀ hφ).mpr
    calc _ ≤ ∑ _χ∈S,E := sum_le_sum hs
         _ = E*(S.card:ℝ) := by rw [sum_const,nsmul_eq_mul,mul_comm]
         _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hS) hE
  have hem : (P.filter (fun x => ¬(x.1*x.2).Coprime r))=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hp,hbad⟩ := mem_filter.mp hx
    exact hbad (chenSwitchPairs_coprime_of_modulus_lt_cutoff hr hrz hp)
  have h := chenPairAP_discrepancy_le P hr hbr
  rw [hem,card_empty,Nat.cast_zero,zero_add,←chenNonprincipal_sum_eq_conductors] at h
  rw [chenAPUnrestrictedB_card_eq_pair_filter,chenUnrestrictedB_card_eq_pairs]
  exact h.trans havg

theorem chenAP_switching_product_mass_of_dirichletGRH {δ : ℝ} (hδ : 0<δ) (hδ' : δ<1/8)
    (hGRH : DirichletGRH) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ r b₂ : ℕ, 0<r → (r:ℝ)≤(N:ℝ)^δ →
      b₂.Coprime r →
      ((chenAPUnrestrictedB N r b₂ (chenLowerCutoff N) (chenUpperCutoff N)).card:ℝ)≤
        (chenSwitchIntegral+ε)*chenAPMassScale N r := by
  obtain ⟨K,hK,hdisc⟩ := chenAP_switching_mass_discrepancy_of_dirichletGRH hGRH
  have he := half_pos hε
  have hbudget := chenAP_log_power_absorb (δ:=δ) (β:=7/8) 3 1 (by linarith) hK.le he
  have hza := eventually_rpow_add_one_le_powerLevel hδ.le hδ'
  filter_upwards [chen_switching_mass_of_dirichletGRH hGRH (ε/2) he,chenSwitching_cutoffs_eventually,
    hza,hbudget,eventually_ge_atTop (2:ℕ)] with N hm hcuts hz hbudget hN r b₂ hr hrN hb₂
  have hN₁ : (1:ℝ)≤N := Nat.one_le_cast.mpr (by omega)
  have hrN' : r≤N := by
    apply (Nat.cast_le (α:=ℝ)).mp
    exact hrN.trans ((Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith : δ≤1)).trans_eq (Real.rpow_one _))
  have hrz : r<chenLowerCutoff N := by
    apply (Nat.cast_lt (α:=ℝ)).mp
    change (N:ℝ)^δ+1≤(chenLowerCutoff N:ℝ) at hz
    linarith only [hz,hrN]
  have hh := (abs_le.mp (hdisc (by omega : 1≤N) hr hrN' hrz hb₂ hcuts.1)).2
  have hsmall := hbudget r hr hrN
  rw [pow_one] at hsmall
  have hφ := Nat.cast_nonneg (α:=ℝ) r.totient
  calc
    _ ≤ ((chenUnrestrictedB N (chenLowerCutoff N) (chenUpperCutoff N)).card:ℝ)/(r.totient:ℝ)+
        K*(N:ℝ)^(7/8:ℝ)*(chenSwitchLog N)^3 := by linarith only [hh]
    _ ≤ ((chenSwitchIntegral+ε/2)*((N:ℝ)/Real.log (N:ℝ)))/(r.totient:ℝ)+
          (ε/2)*chenAPMassScale N r :=
      add_le_add (div_le_div_of_nonneg_right hm hφ) hsmall
    _ = _ := by unfold chenAPMassScale; ring

theorem chenAP_switching_mass_of_dirichletGRH {δ : ℝ} (hδ : 0<δ) (hδ' : δ<1/8)
    (hGRH : DirichletGRH) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ r b₁ b₂ : ℕ, 0<r → (r:ℝ)≤(N:ℝ)^δ →
      b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
      ((chenAPUnrestrictedB N r b₂ (chenLowerCutoff N) (chenUpperCutoff N)).card:ℝ)≤
        (chenSwitchIntegral+ε)*chenAPMassScale N r := by
  filter_upwards [chenAP_switching_product_mass_of_dirichletGRH hδ hδ' hGRH hε] with N h _ r _ b₂ hr hrN _ hb₂ _
  exact h r b₂ hr hrN hb₂

end FareyGoldbach
