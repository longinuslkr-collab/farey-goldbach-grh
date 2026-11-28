import FareyGoldbach.TwinChenConditional
import FareyGoldbach.TwinChenPrimeDistribution
import FareyGoldbach.TwinChenSwitchDistribution
import FareyGoldbach.ChenAPExplicitMargin

/-! # Explicit twin Chen estimates in prescribed reduced classes under GRH -/

open Filter Finset
open scoped Topology

namespace FareyGoldbach

theorem twinChen_ap_count_lower_explicit_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℕ in atTop, ∀ r b : ℕ,
      0<r → (r:ℝ)≤(X:ℝ)^(1/250:ℝ) → b.Coprime r → (b+2).Coprime r →
        c*(X:ℝ)/((r.totient:ℝ)*Real.log (X:ℝ)^2)≤((twinChenRepresentations X r b).card:ℝ) :=
  twinChen_count_lower_of_distributions (δ:=1/250) (θ:=4959/10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) chen_main_margin_4959_pos
    (twinChenPrimeDistribution_of_dirichletGRH (by norm_num) (by norm_num) (by norm_num) hGRH)
    (twinChenClassicDistribution_of_dirichletGRH (by norm_num) (by norm_num) (by norm_num) hGRH)

theorem twinChen_ap_exists_explicit_of_dirichletGRH (hGRH : DirichletGRH) :
    ∀ᶠ X : ℕ in atTop, ∀ r b : ℕ,
      0<r → (r:ℝ)≤(X:ℝ)^(1/250:ℝ) → b.Coprime r → (b+2).Coprime r →
        ∃ p : ℕ, p.Prime ∧ p≤X ∧ p%r=b%r ∧ IsAlmostPrimeTwo (p+2) := by
  classical
  obtain ⟨c,hc,h⟩ := twinChen_ap_count_lower_explicit_of_dirichletGRH hGRH
  filter_upwards [h,eventually_ge_atTop (2:ℕ)] with X h hX r b hr hpow hb hb'
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hX' : (1:ℝ)<X := by exact_mod_cast (show 1<X by omega)
  have hlog := Real.log_pos hX'
  have hp : (0:ℝ)<c*(X:ℝ)/((r.totient:ℝ)*Real.log (X:ℝ)^2) := by positivity
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (Nat.cast_pos.mp
    (hp.trans_le (h r b hr hpow hb hb')))
  obtain ⟨hpr,hmod,ha⟩ := Finset.mem_filter.mp hp
  obtain ⟨hX,hprime⟩ := Nat.mem_primesLE.mp hpr
  exact ⟨p,hprime,hX,hmod,ha⟩

theorem twinChen_ap_bounded_count_lower_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℕ in atTop, ∀ r b : ℕ,
      0<r → (r:ℝ)≤(X:ℝ)^(1/2000:ℝ) → b.Coprime r → (b+2).Coprime r →
        c*(X:ℝ)/((r.totient:ℝ)*Real.log (X:ℝ)^2)≤
          ((twinChenBoundedRepresentations X r b (199/100)).card:ℝ) :=
  twinChen_bounded_count_lower_of_distributions (δ:=1/2000) (θ:=499/1000)
    (η:=7/2000) (εcut:=3/2000) (α:=199/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    chen_margin_gt_balanced_loss_grh
    (twinChenPrimeDistribution_of_dirichletGRH (by norm_num) (by norm_num) (by norm_num) hGRH)
    (twinChenClassicDistribution_of_dirichletGRH (by norm_num) (by norm_num) (by norm_num) hGRH)
    (twinChenBoundedDistribution_of_dirichletGRH (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hGRH)

theorem twinChen_ap_bounded_exists_of_dirichletGRH (hGRH : DirichletGRH) :
    ∀ᶠ X : ℕ in atTop, ∀ r b : ℕ,
      0<r → (r:ℝ)≤(X:ℝ)^(1/2000:ℝ) → b.Coprime r → (b+2).Coprime r →
        ∃ p : ℕ, p.Prime ∧ p≤X ∧ p%r=b%r ∧ IsAlmostPrimeTwoBounded (199/100:ℝ) (p+2) := by
  classical
  obtain ⟨c,hc,h⟩ := twinChen_ap_bounded_count_lower_of_dirichletGRH hGRH
  filter_upwards [h,eventually_ge_atTop (2:ℕ)] with X h hX r b hr hpow hb hb'
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hX' : (1:ℝ)<X := by exact_mod_cast (show 1<X by omega)
  have hlog := Real.log_pos hX'
  have hp : (0:ℝ)<c*(X:ℝ)/((r.totient:ℝ)*Real.log (X:ℝ)^2) := by positivity
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (Nat.cast_pos.mp
    (hp.trans_le (h r b hr hpow hb hb')))
  obtain ⟨hpr,hmod,ha⟩ := Finset.mem_filter.mp hp
  obtain ⟨hX,hprime⟩ := Nat.mem_primesLE.mp hpr
  exact ⟨p,hprime,hX,hmod,ha⟩

end FareyGoldbach
