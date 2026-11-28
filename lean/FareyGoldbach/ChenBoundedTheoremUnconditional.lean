import FareyGoldbach.ChenAPModulusOne
import FareyGoldbach.ChenAPExplicitMargin
import FareyGoldbach.ChenBalancedMass
import FareyGoldbach.ChenBalancedRemainderUnconditional
import FareyGoldbach.ChenBoundedConditional

/-! # Unconditional bounded Chen representations -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

theorem chenAPBalancedDistributionAt_zero_unconditional {θ η : ℝ}
    (hθ : 11/24<θ) (hθ' : θ<1/2) (hη : 0<η) (hη' : η<1/6) :
    ChenAPBalancedDistributionAt 0 θ η := by
  intro ε hε
  filter_upwards [chen_balanced_mass_unconditional hη hη' hε,
    chen_balanced_reduced_error_unconditional hθ hθ' hη' hε] with
    N hmass herr _hEven r b₁ b₂ hr hpow _hb₁ _hb₂ _hcompat
  have hr1 : r=1 := by
    have h : (r:ℝ)≤1 := by simpa only [Real.rpow_zero] using hpow
    have hr' : r≤1 := by exact_mod_cast h
    omega
  subst r
  refine ⟨?_,?_⟩
  · simpa only [chenAPBalancedB_modulus_one,chenAPMassScale,Nat.totient_one,Nat.cast_one,one_mul]
      using hmass
  · have h0 : chenAPBalancedError N 1 0 (chenPowerLevel (1/2-η) N) =
        chenAPBalancedError N 1 b₂ (chenPowerLevel (1/2-η) N) := by
      funext d
      simp only [chenAPBalancedError,chenAPBalancedB_modulus_one]
    rw [h0] at herr
    change chenReducedError (1*N) (chenPowerLevel θ N)
      (chenAPBalancedError N 1 b₂ (chenPowerLevel (1/2-η) N))≤ε*chenAPLogScale N 1
    simpa only [chenAPLogScale,chenLogScale,Nat.totient_one,Nat.cast_one,one_mul]
      using herr

noncomputable def chenBoundedRepresentations (N : ℕ) (α : ℝ) : Finset ℕ :=
  (chenRepresentations N).filter (fun p => IsAlmostPrimeTwoBounded α (N-p))

theorem chenAPBoundedRepresentations_modulus_one (N b₁ b₂ : ℕ) (α : ℝ) :
    chenAPBoundedRepresentations N 1 b₁ b₂ α=chenBoundedRepresentations N α := by
  simp [chenAPBoundedRepresentations,chenBoundedRepresentations,chenAPRepresentations,Nat.mod_one]

theorem chen_bounded_count_lower_unconditional :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      c*(N:ℝ)/Real.log (N:ℝ)^2 ≤ ((chenBoundedRepresentations N (199/100)).card:ℝ) := by
  obtain ⟨c,hc,h⟩ := chen_ap_bounded_count_lower_of_distributions (δ:=0) (θ:=4999/10000)
    (η:=9/2000) (εcut:=1/2000) (α:=199/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) chen_margin_gt_balanced_loss_unconditional
    (chenAPPrimeDistributionAt_zero_unconditional (by norm_num) (by norm_num))
    (chenAPSwitchingDistributionAt_zero_unconditional (by norm_num) (by norm_num))
    (chenAPBalancedDistributionAt_zero_unconditional (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
  refine ⟨c,hc,?_⟩
  filter_upwards [h] with N h he
  simpa only [chenAPBoundedRepresentations_modulus_one,Nat.totient_one,Nat.cast_one,one_mul] using
    h he 1 0 0 (by decide) (by simp) (by simp) (by simp) (by rw [Nat.mod_one,Nat.mod_one])

theorem chen_bounded_theorem_unconditional :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwoBounded (199/100:ℝ) m ∧ p+m=N := by
  have h := chen_ap_bounded_theorem_of_distributions (δ:=0) (θ:=4999/10000)
    (η:=9/2000) (εcut:=1/2000) (α:=199/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) chen_margin_gt_balanced_loss_unconditional
    (chenAPPrimeDistributionAt_zero_unconditional (by norm_num) (by norm_num))
    (chenAPSwitchingDistributionAt_zero_unconditional (by norm_num) (by norm_num))
    (chenAPBalancedDistributionAt_zero_unconditional (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
  filter_upwards [h] with N h he
  obtain ⟨p,m,hp,hm,_,hN,_,_⟩ :=
    h he 1 0 0 (by decide) (by simp) (by simp) (by simp) (by rw [Nat.mod_one,Nat.mod_one])
  exact ⟨p,m,hp,hm,hN⟩

end FareyGoldbach
