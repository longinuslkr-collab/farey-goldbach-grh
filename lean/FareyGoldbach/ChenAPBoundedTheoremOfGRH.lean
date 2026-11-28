import FareyGoldbach.ChenAPTheoremOfGRH
import FareyGoldbach.ChenAPBalancedRemainder
import FareyGoldbach.ChenBalancedMass
import FareyGoldbach.ChenBoundedConditional

/-! # Bounded Chen representations in prescribed classes under GRH -/

open Filter
open scoped Topology

namespace FareyGoldbach

theorem chenAPBalancedDistribution_of_dirichletGRH {δ θ η : ℝ}
    (hδ : 0<δ) (hθ : 11/24<θ) (hsum : δ+θ<1/2) (hη : 0<η) (hη' : η<1/6)
    (hGRH : DirichletGRH) : ChenAPBalancedDistributionAt δ θ η := by
  intro ε hε
  have hδ' : δ<1/8 := by linarith only [hθ,hsum]
  filter_upwards [chen_ap_balanced_mass_of_dirichletGRH hη hη' hδ hδ' hGRH hε,
    chen_ap_balanced_reduced_error_of_dirichletGRH hδ hθ hsum hη' hGRH hε] with
    N hmass herr hEven r b₁ b₂ hr hpow hb₁ hb₂ hcompat
  exact ⟨hmass hEven r b₁ b₂ hr hpow hb₁ hb₂ hcompat,herr r b₂ hr hpow hb₂⟩

private theorem balanced_distribution (hGRH : DirichletGRH) :
    ChenAPBalancedDistributionAt (1/2000) (499/1000) (7/2000) :=
  chenAPBalancedDistribution_of_dirichletGRH (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hGRH

theorem chen_ap_bounded_count_lower_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^(1/2000:ℝ) →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
          c*(N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^2) ≤
            ((chenAPBoundedRepresentations N r b₁ b₂ (199/100)).card:ℝ) :=
  chen_ap_bounded_count_lower_of_distributions (δ:=1/2000) (θ:=499/1000)
    (η:=7/2000) (εcut:=3/2000) (α:=199/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) chen_margin_gt_balanced_loss_grh
    (chenAPPrimeDistribution_of_dirichletGRH (by norm_num) (by norm_num) (by norm_num) hGRH)
    (chenAPSwitchingDistribution_of_dirichletGRH (by norm_num) (by norm_num) (by norm_num) hGRH)
    (balanced_distribution hGRH)

theorem chen_ap_bounded_theorem_of_dirichletGRH (hGRH : DirichletGRH) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^(1/2000:ℝ) →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
          ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwoBounded (199/100:ℝ) m ∧
            p+m=N ∧ p%r=b₁%r ∧ m%r=b₂%r := by
  have h := chen_ap_bounded_theorem_of_distributions (δ:=1/2000) (θ:=499/1000)
    (η:=7/2000) (εcut:=3/2000) (α:=199/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) chen_margin_gt_balanced_loss_grh
    (chenAPPrimeDistribution_of_dirichletGRH (by norm_num) (by norm_num) (by norm_num) hGRH)
    (chenAPSwitchingDistribution_of_dirichletGRH (by norm_num) (by norm_num) (by norm_num) hGRH)
    (balanced_distribution hGRH)
  filter_upwards [h] with N h hEven r b₁ b₂ hr hpow hb₁ hb₂ hcompat
  obtain ⟨p,m,hp,hm,_,hN,hpmod,hmmod⟩ := h hEven r b₁ b₂ hr hpow hb₁ hb₂ hcompat
  exact ⟨p,m,hp,hm,hN,hpmod,hmmod⟩

end FareyGoldbach
