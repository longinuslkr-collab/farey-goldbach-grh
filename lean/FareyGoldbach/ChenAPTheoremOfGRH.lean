import FareyGoldbach.ChenAPExplicitMargin
import FareyGoldbach.ChenAPConditional
import FareyGoldbach.ChenAPPrimeDistributionOfGRH
import FareyGoldbach.ChenAPSwitchingRemainder

/-! # Chen representations in two prescribed reduced classes under GRH -/

open Filter
open scoped Topology Classical

namespace FareyGoldbach

theorem chen_ap_count_lower_of_dirichletGRH_at_pos {δ θ : ℝ}
    (hδ : 0<δ) (hθ : 11/24<θ) (hsum : δ+θ<1/2)
    (hmargin : 0<chenMainMargin θ) (hGRH : DirichletGRH) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        c*(N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^2) ≤
          ((chenAPRepresentations N r b₁ b₂).card:ℝ) :=
  chen_ap_count_lower_of_distributions_pos hδ (by linarith only [hθ,hsum]) hθ
    (by linarith only [hδ,hsum]) hmargin
    (chenAPPrimeDistribution_of_dirichletGRH hδ hθ hsum hGRH)
    (chenAPSwitchingDistribution_of_dirichletGRH hδ hθ hsum hGRH)

theorem chen_ap_nontrivial_count_lower_of_dirichletGRH_at_pos {δ θ : ℝ}
    (hδ : 0<δ) (hθ : 11/24<θ) (hsum : δ+θ<1/2)
    (hmargin : 0<chenMainMargin θ) (hGRH : DirichletGRH) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        c*(N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^2) ≤
          (((chenAPRepresentations N r b₁ b₂).filter (fun p => 1<N-p)).card:ℝ) :=
  chen_ap_nontrivial_count_lower_of_distributions_pos hδ (by linarith only [hθ,hsum]) hθ
    (by linarith only [hδ,hsum]) hmargin
    (chenAPPrimeDistribution_of_dirichletGRH hδ hθ hsum hGRH)
    (chenAPSwitchingDistribution_of_dirichletGRH hδ hθ hsum hGRH)

theorem chen_ap_theorem_of_dirichletGRH_at_pos {δ θ : ℝ}
    (hδ : 0<δ) (hθ : 11/24<θ) (hsum : δ+θ<1/2)
    (hmargin : 0<chenMainMargin θ) (hGRH : DirichletGRH) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ 1<m ∧
          p+m=N ∧ p%r=b₁%r ∧ m%r=b₂%r :=
  chen_ap_theorem_of_distributions_pos hδ (by linarith only [hθ,hsum]) hθ
    (by linarith only [hδ,hsum]) hmargin
    (chenAPPrimeDistribution_of_dirichletGRH hδ hθ hsum hGRH)
    (chenAPSwitchingDistribution_of_dirichletGRH hδ hθ hsum hGRH)

theorem chen_ap_count_lower_of_dirichletGRH_at {δ θ : ℝ}
    (hδ : 0<δ) (hθ : 11/24<θ) (hsum : δ+θ<1/2)
    (hmargin : 1/20<chenMainMargin θ) (hGRH : DirichletGRH) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        c*(N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^2) ≤
          ((chenAPRepresentations N r b₁ b₂).card:ℝ) :=
  chen_ap_count_lower_of_dirichletGRH_at_pos hδ hθ hsum (lt_trans (by norm_num) hmargin) hGRH

theorem chen_ap_nontrivial_count_lower_of_dirichletGRH_at {δ θ : ℝ}
    (hδ : 0<δ) (hθ : 11/24<θ) (hsum : δ+θ<1/2)
    (hmargin : 1/20<chenMainMargin θ) (hGRH : DirichletGRH) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        c*(N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^2) ≤
          (((chenAPRepresentations N r b₁ b₂).filter (fun p => 1<N-p)).card:ℝ) :=
  chen_ap_nontrivial_count_lower_of_dirichletGRH_at_pos hδ hθ hsum (lt_trans (by norm_num) hmargin) hGRH

theorem chen_ap_theorem_of_dirichletGRH_at {δ θ : ℝ}
    (hδ : 0<δ) (hθ : 11/24<θ) (hsum : δ+θ<1/2)
    (hmargin : 1/20<chenMainMargin θ) (hGRH : DirichletGRH) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ 1<m ∧
          p+m=N ∧ p%r=b₁%r ∧ m%r=b₂%r :=
  chen_ap_theorem_of_dirichletGRH_at_pos hδ hθ hsum (lt_trans (by norm_num) hmargin) hGRH

theorem chen_ap_nontrivial_count_lower_explicit_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^(1/250:ℝ) →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        c*(N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^2) ≤
          (((chenAPRepresentations N r b₁ b₂).filter (fun p => 1<N-p)).card:ℝ) :=
  chen_ap_nontrivial_count_lower_of_dirichletGRH_at_pos (θ:=4959/10000) (by norm_num) (by norm_num)
    (by norm_num) chen_main_margin_4959_pos hGRH

theorem chen_ap_theorem_explicit_of_dirichletGRH (hGRH : DirichletGRH) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^(1/250:ℝ) →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ 1<m ∧
          p+m=N ∧ p%r=b₁%r ∧ m%r=b₂%r :=
  chen_ap_theorem_of_dirichletGRH_at_pos (θ:=4959/10000) (by norm_num) (by norm_num)
    (by norm_num) chen_main_margin_4959_pos hGRH

private theorem chen_ap_positive_modulus_exponent :
    ∃ δ θ : ℝ, 0<δ ∧ 11/24<θ ∧ δ+θ<1/2 ∧ 1/20<chenMainMargin θ := by
  obtain ⟨θ,hθ,hmargin⟩ := chen_margin_near_half
  refine ⟨(1/2-θ)/2,θ,by linarith only [hθ.2],hθ.1,by linarith only [hθ.2],?_⟩
  exact hmargin θ ⟨le_rfl,hθ.2.le⟩

theorem chen_ap_count_lower_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ δ c : ℝ, 0<δ ∧ 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        c*(N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^2) ≤
          ((chenAPRepresentations N r b₁ b₂).card:ℝ) := by
  obtain ⟨δ,θ,hδ,hθ,hsum,hmargin⟩ := chen_ap_positive_modulus_exponent
  obtain ⟨c,hc,hN⟩ := chen_ap_count_lower_of_dirichletGRH_at hδ hθ hsum hmargin hGRH
  exact ⟨δ,c,hδ,hc,hN⟩

theorem chen_ap_nontrivial_count_lower_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ δ c : ℝ, 0<δ ∧ 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        c*(N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^2) ≤
          (((chenAPRepresentations N r b₁ b₂).filter (fun p => 1<N-p)).card:ℝ) := by
  obtain ⟨δ,θ,hδ,hθ,hsum,hmargin⟩ := chen_ap_positive_modulus_exponent
  obtain ⟨c,hc,hN⟩ := chen_ap_nontrivial_count_lower_of_dirichletGRH_at hδ hθ hsum hmargin hGRH
  exact ⟨δ,c,hδ,hc,hN⟩

theorem chen_ap_theorem_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ 1<m ∧
          p+m=N ∧ p%r=b₁%r ∧ m%r=b₂%r := by
  obtain ⟨δ,θ,hδ,hθ,hsum,hmargin⟩ := chen_ap_positive_modulus_exponent
  exact ⟨δ,hδ,chen_ap_theorem_of_dirichletGRH_at hδ hθ hsum hmargin hGRH⟩

end FareyGoldbach
