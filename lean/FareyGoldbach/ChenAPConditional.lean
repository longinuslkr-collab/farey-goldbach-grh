import FareyGoldbach.ChenAPComparisons
import FareyGoldbach.ChenAPDistributionInterfaces

/-! # The conditional Chen theorem in two specified residue classes -/

open Filter
open scoped Classical Topology

namespace FareyGoldbach

noncomputable def apSieveScale (N r : ℕ) : ℝ :=
  chenCanonicalU (r*N)*chenAPLogScale N r

noncomputable def apLowerTerm (N r b : ℕ) : ℝ :=
  (chenSifted (r*N) (chenLowerCutoff N) (chenAPA N r b)).card

noncomputable def apMediumTerm (N r b : ℕ) : ℝ :=
  ∑ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
    ((chenSifted (r*N) (chenLowerCutoff N) (chenDivisible (chenAPA N r b) q)).card:ℝ)

noncomputable def apSwitchedTerm (N r b : ℕ) : ℝ :=
  (chenSifted (r*N) (chenUpperCutoff N)
    (chenAPUnrestrictedB N r b (chenLowerCutoff N) (chenUpperCutoff N))).card

theorem ap_sieve_terms_of_distributions {δ θ : ℝ} (hδ : δ<1)
    (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2)
    (hA : ChenAPPrimeDistributionAt δ θ) (hB : ChenAPSwitchingDistributionAt δ θ)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        (chenLowerMainCoeff θ-ε)*apSieveScale N r≤apLowerTerm N r b₁ ∧
        apMediumTerm N r b₁≤(chenMediumMainCoeff θ+ε)*apSieveScale N r ∧
        apSwitchedTerm N r b₂≤(chenSwitchedMainCoeff θ+ε)*apSieveScale N r := by
  let a := chenLowerMainCoeff θ
  let m := chenMediumMainCoeff θ
  let b := 2/θ
  let c := chenSwitchIntegral
  have ⟨ha,hm,hb⟩ : 0<a ∧ 0≤m ∧ 0<b := chen_coeff_pos hθ₁
  have hc : 0≤c := chenSwitchIntegral_nonneg
  obtain ⟨τ,hτ,_,hτa,hbud₁,hbud₂,hbud₃⟩ := chen_profile_budget ha hm hb.le hc hε
  filter_upwards [eventually_ge_atTop (2^24:ℕ), hA τ hτ, hB τ hτ,
    chenAPRosserMainComparisons_unconditional hθ₁ hθ₂ τ hτ] with N hN hA' hB' hProfile hEven
  intro r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  let K := r*N
  let z := chenLowerCutoff N
  let y := chenUpperCutoff N
  let D := chenPowerLevel θ N
  let A := chenAPA N r b₁
  let B := chenAPUnrestrictedB N r b₂ z y
  let R := chenAPMassScale N r
  let v := chenCanonicalU K/Real.log (N:ℝ)
  let T := apSieveScale N r
  have hN' : (2:ℝ)≤N := by exact_mod_cast (show (2:ℕ)≤N by omega)
  have hN₁ : (1:ℝ)≤N := by linarith only [hN']
  have hrN : r≤N := by
    have hp := Real.rpow_le_rpow_of_exponent_le hN₁ hδ.le
    rw [Real.rpow_one] at hp
    exact Nat.cast_le.mp (hrpow.trans hp)
  have hL : 0<Real.log (N:ℝ) := Real.log_pos (by linarith only [hN'])
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hK : 2≤K := (by omega : 2≤N).trans (Nat.le_mul_of_pos_left N hr)
  have hU := chenCanonicalU_ge_half (hEven.mul_left r) hK
  have hU₀ : 0≤chenCanonicalU K := by linarith only [hU]
  have hv : 0≤v := by dsimp [v]; positivity
  have hR : 0<R := by dsimp [R,chenAPMassScale]; positivity
  have hT : T=R*v := by
    dsimp only [T,apSieveScale,chenAPLogScale,R,chenAPMassScale,v,K]
    field_simp
  have hT₀ : 0≤T := hT.symm ▸ mul_nonneg hR.le hv
  have hS : 0≤chenAPLogScale N r := by unfold chenAPLogScale; positivity
  have hlog : chenAPLogScale N r≤2*T := by
    have hh := mul_le_mul_of_nonneg_right hU hS
    dsimp only [T,apSieveScale]
    linarith only [hh]
  have hErr := mul_le_mul_of_nonneg_left hlog hτ.le
  obtain ⟨hAr,he₁,he₂⟩ := hA' hEven r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  obtain ⟨hBu,he₃⟩ := hB' hEven r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  have hAr' := abs_le.mp hAr
  change -τ≤(A.card:ℝ)/R-1 ∧ (A.card:ℝ)/R-1≤τ at hAr'
  have hAl : (1-τ)*R≤(A.card:ℝ) := (le_div_iff₀ hR).mp (by linarith only [hAr'.1])
  have hAu : (A.card:ℝ)≤(1+τ)*R := (div_le_iff₀ hR).mp (by linarith only [hAr'.2])
  have ⟨hP₁,hP₂,hP₃⟩ := hProfile hEven r hr hrN
  obtain ⟨hFin₁,hFin₂,hFin₃⟩ := chen_finite_sieve_terms_for_carriers hθ₁ hN K A B
  let P := chenSiftingProduct K z
  let P' := chenSiftingProduct K y
  let W := ∑ q∈chenMediumPrimes z y,
    if q∣K then 0 else chenDivisorDensity q*linearSieveMain true P (D/q) chenDivisorDensity
  have hLow : ((1-τ)*(a-τ))*T ≤ (A.card:ℝ)*linearSieveMain false P D chenDivisorDensity := by
    calc
      _ = ((1-τ)*R)*((a-τ)*v) := by rw [hT]; ring
      _ ≤ (A.card:ℝ)*((a-τ)*v) := mul_le_mul_of_nonneg_right hAl (mul_nonneg (sub_nonneg.mpr hτa) hv)
      _ ≤ _ := mul_le_mul_of_nonneg_left hP₁ (Nat.cast_nonneg _)
  have hMed : (A.card:ℝ)*W≤((1+τ)*(m+τ))*T := by
    calc
      _ ≤ (A.card:ℝ)*((m+τ)*v) := mul_le_mul_of_nonneg_left hP₂ (Nat.cast_nonneg _)
      _ ≤ ((1+τ)*R)*((m+τ)*v) := mul_le_mul_of_nonneg_right hAu (by positivity)
      _ = _ := by rw [hT]; ring
  have hSwi : (B.card:ℝ)*linearSieveMain true P' D chenDivisorDensity≤((c+τ)*(b+τ))*T := by
    calc
      _ ≤ (B.card:ℝ)*((b+τ)*v) := mul_le_mul_of_nonneg_left hP₃ (Nat.cast_nonneg _)
      _ ≤ ((c+τ)*R)*((b+τ)*v) := mul_le_mul_of_nonneg_right hBu (by positivity)
      _ = _ := by rw [hT]; ring
  have h₁ := mul_le_mul_of_nonneg_right hbud₁ hT₀
  have h₂ := mul_le_mul_of_nonneg_right hbud₂ hT₀
  have h₃ := mul_le_mul_of_nonneg_right hbud₃ hT₀
  change (A.card:ℝ)*linearSieveMain false P D chenDivisorDensity -
    chenReducedError K D (chenAPPrimeError N r b₁) ≤ apLowerTerm N r b₁ at hFin₁
  change apMediumTerm N r b₁ ≤ (A.card:ℝ)*W+chenAPMediumError N r b₁ D at hFin₂
  change apSwitchedTerm N r b₂ ≤ (B.card:ℝ)*linearSieveMain true P' D chenDivisorDensity +
    chenReducedError K D (chenAPSwitchedError N r b₂) at hFin₃
  change (a-ε)*T≤apLowerTerm N r b₁ ∧ apMediumTerm N r b₁≤(m+ε)*T ∧
    apSwitchedTerm N r b₂≤(b*c+ε)*T
  exact ⟨by linarith only [h₁,hLow,hFin₁,he₁,hErr],
    by linarith only [h₂,hMed,hFin₂,he₂,hErr],
    by linarith only [h₃,hSwi,hFin₃,he₃,hErr]⟩

/-- Uniform quantitative Chen bound in two prescribed reduced classes,
given the prime and switched distribution estimates at the same level. -/
theorem chen_ap_count_lower_of_distributions_pos {δ θ : ℝ}
    (hδ₀ : 0<δ) (hδ : δ<1/8) (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2)
    (hmargin : 0<chenMainMargin θ)
    (hA : ChenAPPrimeDistributionAt δ θ) (hB : ChenAPSwitchingDistributionAt δ θ) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        c*(N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^2) ≤
          ((chenAPRepresentations N r b₁ b₂).card:ℝ) := by
  have hδ' : δ∈Set.Ioo (0:ℝ) 1 := ⟨hδ₀,hδ.trans (by norm_num)⟩
  let m := chenMainMargin θ
  have hm : 0<m := hmargin
  refine ⟨m/4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2^24:ℕ),
    ap_sieve_terms_of_distributions hδ'.2 hθ₁ hθ₂ hA hB (ε:=m/8) (by positivity),
    chenAP_power_error_eventually_le hδ (ε:=m/16) (by positivity)] with N hN ht hp hEven
  intro r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  have ⟨hLo,hMed,hSwi⟩ := ht hEven r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  have hSw := chenAP_switching_inequality_floor_explicit hN hb₂ hcompat
  change apLowerTerm N r b₁ - (1/2)*apMediumTerm N r b₁ -
    (1/2)*apSwitchedTerm N r b₂ - (2*(N:ℝ)^(7/8:ℝ)+(N:ℝ)^(1/3:ℝ)) ≤
      (chenAPCount N r b₁:ℝ) at hSw
  have hK : 2≤r*N := (by omega : 2≤N).trans (Nat.le_mul_of_pos_left N hr)
  have hU := chenCanonicalU_ge_half (hEven.mul_left r) hK
  have hU₀ : 0≤chenCanonicalU (r*N) := by linarith only [hU]
  have hScale : 0≤chenAPLogScale N r := by unfold chenAPLogScale; positivity
  have hT : 0≤apSieveScale N r := mul_nonneg hU₀ hScale
  have hhalf : chenAPLogScale N r≤2*apSieveScale N r := by
    have hh := mul_le_mul_of_nonneg_right hU hScale
    unfold apSieveScale
    linarith only [hh]
  have hPower : 2*(N:ℝ)^(7/8:ℝ)+(N:ℝ)^(1/3:ℝ)≤(m/8)*apSieveScale N r := by
    calc _ ≤ (m/16)*chenAPLogScale N r := hp r hr hrpow
         _ ≤ (m/16)*(2*apSieveScale N r) :=
           mul_le_mul_of_nonneg_left hhalf (by positivity)
         _ = _ := by ring
  have he : m*apSieveScale N r = (chenLowerMainCoeff θ -
      (1/2)*chenMediumMainCoeff θ - (1/2)*chenSwitchedMainCoeff θ)*apSieveScale N r := rfl
  have hCount : (m/2)*apSieveScale N r≤(chenAPCount N r b₁:ℝ) := by
    linarith only [hSw,hLo,hMed,hSwi,hPower,he,mul_nonneg hm.le hT]
  rw [← chenAPCount_eq_representations_card hcompat,mul_div_assoc]
  change (m/4)*chenAPLogScale N r≤(chenAPCount N r b₁:ℝ)
  calc _ ≤ (m/4)*(2*apSieveScale N r) := mul_le_mul_of_nonneg_left hhalf (by positivity)
       _ = (m/2)*apSieveScale N r := by ring
       _ ≤ _ := hCount

/-- The quantitative lower bound persists when only complements greater than one
are counted. -/
theorem chen_ap_nontrivial_count_lower_of_distributions_pos {δ θ : ℝ}
    (hδ₀ : 0<δ) (hδ : δ<1/8) (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2)
    (hmargin : 0<chenMainMargin θ)
    (hA : ChenAPPrimeDistributionAt δ θ) (hB : ChenAPSwitchingDistributionAt δ θ) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        c*(N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^2) ≤
          (((chenAPRepresentations N r b₁ b₂).filter (fun p => 1<N-p)).card:ℝ) := by
  obtain ⟨c,hc,hLower⟩ := chen_ap_count_lower_of_distributions_pos hδ₀ hδ hθ₁ hθ₂ hmargin hA hB
  have hδ' : δ<1 := by linarith only [hδ]
  refine ⟨c/2, by positivity, ?_⟩
  filter_upwards [hLower,chenAPLogScale_eventually_gt hδ' (show 0<4/c by positivity)]
    with N hLower hScale hEven
  intro r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  let S := chenAPRepresentations N r b₁ b₂
  let good : ℕ → Prop := fun p => 1<N-p
  have hSub : S.filter (fun p => ¬good p) ⊆ (Finset.range 2).image (fun m => N-m) := by
    intro p hp
    obtain ⟨hp,hbad⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpR,_⟩ := Finset.mem_filter.mp hp
    have hpN : p≤N := by simpa using Finset.mem_range.mp (Finset.mem_filter.mp hpR).1
    change ¬1<N-p at hbad
    exact Finset.mem_image.mpr ⟨N-p, Finset.mem_range.mpr (by omega),Nat.sub_sub_self hpN⟩
  have hBad : (S.filter (fun p => ¬good p)).card≤2 := by
    simpa using (Finset.card_le_card hSub).trans Finset.card_image_le
  have hBadR : ((S.filter (fun p => ¬good p)).card:ℝ)≤2 := by exact_mod_cast hBad
  have hCard : ((S.filter good).card:ℝ)+((S.filter (fun p => ¬good p)).card:ℝ)=S.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s:=S) good
  have hL := hLower hEven r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  rw [mul_div_assoc] at hL
  change c*chenAPLogScale N r≤(S.card:ℝ) at hL
  have hBig := (div_lt_iff₀ hc).mp (hScale r hr hrpow)
  rw [mul_comm] at hBig
  rw [mul_div_assoc]
  change c/2*chenAPLogScale N r≤((S.filter good).card:ℝ)
  linarith only [hL,hBig,hCard,hBadR]

/-- Conditional Chen theorem for each admissible pair of reduced
classes, with a complement strictly greater than one. -/
theorem chen_ap_theorem_of_distributions_pos {δ θ : ℝ}
    (hδ₀ : 0<δ) (hδ : δ<1/8) (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2)
    (hmargin : 0<chenMainMargin θ)
    (hA : ChenAPPrimeDistributionAt δ θ) (hB : ChenAPSwitchingDistributionAt δ θ) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ 1<m ∧
          p+m=N ∧ p%r=b₁%r ∧ m%r=b₂%r := by
  obtain ⟨c,hc,hLower⟩ :=
    chen_ap_nontrivial_count_lower_of_distributions_pos hδ₀ hδ hθ₁ hθ₂ hmargin hA hB
  have hδ' : δ<1 := by linarith only [hδ]
  filter_upwards [hLower,chenAPLogScale_eventually_gt hδ' (show (0:ℝ)<1 by norm_num)]
    with N hLower hScale hEven
  intro r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  let S := (chenAPRepresentations N r b₁ b₂).filter (fun p => 1<N-p)
  have hL := hLower hEven r b₁ b₂ hr hrpow hb₁ hb₂ hcompat
  rw [mul_div_assoc] at hL
  change c*chenAPLogScale N r≤(S.card:ℝ) at hL
  have hPos : (0:ℝ)<S.card :=
    (mul_pos hc ((show (0:ℝ)<1 by norm_num).trans (hScale r hr hrpow))).trans_le hL
  have hCard : 0<S.card := by exact_mod_cast hPos
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hCard
  obtain ⟨hp,hm⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpR,hp₁,hp₂⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpN,hPrime,hAlmost⟩ := Finset.mem_filter.mp hpR
  have hpN' : p≤N := by simpa using Finset.mem_range.mp hpN
  exact ⟨p,N-p,hPrime,hAlmost,hm,Nat.add_sub_of_le hpN',hp₁,hp₂⟩

theorem chen_ap_count_lower_of_distributions {δ θ : ℝ}
    (hδ₀ : 0<δ) (hδ : δ<1/8) (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2)
    (hmargin : 1/20<chenMainMargin θ)
    (hA : ChenAPPrimeDistributionAt δ θ) (hB : ChenAPSwitchingDistributionAt δ θ) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        c*(N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^2) ≤
          ((chenAPRepresentations N r b₁ b₂).card:ℝ) :=
  chen_ap_count_lower_of_distributions_pos hδ₀ hδ hθ₁ hθ₂
    (lt_trans (by norm_num) hmargin) hA hB

theorem chen_ap_nontrivial_count_lower_of_distributions {δ θ : ℝ}
    (hδ₀ : 0<δ) (hδ : δ<1/8) (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2)
    (hmargin : 1/20<chenMainMargin θ)
    (hA : ChenAPPrimeDistributionAt δ θ) (hB : ChenAPSwitchingDistributionAt δ θ) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        c*(N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^2) ≤
          (((chenAPRepresentations N r b₁ b₂).filter (fun p => 1<N-p)).card:ℝ) :=
  chen_ap_nontrivial_count_lower_of_distributions_pos hδ₀ hδ hθ₁ hθ₂
    (lt_trans (by norm_num) hmargin) hA hB

theorem chen_ap_theorem_of_distributions {δ θ : ℝ}
    (hδ₀ : 0<δ) (hδ : δ<1/8) (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2)
    (hmargin : 1/20<chenMainMargin θ)
    (hA : ChenAPPrimeDistributionAt δ θ) (hB : ChenAPSwitchingDistributionAt δ θ) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (r b₁ b₂ : ℕ), 0<r → (r:ℝ)≤(N:ℝ)^δ →
        b₁.Coprime r → b₂.Coprime r → N%r=(b₁+b₂)%r →
        ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ 1<m ∧
          p+m=N ∧ p%r=b₁%r ∧ m%r=b₂%r :=
  chen_ap_theorem_of_distributions_pos hδ₀ hδ hθ₁ hθ₂
    (lt_trans (by norm_num) hmargin) hA hB

end FareyGoldbach
