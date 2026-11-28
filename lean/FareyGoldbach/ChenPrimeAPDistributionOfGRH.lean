import FareyGoldbach.ChenUnconditionalComparisons
import FareyGoldbach.SharpPrimeCount
import FareyGoldbach.PrimeSums

/-! # Prime progression distribution for the Chen sieve -/

namespace FareyGoldbach

open Filter
open scoped Topology Classical

/-- Reflection in the Chen carrier, including the endpoint prime at N. -/
theorem chenDivisible_card_eq_progression (N d : ℕ) :
    (chenDivisible (chenA N) d).card =
      (N.primesLE.filter (fun p => p % d = N % d)).card := by
  apply Finset.card_bij' (fun a _ => N-a) (fun p _ => N-p)
  · intro a ha
    obtain ⟨ha,hd⟩ := Finset.mem_filter.mp ha
    obtain ⟨hr,hp⟩ := Finset.mem_filter.mp ha
    have hle : a≤N := by have := Finset.mem_range.mp hr; omega
    refine Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.sub_le ..,hp⟩,?_⟩
    apply (Nat.modEq_iff_dvd' (Nat.sub_le N a)).mpr
    rwa [Nat.sub_sub_self hle]
  · intro p hp
    obtain ⟨hp,hm⟩ := Finset.mem_filter.mp hp
    obtain ⟨hle,hprime⟩ := Nat.mem_primesLE.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      by rwa [Nat.sub_sub_self hle]⟩,(Nat.modEq_iff_dvd' hle).mp hm⟩
  · intro a ha
    apply Nat.sub_sub_self
    have := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
    omega
  · intro p hp
    exact Nat.sub_sub_self (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1

theorem chenMedium_coprime_modulus {N z y q d : ℕ}
    (hq : q∈chenMediumPrimes z y) (hd : d∣chenSiftingProduct N z) : q.Coprime d := by
  obtain ⟨hqi,hqp⟩ := Finset.mem_filter.mp hq
  have hqz := (Finset.mem_Ico.mp hqi).1
  apply Nat.Coprime.of_dvd_right hd
  unfold chenSiftingProduct
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  obtain ⟨hpz,hpp,_⟩ := Finset.mem_filter.mp hp
  exact (Nat.coprime_primes hqp hpp).mpr (by have := Finset.mem_range.mp hpz; omega)

theorem chenDivisible_twice {q d : ℕ} (hd : q.Coprime d) (A : Finset ℕ) :
    chenDivisible (chenDivisible A q) d = chenDivisible A (q*d) := by
  ext a
  simp only [chenDivisible,Finset.mem_filter]
  exact ⟨fun h => ⟨h.1.1,hd.mul_dvd_of_dvd_of_dvd h.1.2 h.2⟩,
    fun h => ⟨⟨h.1,(Nat.dvd_mul_right q d).trans h.2⟩,(Nat.dvd_mul_left d q).trans h.2⟩⟩

/-- An omitted prime can only count its own reflection. -/
theorem chenMediumAPError_le_one_of_dvd {N q : ℕ} (hq : q.Prime) (hN : q∣N) (d : ℕ) :
    |chenMediumAPError N q d|≤1 := by
  have hsub : chenDivisible (chenDivisible (chenA N) q) d ⊆ {N-q} := by
    intro a ha
    obtain ⟨ha,_⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha,hqa⟩ := Finset.mem_filter.mp ha
    obtain ⟨hp,hp'⟩ := Finset.mem_filter.mp ha
    have hle : a≤N := by have := Finset.mem_range.mp hp; omega
    have hq' : N-a=q := (hp'.dvd_iff_eq hq.ne_one).mp (Nat.dvd_sub hN hqa)
    exact Finset.mem_singleton.mpr (by omega)
  have hcard : (chenDivisible (chenDivisible (chenA N) q) d).card≤1 :=
    (Finset.card_le_card hsub).trans_eq (Finset.card_singleton _)
  simpa [chenMediumAPError,chenAPError,chenMediumMass,hN] using
    (Nat.cast_le (α:=ℝ)).mpr hcard

/-- For a retained medium prime the count and its main term both have modulus qd. -/
theorem chenMediumAPError_eq_primeAPError {N z y q d : ℕ} (hqm : q∈chenMediumPrimes z y)
    (hqN : ¬q∣N) (hd : d∣chenSiftingProduct N z) :
    chenMediumAPError N q d = chenPrimeAPError N (q*d) := by
  have hc := chenMedium_coprime_modulus hqm hd
  simp only [chenMediumAPError,chenPrimeAPError,chenAPError,chenMediumMass,ite_eq_right hqN,
    chenDivisible_twice hc,Nat.totient_mul hc,Nat.cast_mul,div_div]

theorem sum_filtered_Ico_abs_le {D : ℕ} (P : ℕ→Prop) [DecidablePred P]
    (E : ℝ) (hE : 0≤E) (err : ℕ→ℝ)
    (h : ∀ d∈(Finset.Ico 1 D).filter P, |err d|≤E) :
    (∑ d∈(Finset.Ico 1 D).filter P, |err d|) ≤ (D:ℝ)*E := by
  apply (Finset.sum_le_sum h).trans
  rw [Finset.sum_const,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hE
  exact Nat.cast_le.mpr ((Finset.card_filter_le ..).trans
    (by rw [Nat.card_Ico]; exact Nat.sub_le ..))

private theorem chenDistribution_finite {N D : ℕ} (hN : 2≤N) (hD : D≤N) {E : ℝ} (hE : 1≤E)
    (hAP : ∀ d : ℕ, 0<d → d≤N → d.Coprime N → |chenPrimeAPError N d|≤E) :
    chenReducedError N D (chenPrimeAPError N) ≤ (D:ℝ)*E ∧
    chenMediumError N D ≤ (D:ℝ)*E*(1+Real.log (N:ℝ)) := by
  have h₀ : 0≤E := zero_le_one.trans hE
  refine ⟨sum_filtered_Ico_abs_le _ _ h₀ _ ?_,?_⟩
  · intro d hd
    obtain ⟨hI,hcop⟩ := Finset.mem_filter.mp hd
    obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hI
    exact hAP _ hl (hu.le.trans hD) hcop
  · let z := chenLowerCutoff N
    let y := chenUpperCutoff N
    have hsum (q : ℕ) (hq : q∈chenMediumPrimes z y) :
        (∑ d∈(Finset.Ico 1 (D/q)).filter (fun d => d∣chenSiftingProduct N z),
          |chenMediumAPError N q d|) ≤ (D:ℝ)*E*(1/(q:ℝ)) := by
      have hqp := (Finset.mem_filter.mp hq).2
      apply (sum_filtered_Ico_abs_le _ _ h₀ _ ?_).trans
      · have hfloor : ((D/q:ℕ):ℝ)≤(D:ℝ)/(q:ℝ) := Nat.cast_div_le
        calc _ ≤ (D:ℝ)/(q:ℝ)*E := mul_le_mul_of_nonneg_right hfloor h₀
             _ = _ := by ring
      · intro d hd
        obtain ⟨hI,hdP⟩ := Finset.mem_filter.mp hd
        obtain ⟨hd₀,hdD⟩ := Finset.mem_Ico.mp hI
        by_cases hqN : q∣N
        · exact (chenMediumAPError_le_one_of_dvd hqp hqN d).trans hE
        · rw [chenMediumAPError_eq_primeAPError hq hqN hdP]
          apply hAP _ (Nat.mul_pos hqp.pos hd₀)
          · exact (Nat.mul_le_mul_left q hdD.le).trans
              ((Nat.mul_div_le D q).trans hD)
          · exact (hqp.coprime_iff_not_dvd.mpr hqN).mul_left
              ((chenSiftingProduct_coprime N z).coprime_dvd_left hdP)
    have hsub : chenMediumPrimes z y ⊆ Finset.Icc 1 N := by
      intro q hq
      obtain ⟨hqi,hqp⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_Icc.mpr ⟨hqp.pos,(Finset.mem_Ico.mp hqi).2.le.trans
        (chenPowerLevel_le_self (a:=1/3) (by norm_num) (by omega))⟩
    have hh : (∑ q∈chenMediumPrimes z y,1/(q:ℝ)) ≤ 1+Real.log (N:ℝ) :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
        (harmonic_le_one_add_log (by omega))
    apply (Finset.sum_le_sum hsum).trans
    rw [←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hh (by positivity)

/-- The sum over conditioned moduli costs at most one harmonic sum. At any fixed
power below one half, its extra logarithm is absorbed by the remaining power. -/
theorem chenPowerLevel_allErrors_small {θ C ε : ℝ} (hθ : θ<1/2)
    (hC : 0≤C) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,
      (chenPowerLevel θ N:ℝ)*(C*Real.sqrt (N:ℝ)*Real.log (2*(N:ℝ))^2)*
        (1+Real.log (N:ℝ)) ≤ ε*chenLogScale N := by
  have h := (isLittleO_log_rpow_rpow_atTop 5 (show 0<1/2-θ by linarith)).tendsto_div_nhds_zero
  have hlim : Tendsto (fun x : ℝ => (8*C)*(Real.log x^5/x^(1/2-θ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat,mul_zero] using h.const_mul (8*C)
  have hn := hlim.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hL := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [hn.eventually_lt_const hε,hL,eventually_ge_atTop (2:ℕ)] with N ht hL hN
  have hNr : (2:ℝ)≤N := by exact_mod_cast hN
  have hNp : (0:ℝ)<N := by linarith
  change 1≤Real.log (N:ℝ) at hL
  have hLp : 0<Real.log (N:ℝ) := by linarith
  have ht₀ : (8*C)*(Real.log (N:ℝ)^5) ≤ ε*(N:ℝ)^(1/2-θ) := by
    change (8*C)*(Real.log (N:ℝ)^5/(N:ℝ)^(1/2-θ))<ε at ht
    rw [← mul_div_assoc] at ht
    exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hNp _)).mp ht).le
  have h2L : Real.log (2*(N:ℝ))≤2*Real.log (N:ℝ) := by
    rw [Real.log_mul (by norm_num) hNp.ne']
    linarith only [Real.log_le_log (by norm_num : (0:ℝ)<2) hNr]
  have hlog0 : 0≤Real.log (2*(N:ℝ)) := Real.log_nonneg (by linarith)
  have hlev : (chenPowerLevel θ N:ℝ)≤(N:ℝ)^θ := Nat.floor_le (Real.rpow_nonneg hNp.le _)
  unfold chenLogScale
  rw [←mul_div_assoc]
  apply (le_div_iff₀ (pow_pos hLp 2)).mpr
  calc
    _ ≤ ((N:ℝ)^θ)*(C*Real.sqrt (N:ℝ)*(2*Real.log (N:ℝ))^2)*
          (2*Real.log (N:ℝ))*Real.log (N:ℝ)^2 := by
            gcongr
            linarith
    _ = (N:ℝ)^θ*Real.sqrt (N:ℝ)*(8*C*Real.log (N:ℝ)^5) := by ring
    _ ≤ (N:ℝ)^θ*Real.sqrt (N:ℝ)*(ε*(N:ℝ)^(1/2-θ)) :=
      mul_le_mul_of_nonneg_left ht₀ (by positivity)
    _ = ε*(N:ℝ) := by
      rw [Real.sqrt_eq_rpow]
      calc _ = ε*(((N:ℝ)^θ*(N:ℝ)^(1/2:ℝ))*(N:ℝ)^(1/2-θ)) := by ring
           _ = _ := by rw [←Real.rpow_add hNp,←Real.rpow_add hNp,show θ+1/2+(1/2-θ)=(1:ℝ) by ring,Real.rpow_one]

/-- The two standard prime-counting estimates suffice for the ordinary and
medium-prime distribution hypotheses at every fixed power below one half. -/
theorem chenPrimeAPDistribution_of_progression_bounds
    (hPNT : Tendsto (fun N : ℕ => (N.primeCounting:ℝ)/((N:ℝ)/Real.log (N:ℝ))) atTop (𝓝 1))
    (hAP : ∃ C : ℝ, 0<C ∧ ∀ {N d a : ℕ}, 2≤N → 0<d → d≤N → a.Coprime d →
      |((N.primesLE.filter (fun p => p%d=a%d)).card:ℝ)-(N.primeCounting:ℝ)/(d.totient:ℝ)| ≤
        C*Real.sqrt (N:ℝ)*Real.log (2*(N:ℝ))^2) : ChenPrimeAPDistribution := by
  obtain ⟨C,hC,hAP⟩ := hAP
  intro θ _ hθ
  refine ⟨by simpa only [chenA_card_eq_primeCounting] using hPNT,?_⟩
  intro ε hε
  have hL := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [chenPowerLevel_allErrors_small hθ (C:=C+1) (by linarith) hε,hL,
    eventually_ge_atTop (2:ℕ)] with N hsmall hlog hN _
  change 1≤Real.log (N:ℝ) at hlog
  have hNr : (2:ℝ)≤N := by exact_mod_cast hN
  have hs : 1≤Real.sqrt (N:ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hlog' : 1≤Real.log (2*(N:ℝ)) :=
    hlog.trans (Real.log_le_log (by linarith) (by linarith))
  let E := (C+1)*Real.sqrt (N:ℝ)*Real.log (2*(N:ℝ))^2
  have hE : 1≤E := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by linarith) hs) (one_le_pow₀ hlog')
  have hb := chenDistribution_finite (D:=chenPowerLevel θ N) hN
    (chenPowerLevel_le_self (by linarith) (by omega)) hE (by
      intro d hd hdN hc
      unfold chenPrimeAPError chenAPError
      rw [chenDivisible_card_eq_progression,chenA_card_eq_primeCounting]
      apply (hAP hN hd hdN hc.symm).trans
      unfold E
      gcongr
      linarith)
  have hlarge : 1≤1+Real.log (N:ℝ) := by linarith
  exact ⟨(hb.1.trans (le_mul_of_one_le_right (by positivity) hlarge)).trans hsmall,hb.2.trans hsmall⟩

/-- Character estimates imply both prime-distribution bounds at every
fixed exponent strictly below one half. -/
theorem chenPrimeAPDistribution_of_twistBound (h : SharpVonMangoldtTwistBound) :
    ChenPrimeAPDistribution :=
  chenPrimeAPDistribution_of_progression_bounds (primeCounting_ratio_of_twistBound h)
    (primeAP_count_of_twistBound h)

/-- Dirichlet GRH supplies the prime and conditioned-prime distributions at
every fixed Chen level strictly below the square root. -/
theorem chenPrimeAPDistribution_of_dirichletGRH (hGRH : DirichletGRH) : ChenPrimeAPDistribution :=
  chenPrimeAPDistribution_of_progression_bounds (primeCounting_ratio_of_dirichletGRH hGRH)
    (primeAP_count_of_dirichletGRH hGRH)

/-- The remaining arithmetic input at the switching stage is the distribution
of the reflected three-prime products. -/
theorem chen_count_lower_of_dirichletGRH_and_switching (hGRH : DirichletGRH)
    (hB : ChenSwitchingDistribution) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      c*(N:ℝ)/Real.log (N:ℝ)^2 ≤ (chenCount N:ℝ) :=
  chen_count_lower_of_distributions (chenPrimeAPDistribution_of_dirichletGRH hGRH) hB

theorem chen_theorem_of_dirichletGRH_and_switching (hGRH : DirichletGRH)
    (hB : ChenSwitchingDistribution) :
    ∀ᶠ N : ℕ in atTop, Even N → ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ p+m=N :=
  chen_theorem_of_distributions (chenPrimeAPDistribution_of_dirichletGRH hGRH) hB

end FareyGoldbach
