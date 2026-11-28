import FareyGoldbach.ChenPrimeAPDistributionOfGRH
import FareyGoldbach.ChenSwitchingAsymptotics

/-! # Reduction of the conditioned prime errors to the ordinary errors -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

private theorem medium_prime_not_dvd {N z y q d : ℕ}
    (hq : q ∈ chenMediumPrimes z y) (hd : d ∣ chenSiftingProduct N z) : ¬ q ∣ d := by
  obtain ⟨hqz,hqp⟩ := Finset.mem_filter.mp hq
  intro hh
  have h := Nat.mem_primeFactors.mpr ⟨hqp, hh.trans hd, fun h0 =>
    (chenSiftingProduct_squarefree N z).ne_zero h0⟩
  rw [chenSiftingProduct_primeFactors] at h
  exact (not_lt_of_ge (Finset.mem_Ico.mp hqz).1) (Finset.mem_range.mp (Finset.mem_filter.mp h).1)

/-- Among the retained medium primes and small-prime divisors, the modulus
qd has exactly one prime factor at least z. This avoids a harmonic loss
on the ordinary progression errors. -/
private theorem chenMediumError_le_reducedError_add_min {N D : ℕ} (hN : 2 ≤ N) :
    chenMediumError N D ≤
      chenReducedError N D (chenPrimeAPError N) + min ((D:ℝ)*(1+Real.log (N:ℝ)))
        ((N.primeFactors.card:ℝ)*((D/chenLowerCutoff N:ℕ):ℝ)) := by
  let z := chenLowerCutoff N
  let y := chenUpperCutoff N
  let P := chenMediumPrimes z y
  let I (q : ℕ) := (Finset.Ico 1 (D/q)).filter (fun d => d ∣ chenSiftingProduct N z)
  let S := P.sigma I
  let T := S.filter (fun p => ¬p.1 ∣ N)
  let U := S.filter (fun p => p.1 ∣ N)
  let f (p : Σ _q : ℕ, ℕ) := p.1*p.2
  let g (p : Σ _q : ℕ, ℕ) := |chenMediumAPError N p.1 p.2|
  have memI {q d : ℕ} (h : d ∈ I q) :
      1 ≤ d ∧ d < D/q ∧ d ∣ chenSiftingProduct N z := by
    obtain ⟨hi,hg⟩ := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_Ico.mp hi).1,(Finset.mem_Ico.mp hi).2,hg⟩
  have hp {q : ℕ} (hq : q ∈ P) : q.Prime := (Finset.mem_filter.mp hq).2
  have hmain : (∑ p ∈ T,g p) ≤ chenReducedError N D (chenPrimeAPError N) := by
    have hinj : Set.InjOn f T := by
      rintro ⟨q,d⟩ h₁ ⟨q',d'⟩ h₂ he
      have ⟨hq,hd⟩ := Finset.mem_sigma.mp (Finset.mem_filter.mp h₁).1
      have ⟨hq',hd'⟩ := Finset.mem_sigma.mp (Finset.mem_filter.mp h₂).1
      change q*d = q'*d' at he
      have hqd' : ¬ q ∣ d' := medium_prime_not_dvd hq (memI hd').2.2
      have hqq' : q = q' := by
        have h := (hp hq).dvd_mul.mp (show q ∣ q'*d' by rw [←he]; exact dvd_mul_right ..)
        exact ((hp hq').dvd_iff_eq (hp hq).ne_one).mp (h.resolve_right hqd') |>.symm
      subst q'
      have hdd' : d = d' := Nat.eq_of_mul_eq_mul_left (hp hq).pos he
      subst d'
      rfl
    calc
      _ = ∑ p ∈ T, |chenPrimeAPError N (f p)| := by
        apply Finset.sum_congr rfl
        intro p hpt
        have ⟨hs,hqN⟩ := Finset.mem_filter.mp hpt
        have ⟨hq,hd⟩ := Finset.mem_sigma.mp hs
        dsimp only [g,f]
        rw [chenMediumAPError_eq_primeAPError hq hqN (memI hd).2.2]
      _ = ∑ d ∈ T.image f, |chenPrimeAPError N d| := by
        rw [Finset.sum_image (fun _ h _ h' he => hinj h h' he)]
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => abs_nonneg _)
        intro a ha
        obtain ⟨p,ht,rfl⟩ := Finset.mem_image.mp ha
        have ⟨hs,hqN⟩ := Finset.mem_filter.mp ht
        have ⟨hq,hd⟩ := Finset.mem_sigma.mp hs
        obtain ⟨hd1,hdD,hdP⟩ := memI hd
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Ico.mpr ⟨Nat.mul_pos (hp hq).pos hd1,?_⟩,?_⟩
        · exact (Nat.mul_lt_mul_of_pos_left hdD (hp hq).pos).trans_le (Nat.mul_div_le D p.1)
        · exact ((hp hq).coprime_iff_not_dvd.mpr hqN).mul_left
            ((chenSiftingProduct_coprime N z).coprime_dvd_left hdP)
  have hdiscard : (∑ p∈U, g p) ≤ ∑ _p∈U, (1:ℝ) := by
    apply Finset.sum_le_sum
    intro p hpU
    obtain ⟨hs,hqN⟩ := Finset.mem_filter.mp hpU
    exact chenMediumAPError_le_one_of_dvd (hp (Finset.mem_sigma.mp hs).1) hqN _
  have hbad : (∑ p ∈ U,g p) ≤ (D:ℝ)*(1+Real.log (N:ℝ)) := by
    calc
      _ ≤ ∑ _p ∈ S, (1:ℝ) := hdiscard.trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (by intros; norm_num))
      _ = ∑ q ∈ P, ((I q).card:ℝ) := by simp [S]
      _ ≤ ∑ q ∈ P, (D:ℝ)*(1/(q:ℝ)) := by
        apply Finset.sum_le_sum
        intro q _
        rw [mul_one_div]
        apply le_trans _ Nat.cast_div_le
        exact Nat.cast_le.mpr ((Finset.card_filter_le ..).trans (by
          rw [Nat.card_Ico]; exact Nat.sub_le ..))
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg D)
        apply (Finset.sum_le_sum_of_subset_of_nonneg (t:=Finset.Icc 1 N) ?_
          (by intros; positivity)).trans (harmonic_le_one_add_log (by omega))
        intro q hq
        have hz := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).2
        exact Finset.mem_Icc.mpr ⟨(hp hq).pos,hz.le.trans
          (chenPowerLevel_le_self (a:=1/3) (by norm_num) (by omega))⟩
  have hsharp : (∑ p ∈ U,g p) ≤ (N.primeFactors.card:ℝ)*((D/z:ℕ):ℝ) := by
    have hz : 1 ≤ z := by
      apply Nat.le_floor
      exact Real.one_le_rpow (Nat.one_le_cast.mpr (by omega : 1≤N)) (by norm_num)
    have hsub : U ⊆ N.primeFactors.sigma (fun _ => Finset.Icc 1 (D/z)) := by
      intro p hpU
      obtain ⟨hpS,hdiv⟩ := Finset.mem_filter.mp hpU
      obtain ⟨hpP,hpI⟩ := Finset.mem_sigma.mp hpS
      have hqz : z≤p.1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hpP).1).1
      exact Finset.mem_sigma.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp hpP,hdiv,by omega⟩,
        Finset.mem_Icc.mpr ⟨(memI hpI).1,(memI hpI).2.1.le.trans (Nat.div_le_div_left hqz hz)⟩⟩
    calc
      _ ≤ ∑ _p ∈ U, (1:ℝ) := hdiscard
      _ = (U.card:ℝ) := by simp
      _ ≤ ((N.primeFactors.sigma (fun _ => Finset.Icc 1 (D/z))).card:ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ = _ := by simp

  have hsplit : chenMediumError N D = (∑ p ∈ T,g p) + ∑ p ∈ U,g p := by
    change (∑ q ∈ P,∑ d ∈ I q, g ⟨q,d⟩) = _
    rw [←Finset.sum_sigma P I g]
    simpa only [T,U,not_not] using (Finset.sum_filter_add_sum_filter_not S (fun p => ¬p.1 ∣ N) g).symm
  rw [hsplit]
  exact add_le_add hmain (le_min hbad hsharp)

/-- Finite medium-modulus reduction. Only prime factors of N can contribute
to the discarded fibers and each fiber has at most D/z elements. -/
theorem chenMediumError_le_reducedError_add_primeFactors {N D : ℕ} (hN : 2 ≤ N) :
    chenMediumError N D ≤ chenReducedError N D (chenPrimeAPError N) +
      (N.primeFactors.card:ℝ)*((D/chenLowerCutoff N:ℕ):ℝ) :=
  (chenMediumError_le_reducedError_add_min hN).trans (add_le_add le_rfl (min_le_right ..))

theorem chenMediumError_le_reducedError_add {N D : ℕ} (hN : 2 ≤ N) :
    chenMediumError N D ≤
      chenReducedError N D (chenPrimeAPError N) + (D : ℝ) * (1 + Real.log (N : ℝ)) :=
  (chenMediumError_le_reducedError_add_min hN).trans (add_le_add le_rfl (min_le_left ..))

theorem chen_medium_reduced_loss_small {θ ε : ℝ} (hθ : θ < 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((chenPowerLevel θ N : ℕ):ℝ) * (1+Real.log (N:ℝ))
      ≤ ε*chenLogScale N := by
  filter_upwards [chenSwitching_budget_small (β:=θ) hθ (C:=1) zero_le_one hε,
    eventually_ge_atTop (2:ℕ)] with N h hN
  have hN₁ : 1 ≤ N := by omega
  have hL₁ := one_le_chenSwitchLog hN₁
  have hL : 1+Real.log (N:ℝ) ≤ chenSwitchLog N := by
    unfold chenSwitchLog
    have hh := Real.log_le_log (x:=(N:ℝ)) (y:=2*(N:ℝ)) (by positivity) (by
      have : (0:ℝ)≤N := Nat.cast_nonneg _
      linarith)
    linarith
  calc
    _ ≤ (N:ℝ)^θ*chenSwitchLog N := by
      exact mul_le_mul (Nat.floor_le (by positivity)) hL (by positivity) (by positivity)
    _ ≤ (N:ℝ)^θ*(chenSwitchLog N)^20 :=
      mul_le_mul_of_nonneg_left (le_self_pow₀ hL₁ (by norm_num)) (by positivity)
    _ ≤ (1:ℝ)*((N:ℝ)/(chenSwitchLog N)^4+(N:ℝ)^θ*(chenSwitchLog N)^20) := by
      rw [one_mul]
      exact le_add_of_nonneg_left (by positivity)
    _ ≤ _ := h

end FareyGoldbach
