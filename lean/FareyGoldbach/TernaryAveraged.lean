import FareyGoldbach.TernaryProgressions
import FareyGoldbach.TernaryCandidatePrimes
import FareyGoldbach.TernaryAverageBudget
import FareyGoldbach.ShortSingleAverageGoldbach

/-! # Simultaneous ternary representation on average over prescribed classes -/

open scoped BigOperators Classical

namespace FareyGoldbach

/-- A last class is bad when at least one compatible odd target in the block fails. -/
noncomputable def ternaryBadLastClasses (X r : ℕ) (b₁ b₂ : ReducedClass r) : Finset (ReducedClass r) := by
  classical
  exact (coprimeClasses r).attach.filter (fun b₃ => ¬ternaryGoodBlock X r b₁.1 b₂.1 b₃.1)

noncomputable def ternaryBadLastFraction (X r : ℕ) (b₁ b₂ : ReducedClass r) : ℝ :=
  ((ternaryBadLastClasses X r b₁ b₂).card:ℝ)/(r.totient:ℝ)

noncomputable def ternaryBadPairFraction (X r : ℕ) (b₁ : ReducedClass r) : ℝ :=
  (∑ b₂ ∈ (coprimeClasses r).attach, ((ternaryBadLastClasses X r b₁ b₂).card:ℝ))/(r.totient:ℝ)^2

private theorem marked_sum {ι : Type*} (s : Finset ι) (p : ι→Prop) [DecidablePred p]
    (f : ι→ℝ) {T : ℝ} (h₀ : ∀ i, 0≤f i) (h : ∀ i, p i → T≤f i) :
    ((s.filter p).card:ℝ)*T ≤ ∑ i ∈ s, f i := by
  calc _ = ∑ _i ∈ s.filter p, T := by rw [Finset.sum_const,nsmul_eq_mul]
       _ ≤ ∑ i ∈ s.filter p, f i := Finset.sum_le_sum (fun i hi => h i (Finset.mem_filter.mp hi).2)
       _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => h₀ i)

private theorem ternary_last_fraction_le_one {r : ℕ} (hr : 0<r) (X : ℕ) (b c : ReducedClass r) :
    ternaryBadLastFraction X r b c ≤ 1 := by
  have ht : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  apply (div_le_one ht).2
  exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (Finset.card_attach.trans (card_coprimeClasses r))

theorem ternary_bad_last_binary_bound {X r : ℕ} (hX : 4≤X) (hr : 0<r) (b c : ReducedClass r)
    (hsize : ternaryCandidateScale X r ≤ ((ternaryCandidatePrimes X r b.1).card:ℝ)) :
    let s := X/4
    ternaryBadLastFraction X r b c * ternaryCandidateScale X r ≤
      shortSingleAvgExceptions s s r hr c + shortSingleAvgExceptions (2*s) (2*s) r hr c +
      shortSingleAvgExceptions (4*s) (4*s) r hr c := by
  classical
  intro s
  let E (y : ℕ) (d : ReducedClass r) := ((shortIntervalExceptions (shortProgressions hr c d) y y).card:ℝ)
  have h := marked_sum (coprimeClasses r).attach (fun d => ¬ternaryGoodBlock X r b.1 c.1 d.1)
    (fun d => E s d+E (2*s) d+E (4*s) d)
    (fun d => by dsimp [E]; positivity) (fun d hd => hsize.trans (by
       have hh := ternaryCandidate_card_le_block_exceptions hX hr b c d hd
       dsimp only at hh
       dsimp only [E,s]
       exact_mod_cast hh))
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at h
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0≤1/(r.totient:ℝ))
  change ((ternaryBadLastClasses X r b c).card:ℝ)/(r.totient:ℝ)*ternaryCandidateScale X r ≤ _
  rw [div_eq_inv_mul,←one_div,mul_assoc]
  exact hh.trans_eq (by simp only [mul_add,shortSingleAvgExceptions,E])

theorem ternary_bad_pair_binary_bound {X r : ℕ} (hr : 0<r) (b : ReducedClass r)
    (hsize : ternaryCandidateScale X r ≤ ((ternaryCandidatePrimes X r b.1).card:ℝ)) :
    ternaryBadPairFraction X r b * ternaryCandidateScale X r ≤ doubleAvgExceptions X r hr := by
  classical
  let s := (coprimeClasses r).attach
  let E (c d : ReducedClass r) := ((exceptions (shortProgressions hr c d) X).card:ℝ)
  have hc (c : ReducedClass r) : ((ternaryBadLastClasses X r b c).card:ℝ)*ternaryCandidateScale X r ≤ ∑ d ∈ s, E c d :=
    marked_sum s (fun d => ¬ternaryGoodBlock X r b.1 c.1 d.1) (E c) (fun d => by dsimp [E]; positivity)
      (fun d hd => hsize.trans (Nat.cast_le.mpr (ternaryCandidate_card_le_exceptions_of_badBlock hr b c d hd)))
  have hh := Finset.sum_le_sum (s:=s) (fun c _ => hc c)
  rw [←Finset.sum_mul] at hh
  change ((∑ c ∈ s, ((ternaryBadLastClasses X r b c).card:ℝ))/(r.totient:ℝ)^2)*ternaryCandidateScale X r ≤ _
  rw [div_eq_inv_mul,←one_div,mul_assoc]
  exact mul_le_mul_of_nonneg_left hh (by positivity)

/-- For fixed first and second classes, the proportion of last classes with a
failure anywhere on the compatible odd block has the one-logarithm bound. -/
theorem ternary_single_average_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ {X r : ℕ} (_hr : 0<r) (b₁ b₂ : ReducedClass r), 2≤X → r≤X →
      ternaryBadLastFraction X r b₁ b₂ ≤ C*ternarySingleAverageBudget X r := by
  obtain ⟨d,hd,hcand⟩ := ternary_candidate_prime_lower_of_dirichletGRH hGRH
  obtain ⟨C,hC,hbinary⟩ := short_single_average_of_dirichletGRH hGRH
  let c := min d (1/16:ℝ)
  have hc : 0<c := lt_min hd (by norm_num)
  refine ⟨max (192*C) (2/c^2),lt_of_lt_of_le (by positivity : 0<192*C) (le_max_left _ _),?_⟩
  intro X r hr b₁ b₂ hX hrX
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have ht : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hL := one_le_log_two_mul hX
  have hl : 0<Real.log (2*(X:ℝ)) := by linarith
  have hJ : 0<(X:ℝ)/((r.totient:ℝ)^2*Real.log (2*(X:ℝ))^2) := by positivity
  have hlg := Real.log_nonneg (by linarith : 1≤2+(X:ℝ)/((r.totient:ℝ)^2*Real.log (2*(X:ℝ))^2))
  have hBud : 0≤ternarySingleAverageBudget X r := by dsimp [ternarySingleAverageBudget,ternaryDoubleAverageBudget]; positivity
  by_cases hp : (r.totient:ℝ)≤c*Real.sqrt (X:ℝ)/Real.log (2*(X:ℝ))
  · obtain ⟨h16,hr4⟩ := ternary_candidate_active hr hX hrX hc (min_le_right ..) hp
    let s := X/4
    have hs : 2≤s := by dsimp [s]; omega
    have hsr : r≤s := hr4
    have h4X : 4*s≤X := by dsimp [s]; omega
    have hpd := hp.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left ..) (Real.sqrt_nonneg _)) hl.le)
    have hh := ternary_bad_last_binary_bound (by omega : 4≤X) hr b₁ b₂ (hcand h16 hr hrX hpd b₁.1 b₁.2)
    have hlim (y : ℕ) (hy : 2≤y) (hry : r≤y) (hyX : y≤X) :
        shortSingleAvgExceptions y y r hr b₂ ≤ C*ternaryBinarySingleBudget X r :=
      (hbinary hr b₂ hy hry (by omega) le_rfl).trans (mul_le_mul_of_nonneg_left (ternary_binary_window_bound hr hy hyX) hC.le)
    have h₁ := hlim s hs hsr (by omega)
    have h₂ := hlim (2*s) (by omega) (by omega) (by omega)
    have h₃ := hlim (4*s) (by omega) (by omega) h4X
    change _ ≤ shortSingleAvgExceptions s s r hr b₂ + shortSingleAvgExceptions (2*s) (2*s) r hr b₂ +
      shortSingleAvgExceptions (4*s) (4*s) r hr b₂ at hh
    have hscale : 0<ternaryCandidateScale X r := by unfold ternaryCandidateScale; positivity
    have he : ternaryBadLastFraction X r b₁ b₂ * ternaryCandidateScale X r ≤ (3*C)*ternaryBinarySingleBudget X r := by
      linarith only [hh,h₁,h₂,h₃]
    have hdv := (le_div_iff₀ hscale).2 he
    rw [mul_div_assoc,ternary_binary_single_scale hr hX] at hdv
    exact (hdv.trans_eq (by ring : 3*C*(64*ternarySingleAverageBudget X r)=(192*C)*ternarySingleAverageBudget X r)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hBud)
  · exact (ternary_last_fraction_le_one hr X b₁ b₂).trans ((ternary_single_inactive hr hX hrX hc hp).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hBud))

/-- For a fixed first class and a modulus in the uniform prime-candidate range,
the proportion of pairs failing anywhere on the compatible odd block is bounded
by the double-average binary scale divided by the number of candidate primes. -/
theorem ternary_double_average_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ c : ℝ, 0<c ∧ ∃ C : ℝ, 0<C ∧ ∀ {X r : ℕ} (_hr : 0<r) (b₁ : ReducedClass r), 2≤X → r≤X →
      (r.totient:ℝ)≤c*Real.sqrt (X:ℝ)/Real.log (2*(X:ℝ)) →
      ternaryBadPairFraction X r b₁ ≤ C*ternaryDoubleAverageBudget X r := by
  obtain ⟨d,hd,hcand⟩ := ternary_candidate_prime_lower_of_dirichletGRH hGRH
  obtain ⟨C,hC,hbinary⟩ := double_average_of_dirichletGRH hGRH
  let c := min d (1/16:ℝ)
  have hc : 0<c := lt_min hd (by norm_num)
  refine ⟨c,hc,64*C,by positivity,?_⟩
  intro X r hr b₁ hX hrX hp
  have hl := zero_lt_one.trans_le (one_le_log_two_mul hX)
  have ht : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have h16 := (ternary_candidate_active hr hX hrX hc (min_le_right ..) hp).1
  have hpd := hp.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left ..) (Real.sqrt_nonneg _)) hl.le)
  have hh := ternary_bad_pair_binary_bound hr b₁ (hcand h16 hr hrX hpd b₁.1 b₁.2)
  have he := (hh.trans (hbinary X r hr hX hrX)).trans (mul_le_mul_of_nonneg_left (min_le_right ..) hC.le)
  have hscale : 0<ternaryCandidateScale X r := by unfold ternaryCandidateScale; positivity
  have hdv := (le_div_iff₀ hscale).2 he
  change ternaryBadPairFraction X r b₁ ≤ C*shortDoubleAvgAnalyticCap X X r/ternaryCandidateScale X r at hdv
  rw [mul_div_assoc,ternary_binary_double_scale hr hX] at hdv
  exact hdv.trans_eq (by ring)

end FareyGoldbach




