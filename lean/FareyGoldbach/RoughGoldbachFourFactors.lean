import FareyGoldbach.ChenCanonicalComparisons
import FareyGoldbach.RoughGoldbachPairSieve

/-! # The four-factor contribution to the rough P₃ count -/

open Filter
open scoped Topology Classical

namespace FareyGoldbach

/-- The four-factor members of the clean prime-complement carrier. -/
noncomputable def chenRoughThreeFourFactors (N z y : ℕ) : Finset ℕ :=
  (chenA N).filter fun m ↦
    1 < m ∧ Squarefree m ∧ IsRough z m ∧ m.primeFactorsList.length = 4 ∧ y ≤ N - m

private theorem pow_length_le_list_prod (z : ℕ) (l : List ℕ) (h : ∀ q ∈ l, z ≤ q) :
    z ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons q l ih =>
    rw [List.length_cons, pow_succ', List.prod_cons]
    exact Nat.mul_le_mul (h q (List.mem_cons_self ..))
      (ih fun r hr ↦ h r (List.mem_cons_of_mem _ hr))

/-- Five prime factors above the cutoff would already exceed `N`. -/
theorem chen_rough_three_factor_length_le_four {N z m : ℕ}
    (hm : 1 < m) (hmN : m ≤ N) (hr : IsRough z m) (hz : N < z^5) :
    m.primeFactorsList.length ≤ 4 := by
  have hz₁ : 1 ≤ z := by
    by_contra! h
    have hz₀ : z = 0 := by omega
    simp [hz₀] at hz
  have hprod := pow_length_le_list_prod z m.primeFactorsList
    (fun q hq ↦ hr q (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hq))
  rw [Nat.prod_primeFactorsList (by omega : m ≠ 0)] at hprod
  by_contra! h
  exact (not_lt_of_ge ((pow_le_pow_right₀ hz₁ (by omega : 5 ≤ m.primeFactorsList.length)).trans
    (hprod.trans hmN))) hz

private theorem length_four_list {l : List ℕ} (h : l.length = 4) :
    ∃ a b c q, l = [a, b, c, q] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨q, _ | ⟨r, tail⟩⟩⟩⟩⟩
  all_goals simp at h
  exact ⟨a, b, c, q, rfl⟩

/-- The actual factor list is increasing, and squarefreeness makes it strictly increasing. -/
theorem chen_rough_three_four_factors_sorted {m : ℕ} (hsq : Squarefree m)
    (hfour : m.primeFactorsList.length = 4) :
    ∃ a b c q, m.primeFactorsList = [a, b, c, q] ∧ a < b ∧ b < c ∧ c < q := by
  obtain ⟨a, b, c, q, hl⟩ := length_four_list hfour
  have hle := (Nat.primeFactorsList_sorted m).pairwise
  have hne := hsq.nodup_primeFactorsList
  rw [hl] at hle hne
  simp [List.pairwise_cons] at hle hne
  obtain ⟨hab, hbc, hcq⟩ : a ≤ b ∧ b ≤ c ∧ c ≤ q := by tauto
  obtain ⟨hab', hbc', hcq'⟩ : a ≠ b ∧ b ≠ c ∧ c ≠ q := by tauto
  exact ⟨a, b, c, q, hl, by omega, by omega, by omega⟩

private noncomputable def fourFactorWindow (lo hi : ℝ) (N : ℕ) : Finset ℕ :=
  (chenPowerLevel hi N).primesLE \ (chenPowerLevel lo N).primesLE

private theorem fourFactorWindow_mem {lo hi : ℝ} {N q : ℕ} (hprime : q.Prime)
    (hlo : (N:ℝ)^lo < q) (hhi : (q:ℝ) ≤ (N:ℝ)^hi) :
    q ∈ fourFactorWindow lo hi N := by
  refine Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hhi, hprime⟩, ?_⟩
  intro hq
  have hqlo := (Nat.mem_primesLE.mp hq).1
  exact (not_le_of_gt hlo) ((Nat.cast_le.mpr hqlo).trans (Nat.floor_le (by positivity)))

private theorem fourFactorWindow_prime {lo hi : ℝ} {N q : ℕ}
    (hq : q ∈ fourFactorWindow lo hi N) : q.Prime :=
  (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hq).1).2

private theorem fourFactorWindow_reciprocal_tendsto {lo hi : ℝ} (hlo : 0 < lo) (hlhi : lo < hi) :
    Tendsto (fun N : ℕ ↦ ∑ q ∈ fourFactorWindow lo hi N, 1/(q:ℝ)) atTop
      (𝓝 (Real.log (hi / lo))) := by
  have hhi := hlo.trans hlhi
  obtain ⟨B, hM⟩ := chen_prime_reciprocal_mertens
  have hloTop := (tendsto_rpow_atTop hlo).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hhiTop := (tendsto_rpow_atTop hhi).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlim := ((hM.comp hhiTop).sub (hM.comp hloTop)).add
    (tendsto_const_nhds (x := Real.log (hi / lo)))
  rw [sub_self, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN₁ : (1:ℝ) < N := Nat.one_lt_cast.mpr hN
  have hlog := Real.log_pos hN₁
  have hpow := Real.rpow_le_rpow_of_exponent_le hN₁.le hlhi.le
  have hsub : (chenPowerLevel lo N).primesLE ⊆ (chenPowerLevel hi N).primesLE :=
    fun q hq ↦ Nat.mem_primesLE.mpr
      ⟨(Nat.mem_primesLE.mp hq).1.trans (Nat.floor_mono hpow), (Nat.mem_primesLE.mp hq).2⟩
  have hsum := Finset.sum_sdiff hsub (f := fun q : ℕ ↦ (1:ℝ)/(q:ℝ))
  have hlogs : Real.log (Real.log ((N:ℝ)^hi)) - Real.log (Real.log ((N:ℝ)^lo)) =
      Real.log (hi / lo) := by
    rw [Real.log_rpow hNp, Real.log_rpow hNp, Real.log_mul hhi.ne' hlog.ne',
      Real.log_mul hlo.ne' hlog.ne', Real.log_div hhi.ne' hlo.ne']
    ring
  change ((∑ q ∈ (chenPowerLevel hi N).primesLE, 1/(q:ℝ)) - Real.log (Real.log ((N:ℝ)^hi))) -
    ((∑ q ∈ (chenPowerLevel lo N).primesLE, 1/(q:ℝ)) - Real.log (Real.log ((N:ℝ)^lo))) +
      Real.log (hi / lo) = _
  unfold fourFactorWindow
  linarith only [hsum, hlogs]

private theorem fourFactorWindow_reciprocal_le {ε : ℝ} (hε : 0 < ε)
    (hε₀ : ε < (1:ℝ)/524288) :
    let lo : ℝ := 1/4 - ε - ε/12
    ∀ᶠ N : ℕ in atTop,
      (∑ q ∈ fourFactorWindow lo (1 - 3*lo) N, 1/(q:ℝ)) ≤ 20*ε := by
  dsimp only
  let lo : ℝ := 1/4 - ε - ε/12
  let hi : ℝ := 1 - 3*lo
  have hlo : 0 < lo := by dsimp [lo]; linarith
  have hdiff : hi - lo = (13/3)*ε := by dsimp [hi, lo]; ring
  have hlhi : lo < hi := by linarith
  have hratio : hi / lo - 1 < 20*ε := by
    have hlower : (13/3:ℝ) < 20*lo := by dsimp [lo]; linarith
    have hmul := mul_lt_mul_of_pos_right hlower hε
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hlo]
    nlinarith only [hmul, hdiff]
  have hlim := fourFactorWindow_reciprocal_tendsto hlo hlhi
  have hlog := Real.log_le_sub_one_of_pos (div_pos (hlo.trans hlhi) hlo)
  exact (hlim.eventually_lt_const (hlog.trans_lt hratio)).mono (fun _ h ↦ h.le)

private theorem prime_list_four_mem_window {lo : ℝ} {N z m a b c q : ℕ}
    (hN : 0 < N) (hm : 1 < m) (hmN : m ≤ N) (hr : IsRough z m)
    (hl : m.primeFactorsList = [a, b, c, q]) (h₁ : a < b) (h₂ : b < c) (h₃ : c < q)
    (hzlo : (N:ℝ)^lo + 1 ≤ z) :
    (∀ r ∈ [a, b, c, q], r ∈ fourFactorWindow lo (1-3*lo) N) ∧ m = a*b*c*q := by
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hfactor (r : ℕ) (hrl : r ∈ [a, b, c, q]) : r.Prime ∧ z ≤ r := by
    have hrl' : r ∈ m.primeFactorsList := by rwa [hl]
    exact ⟨Nat.prime_of_mem_primeFactorsList hrl', hr r (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hrl')⟩
  have hprod := Nat.prod_primeFactorsList (by omega : m ≠ 0)
  rw [hl] at hprod
  have hmprod : m = a*b*c*q := by simpa [List.prod_cons, mul_assoc] using hprod.symm
  have hlow (r : ℕ) (hrl : r ∈ [a, b, c, q]) : (N:ℝ)^lo < r := by
    have hz : (z:ℝ) ≤ r := Nat.cast_le.mpr (hfactor r hrl).2
    linarith
  have hprodreal : (m:ℝ) = (a:ℝ)*(b:ℝ)*(c:ℝ)*(q:ℝ) := by exact_mod_cast hmprod
  have hmul : (N:ℝ)^lo * (N:ℝ)^lo * (N:ℝ)^lo * (q:ℝ) ≤ m := by
    rw [hprodreal]
    gcongr
    · exact (hlow a (by simp)).le
    · exact (hlow b (by simp)).le
    · exact (hlow c (by simp)).le
  have hpow : (N:ℝ)^lo * (N:ℝ)^lo * (N:ℝ)^lo = (N:ℝ)^(3*lo) := by
    rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]
    congr 1
    ring
  have htop : (q:ℝ) ≤ (N:ℝ)^(1-3*lo) := by
    have hmul' : (N:ℝ)^(3*lo) * (q:ℝ) ≤ (N:ℝ)^(3*lo) * (N:ℝ)^(1-3*lo) := calc
      _ ≤ (m:ℝ) := by rw [← hpow]; exact hmul
      _ ≤ (N:ℝ) := Nat.cast_le.mpr hmN
      _ ≤ _ := by
        rw [← Real.rpow_add hNp, show 3*lo + (1-3*lo) = 1 by ring, Real.rpow_one]
    exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hNp (3*lo))).mp hmul'
  refine ⟨fun r hrl ↦ fourFactorWindow_mem (hfactor r hrl).1 (hlow r hrl)
    ((Nat.cast_le.mpr (show r ≤ q by simp only [List.mem_cons, List.not_mem_nil, or_false] at hrl; omega)).trans htop),
    hmprod⟩

/-- The small-prime cutoff stays below the roughness cutoff, whose fifth power exceeds `N`. -/
theorem eventually_rough_three_cutoff_geometry {ε : ℝ} (hε₀ : ε < (1:ℝ)/524288) :
    ∀ᶠ N : ℕ in atTop,
      chenPowerLevel (1/512) N + 1 ≤ chenPowerLevel (1/4-ε) N ∧
      N < (chenPowerLevel (1/4-ε) N)^5 := by
  have hcut := eventually_rpow_add_one_le_powerLevel (a:=1/512) (b:=1/4-ε)
    (by norm_num) (by linarith)
  have hpow := eventually_rpow_add_one_le_powerLevel (a:=1/5) (b:=1/4-ε)
    (by norm_num) (by linarith)
  filter_upwards [hcut, hpow] with N hc hp
  refine ⟨?_, ?_⟩
  · have hf : (chenPowerLevel (1/512) N:ℝ) ≤ (N:ℝ)^(1/512:ℝ) := Nat.floor_le (by positivity)
    exact_mod_cast (show (chenPowerLevel (1/512) N:ℝ) + 1 ≤ (chenPowerLevel (1/4-ε) N:ℝ) by linarith)
  · have hlt : (N:ℝ)^(1/5:ℝ) < (chenPowerLevel (1/4-ε) N:ℝ) := by linarith
    have hp := pow_lt_pow_left₀ hlt (by positivity : 0 ≤ (N:ℝ)^(1/5:ℝ)) (by decide : 5 ≠ 0)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)] at hp
    norm_num at hp
    exact_mod_cast hp

private theorem fourFactors_count_of_window {lo C : ℝ} {N z y : ℕ}
    (hN : 0 < N) (hyz : y ≤ z) (hzlo : (N:ℝ)^lo + 1 ≤ z) (hC : 0 ≤ C)
    (hpair : ∀ d : ℕ, 0 < d → z ≤ N/d → (∀ ℓ : ℕ, ℓ.Prime → ℓ < y → ¬ ℓ ∣ d) →
      ((chenRoughThreePrimePairs N d y).card:ℝ) ≤ C / (d:ℝ)) :
    ((chenRoughThreeFourFactors N z y).card:ℝ) ≤
      C * (∑ q ∈ fourFactorWindow lo (1-3*lo) N, 1/(q:ℝ))^3 := by
  classical
  let P := fourFactorWindow lo (1-3*lo) N
  let triples := P ×ˢ (P ×ˢ P)
  let prod (t : ℕ × ℕ × ℕ) := t.1 * t.2.1 * t.2.2
  let T := triples.filter (fun t ↦ z ≤ t.1 ∧ z ≤ t.2.1 ∧ z ≤ t.2.2 ∧ z ≤ N / prod t)
  let S (d : ℕ) := chenRoughThreePrimePairs N d y
  let carrier (t : ℕ × ℕ × ℕ) := (S (prod t)).image (fun q ↦ prod t * q)
  have hsub : chenRoughThreeFourFactors N z y ⊆ T.biUnion carrier := by
    intro m hm
    obtain ⟨ha, hm₁, hsq, hr, hlen, hpy⟩ := Finset.mem_filter.mp hm
    obtain ⟨hb, hp⟩ := Finset.mem_filter.mp ha
    have hmN := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    obtain ⟨a, b, c, q, hl, hab, hbc, hcq⟩ := chen_rough_three_four_factors_sorted hsq hlen
    obtain ⟨hw, hprod⟩ := prime_list_four_mem_window hN hm₁ hmN hr hl hab hbc hcq hzlo
    have hP (r : ℕ) (hrl : r ∈ [a, b, c, q]) : r ∈ P := hw r hrl
    have hz (r : ℕ) (hrl : r ∈ [a, b, c, q]) : z ≤ r :=
      hr r (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr (by rwa [hl]))
    have hd : 0 < a*b*c :=
      Nat.mul_pos (Nat.mul_pos (fourFactorWindow_prime (hP a (by simp))).pos
        (fourFactorWindow_prime (hP b (by simp))).pos) (fourFactorWindow_prime (hP c (by simp))).pos
    have hqN : q ≤ N / (a*b*c) :=
      (Nat.le_div_iff_mul_le hd).mpr (by rw [mul_comm, ← hprod]; exact hmN)
    refine Finset.mem_biUnion.mpr ⟨(a,b,c), ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hP a (by simp), Finset.mem_product.mpr ⟨hP b (by simp), hP c (by simp)⟩⟩,
          hz a (by simp), hz b (by simp), hz c (by simp), (hz q (by simp)).trans hqN⟩
    · apply Finset.mem_image.mpr
      refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hyz.trans (hz q (by simp)), hqN⟩,
        fourFactorWindow_prime (hP q (by simp)), ?_, ?_⟩, hprod.symm⟩
      · change y ≤ N - a*b*c*q
        simpa only [← hprod] using hpy
      · change (N - a*b*c*q).Prime
        simpa only [← hprod] using hp
  have hcard : (chenRoughThreeFourFactors N z y).card ≤ ∑ t ∈ T, (S (prod t)).card :=
    (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum (fun _ _ ↦ Finset.card_image_le)))
  have hpair' (t : ℕ × ℕ × ℕ) (ht : t ∈ T) :
      ((S (prod t)).card:ℝ) ≤ C/(prod t:ℝ) := by
    obtain ⟨htr, ha, hb, hc, hdiv⟩ := Finset.mem_filter.mp ht
    have hparts : t.1 ∈ P ∧ t.2.1 ∈ P ∧ t.2.2 ∈ P := by
      simpa only [triples, Finset.mem_product] using htr
    obtain ⟨h₁, h₂, h₃⟩ := hparts
    have hp₁ := fourFactorWindow_prime (show t.1 ∈ P from h₁)
    have hp₂ := fourFactorWindow_prime (show t.2.1 ∈ P from h₂)
    have hp₃ := fourFactorWindow_prime (show t.2.2 ∈ P from h₃)
    refine hpair (prod t) (Nat.mul_pos (Nat.mul_pos hp₁.pos hp₂.pos) hp₃.pos) hdiv ?_
    intro ℓ hℓ hly hdvd
    change ℓ ∣ t.1 * t.2.1 * t.2.2 at hdvd
    rcases hℓ.dvd_mul.mp hdvd with h | h
    · rcases hℓ.dvd_mul.mp h with h | h
      · have heq := (Nat.prime_dvd_prime_iff_eq hℓ hp₁).mp h
        omega
      · have heq := (Nat.prime_dvd_prime_iff_eq hℓ hp₂).mp h
        omega
    · have heq := (Nat.prime_dvd_prime_iff_eq hℓ hp₃).mp h
      omega
  let w (q : ℕ) : ℝ := 1/(q:ℝ)
  have hsums : (∑ t ∈ triples, ((w t.1 * w t.2.1) * w t.2.2)) = (∑ q ∈ P, w q)^3 := by
    simp only [triples, Finset.sum_product, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  calc
    _ ≤ ∑ t ∈ T, ((S (prod t)).card:ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ t ∈ T, C/(prod t:ℝ) := Finset.sum_le_sum hpair'
    _ ≤ ∑ t ∈ triples, C/(prod t:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
        (fun t _ _ ↦ div_nonneg hC (Nat.cast_nonneg (prod t)))
    _ = C * (∑ t ∈ triples, ((w t.1 * w t.2.1) * w t.2.2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      simp only [prod, w, Nat.cast_mul, one_div]
      ring
    _ = _ := by rw [hsums]

/-- The uniform bound on prime pairs gives a cubic loss in the short factor window. -/
theorem chen_rough_three_four_count_upper {ε : ℝ} (hε : 0 < ε)
    (hε₀ : ε < (1:ℝ)/524288) :
    ∀ᶠ N : ℕ in atTop, Even N →
      let z := chenPowerLevel (1/4-ε) N
      let y := chenPowerLevel (1/512) N + 1
      ((chenRoughThreeFourFactors N z y).card:ℝ) ≤
        (2:ℝ)^35 * ε^3 * chenSieveScale chenCanonicalU N := by
  let lo : ℝ := 1/4 - ε - ε/12
  have hlo : 0 ≤ lo := by dsimp [lo]; linarith
  have hlo' : lo < 1/4 - ε := by dsimp [lo]; linarith
  have hcut := eventually_rpow_add_one_le_powerLevel hlo hlo'
  have hwindow := fourFactorWindow_reciprocal_le hε hε₀
  have hU := eventually_inf_principal.mp chenCanonicalU_eventually_ge_half
  have hpair := chen_rough_three_pair_count_upper hε₀
  filter_upwards [hpair, hcut, hwindow, hU, eventually_rough_three_cutoff_geometry hε₀,
    eventually_ge_atTop (1 : ℕ)] with N hp hzlo hw hu hg hN
  intro he
  have hu₀ : 0 ≤ chenCanonicalU N := le_trans (by norm_num) (hu he)
  have hscale : 0 ≤ chenSieveScale chenCanonicalU N := by unfold chenSieveScale; positivity
  have hC : 0 ≤ (2:ℝ)^22 * chenSieveScale chenCanonicalU N := by positivity
  have hraw := fourFactors_count_of_window (by omega : 0 < N) hg.1 hzlo hC (hp he)
  have hsum : 0 ≤ ∑ q ∈ fourFactorWindow lo (1-3*lo) N, 1/(q:ℝ) :=
    Finset.sum_nonneg (fun _ _ ↦ by positivity)
  have hpow := pow_le_pow_left₀ hsum hw 3
  apply hraw.trans
  calc
    _ ≤ ((2:ℝ)^22 * chenSieveScale chenCanonicalU N) * (20*ε)^3 :=
      mul_le_mul_of_nonneg_left hpow hC
    _ ≤ _ := by
      have hn : (2:ℝ)^22 * 20^3 ≤ (2:ℝ)^35 := by norm_num
      calc
        _ = ((2:ℝ)^22 * 20^3) * (ε^3 * chenSieveScale chenCanonicalU N) := by ring
        _ ≤ (2:ℝ)^35 * (ε^3 * chenSieveScale chenCanonicalU N) :=
          mul_le_mul_of_nonneg_right hn (by positivity)
        _ = _ := by ring

end FareyGoldbach
