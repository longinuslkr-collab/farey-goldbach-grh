import FareyGoldbach.ShortDoubleAverageGoldbach

/-! # Exact specialization to even integers at modulus one -/

open Filter
open scoped BigOperators Classical Topology

namespace FareyGoldbach

/-- Even integers in the translated window. -/
noncomputable def shortEvenIntegers (X Δ : ℕ) : Finset ℕ :=
  (Finset.Ioc X (X+Δ)).filter Even

/-- Binary Goldbach exceptions among the even integers in the translated window. -/
noncomputable def shortGoldbachExceptions (X Δ : ℕ) : Finset ℕ := by
  classical
  exact (shortEvenIntegers X Δ).filter (fun n => ¬∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n)

theorem card_shortEvenIntegers (X Δ : ℕ) :
    (shortEvenIntegers X Δ).card = (X+Δ)/2-X/2 := by
  have heq : shortEvenIntegers X Δ =
      (Finset.Ioc (X/2) ((X+Δ)/2)).image (fun j => 2*j) := by
    ext n
    simp only [shortEvenIntegers,Finset.mem_filter,Finset.mem_Ioc,Finset.mem_image]
    constructor
    · rintro ⟨⟨hx,hy⟩,j,hj⟩
      exact ⟨j,⟨by omega,by omega⟩,by omega⟩
    · rintro ⟨j,⟨hx,hy⟩,rfl⟩
      exact ⟨⟨by omega,by omega⟩,j,by omega⟩
  rw [heq,Finset.card_image_of_injective _ (by intro a b h; dsimp at h; omega)]
  simp

private def unitProgressions : Progressions :=
  ⟨1,by decide,0,0,by decide,by decide,by decide,by decide⟩

private theorem no_unit_rep_iff (n : ℕ) :
    (primeRepresentations unitProgressions n).card=0 ↔
      ¬∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n := by
  classical
  rw [Finset.card_eq_zero]
  constructor
  · rintro he ⟨p,q,hp,hq,hs⟩
    have hm : (p,q) ∈ primeRepresentations unitProgressions n := by
      refine Finset.mem_filter.mpr ⟨?_,hp,hq,hs,Nat.mod_one _,Nat.mod_one _⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le,by omega⟩,
        Finset.mem_Icc.mpr ⟨hq.two_le,by omega⟩⟩
    exact Finset.notMem_empty _ (he ▸ hm)
  · intro he
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨p,q⟩ hm
    have hf := (Finset.mem_filter.mp hm).2
    exact he ⟨p,q,hf.1,hf.2.1,hf.2.2.1⟩

private theorem unit_exceptions_eq (X Δ : ℕ) :
    shortIntervalExceptions unitProgressions X Δ = shortGoldbachExceptions X Δ := by
  ext n
  simp only [shortIntervalExceptions,exceptions,shortGoldbachExceptions,shortEvenIntegers,
    Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc,unitProgressions,Nat.mod_one,true_and]
  change ((1≤n ∧ n≤X+Δ) ∧ Even n ∧ (primeRepresentations unitProgressions n).card=0) ∧ X<n ↔ _
  rw [no_unit_rep_iff]
  constructor
  · rintro ⟨⟨⟨_,hi⟩,he,hn⟩,hl⟩; exact ⟨⟨⟨hl,hi⟩,he⟩,hn⟩
  · rintro ⟨⟨⟨hl,hi⟩,he⟩,hn⟩; exact ⟨⟨⟨by omega,hi⟩,he,hn⟩,hl⟩

theorem shortDoubleAvgExceptions_one (X Δ : ℕ) :
    shortDoubleAvgExceptions X Δ 1 (by decide) = ((shortGoldbachExceptions X Δ).card : ℝ) := by
  have hp (b c : {b // b ∈ coprimeClasses 1}) : shortProgressions (r:=1) (by decide) b c = unitProgressions := by
    obtain ⟨b,hb⟩ := b
    obtain ⟨c,hc⟩ := c
    obtain rfl := (Nat.lt_one_iff.mp (mem_coprimeClasses.mp hb).1)
    obtain rfl := (Nat.lt_one_iff.mp (mem_coprimeClasses.mp hc).1)
    rfl
  simp only [shortDoubleAvgExceptions,hp,unit_exceptions_eq,Finset.sum_const,Finset.card_attach,
    card_coprimeClasses,Nat.totient_one,Nat.cast_one,one_pow,div_one,one_mul,one_nsmul]

/-- The density is relative to the actual number of even integers in each window. -/
theorem short_goldbach_even_exception_density_zero_of_bound (h : ShortDoubleAvgBound)
    (X Δ : ℕ → ℕ) (hX : ∀ n, 2≤X n) (hΔ : ∀ n, 1≤Δ n) (hΔX : ∀ n, Δ n≤X n)
    (hP : Tendsto (fun n => (Δ n:ℝ)/Real.log (2*(X n:ℝ))^6) atTop atTop) :
    Tendsto (fun n => ((shortGoldbachExceptions (X n) (Δ n)).card:ℝ) /
      ((shortEvenIntegers (X n) (Δ n)).card:ℝ)) atTop (𝓝 0) := by
  have ht := shortDoubleAvgDensity_of_bound h X Δ (fun _ => 1) (fun _ => by decide) hX
    (fun n => by have := hX n; omega) hΔ hΔX (by simpa [shortDoubleAvgParameter] using hP)
  simp only [shortDoubleAvgExceptions_one,Nat.cast_one,div_one] at ht
  have ht3 : Tendsto (fun n => 3*(((shortGoldbachExceptions (X n) (Δ n)).card:ℝ)/(Δ n:ℝ)))
      atTop (𝓝 0) := by simpa using ht.const_mul 3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht3
    (Filter.Eventually.of_forall (fun n => by positivity)) (Filter.Eventually.of_forall fun n => ?_)
  let N := (shortEvenIntegers (X n) (Δ n)).card
  let E := (shortGoldbachExceptions (X n) (Δ n)).card
  change (E:ℝ)/N ≤ 3*((E:ℝ)/(Δ n:ℝ))
  by_cases hN : N=0
  · rw [hN,Nat.cast_zero,div_zero]; positivity
  · have hden : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
    have hd : (0:ℝ)<Δ n := Nat.cast_pos.mpr (hΔ n)
    have hN' : N=(X n+Δ n)/2-X n/2 := card_shortEvenIntegers _ _
    have hl : (Δ n:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast (show Δ n ≤ 3*N by omega)
    rw [← mul_div_assoc,div_le_div_iff₀ hden hd]
    nlinarith only [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α:=ℝ) E)]

/-- Even integers represented as a sum of two primes. -/
noncomputable def shortGoldbachRepresented (X Δ : ℕ) : Finset ℕ := by
  classical
  exact (shortEvenIntegers X Δ).filter (fun n => ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p+q=n)

/-- In the diverging-parameter range, the proportion of even integers represented
as a sum of two primes tends to one in every sequence of translated windows. -/
theorem short_goldbach_even_density_one_of_bound (h : ShortDoubleAvgBound)
    (X Δ : ℕ → ℕ) (hX : ∀ n, 2≤X n) (hΔ : ∀ n, 1≤Δ n) (hΔX : ∀ n, Δ n≤X n)
    (hP : Tendsto (fun n => (Δ n:ℝ)/Real.log (2*(X n:ℝ))^6) atTop atTop) :
    Tendsto (fun n => ((shortGoldbachRepresented (X n) (Δ n)).card:ℝ) /
      ((shortEvenIntegers (X n) (Δ n)).card:ℝ)) atTop (𝓝 1) := by
  classical
  have ht := short_goldbach_even_exception_density_zero_of_bound h X Δ hX hΔ hΔX hP
  have ht' := (tendsto_const_nhds (x:= (1:ℝ))).sub ht
  rw [sub_zero] at ht'
  refine ht'.congr' ?_
  filter_upwards [hP.eventually_ge_atTop 2] with n hn
  have hlog := one_le_log_two_mul (hX n)
  have hpow : 1 ≤ Real.log (2*(X n:ℝ))^6 := one_le_pow₀ hlog
  have hpos : 0 < Real.log (2*(X n:ℝ))^6 := by linarith
  have hd : (2:ℝ) ≤ Δ n := by
    have hh := (le_div_iff₀ hpos).mp hn
    linarith
  have hd' : 2≤Δ n := by exact_mod_cast hd
  have hc : 0 < (shortEvenIntegers (X n) (Δ n)).card := by
    rw [card_shortEvenIntegers]; omega
  have hcr : (0:ℝ) < (shortEvenIntegers (X n) (Δ n)).card := Nat.cast_pos.mpr hc
  have hh : (shortGoldbachRepresented (X n) (Δ n)).card + (shortGoldbachExceptions (X n) (Δ n)).card =
      (shortEvenIntegers (X n) (Δ n)).card :=
    Finset.card_filter_add_card_filter_not _
  change 1 - _ / _ = _ / _
  rw [sub_div' hcr.ne',one_mul,div_left_inj₀ hcr.ne']
  exact sub_eq_of_eq_add (by exact_mod_cast hh.symm)

end FareyGoldbach




