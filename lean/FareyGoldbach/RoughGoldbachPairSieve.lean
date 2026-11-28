import FareyGoldbach.ChenCanonicalNormalization
import FareyGoldbach.ChenConditionalMargin
import FareyGoldbach.ChenSwitchingScales
import FareyGoldbach.SelbergEulerProduct
import FareyGoldbach.SelbergFiniteSieve
import FareyGoldbach.SelbergTruncation

/-! # A uniform Selberg bound for the last factor of a four-prime complement -/

open Filter Finset
open scoped BigOperators Classical Topology

namespace FareyGoldbach

/-- Both primes are at least the strict sifting cutoff. -/
def chenRoughThreePrimePairs (N d y : ℕ) : Finset ℕ :=
  (Icc y (N / d)).filter fun q ↦ q.Prime ∧ y ≤ N - d * q ∧ (N - d * q).Prime

private def pairSievePrimes (y : ℕ) : Finset ℕ :=
  (chenPrimesBelow y).filter (3 < ·)

private theorem mem_primesBelow {p y : ℕ} :
    p ∈ chenPrimesBelow y ↔ p.Prime ∧ p < y := by
  unfold chenPrimesBelow
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨_, h⟩, hp⟩
    exact ⟨hp, by have := hp.pos; omega⟩
  · rintro ⟨hp, hy⟩
    exact ⟨⟨hp.pos, by omega⟩, hp⟩

private theorem mem_pairSievePrimes {p y : ℕ} :
    p ∈ pairSievePrimes y ↔ p.Prime ∧ p < y ∧ 3 < p := by
  simp [pairSievePrimes, mem_primesBelow, and_assoc]

private noncomputable def pairRootCount (N p : ℕ) : ℝ :=
  if p ∣ N then 1 else 2

private noncomputable def pairG (N p : ℕ) : ℝ :=
  pairRootCount N p / ((p:ℝ) - pairRootCount N p)

private noncomputable def pairV (N y : ℕ) : ℝ :=
  ∏ p ∈ pairSievePrimes y, (1 - pairRootCount N p / (p:ℝ))

private theorem pairRootCount_bounds (N p : ℕ) :
    1 ≤ pairRootCount N p ∧ pairRootCount N p ≤ 2 := by
  unfold pairRootCount
  split_ifs <;> norm_num

private theorem pairG_bounds (N : ℕ) {p : ℕ} (hp : 3 < p) :
    0 ≤ pairG N p ∧ pairG N p ≤ 1 := by
  have hp' : (4:ℝ) ≤ p := by exact_mod_cast hp
  have h := pairRootCount_bounds N p
  unfold pairG
  constructor
  · exact div_nonneg (by linarith [h.1]) (by linarith [h.2])
  · exact (div_le_iff₀ (by linarith [h.2])).2 (by linarith [h.2])

private theorem pairG_ratio (N : ℕ) {p : ℕ} (hp : 3 < p) :
    pairG N p / (1 + pairG N p) = pairRootCount N p / (p:ℝ) := by
  have hp' : (4:ℝ) ≤ p := by exact_mod_cast hp
  have h := (pairRootCount_bounds N p).2
  have h₀ : (p:ℝ) ≠ 0 := by linarith
  have h₁ : (p:ℝ) - pairRootCount N p ≠ 0 := by linarith
  have h₂ : 1 + pairG N p ≠ 0 := by linarith [(pairG_bounds N hp).1]
  apply (div_eq_iff h₂).2
  unfold pairG
  field_simp
  ring

private noncomputable def pairResidues (N d p : ℕ) : Finset (ZMod p) :=
  {0, (N:ZMod p) * (d:ZMod p)⁻¹}

private noncomputable def pairWeight (N d p : ℕ) (x : ZMod p) : ℝ :=
  if x ∈ pairResidues N d p then -1 else pairG N p

private theorem pairResidues_card {N d p : ℕ} (hp : p.Prime) (hd : ¬p ∣ d) :
    ((pairResidues N d p).card:ℝ) = pairRootCount N p := by
  let : Fact p.Prime := ⟨hp⟩
  have hd' : (d:ZMod p) ≠ 0 := fun h ↦ hd ((ZMod.natCast_eq_zero_iff d p).1 h)
  by_cases hN : p ∣ N
  · have hN' : (N:ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).2 hN
    simp [pairResidues, pairRootCount, hN, hN']
  · have hN' : (N:ZMod p) ≠ 0 := fun h ↦ hN ((ZMod.natCast_eq_zero_iff N p).1 h)
    have hne : (0:ZMod p) ≠ (N:ZMod p) * (d:ZMod p)⁻¹ :=
      (mul_ne_zero hN' (inv_ne_zero hd')).symm
    simp [pairResidues, pairRootCount, hN, hne]

private theorem sum_pair_ite {A : Type*} [Fintype A] [DecidableEq A]
    (B : Finset A) (a b : ℝ) :
    (∑ x : A, if x ∈ B then a else b) =
      (B.card:ℝ) * a + ((Fintype.card A:ℝ) - B.card) * b := by
  rw [Finset.sum_ite]
  have h₁ : (Finset.univ.filter (· ∈ B)) = B := by ext x; simp
  have h₂ : (Finset.univ.filter (· ∉ B)) = Finset.univ \ B := by ext x; simp
  rw [h₁, h₂]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.cast_card_sdiff (Finset.subset_univ B),
    Finset.card_univ]

private theorem pairWeight_sum {N d p : ℕ} (hp : p.Prime) (hp₄ : 3 < p) (hd : ¬p ∣ d)
    [NeZero p] : (∑ x : ZMod p, pairWeight N d p x) = 0 := by
  have hp' : (4:ℝ) ≤ p := by exact_mod_cast hp₄
  have h := (pairRootCount_bounds N p).2
  have h₁ : (p:ℝ) - pairRootCount N p ≠ 0 := by linarith
  unfold pairWeight
  rw [sum_pair_ite, ZMod.card, pairResidues_card hp hd]
  unfold pairG
  field_simp
  ring

private theorem pairWeight_square_sum {N d p : ℕ} (hp : p.Prime) (hp₄ : 3 < p) (hd : ¬p ∣ d)
    [NeZero p] : (∑ x : ZMod p, (pairWeight N d p x)^2) = (p:ℝ) * pairG N p := by
  have hp' : (4:ℝ) ≤ p := by exact_mod_cast hp₄
  have h := (pairRootCount_bounds N p).2
  have h₁ : (p:ℝ) - pairRootCount N p ≠ 0 := by linarith
  calc
    _ = ∑ x : ZMod p, if x ∈ pairResidues N d p then (1:ℝ) else (pairG N p)^2 := by
      apply Finset.sum_congr rfl
      intro x _
      unfold pairWeight
      split_ifs <;> norm_num
    _ = _ := by
      rw [sum_pair_ite, ZMod.card, pairResidues_card hp hd]
      unfold pairG
      field_simp
      ring

private theorem pairWeight_of_mem {N d y q p : ℕ} (hd : 0 < d)
    (hq : q ∈ chenRoughThreePrimePairs N d y) (hp : p.Prime) (hpy : p < y) (hpd : ¬p ∣ d) :
    pairWeight N d p (q:ZMod p) = pairG N p := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hqI, hqP, hNy, hNP⟩ := Finset.mem_filter.1 hq
  obtain ⟨hqy, hqD⟩ := Finset.mem_Icc.1 hqI
  have hmul : d * q ≤ N := by
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le hd).1 hqD
  have hqne : (q:ZMod p) ≠ 0 := by
    intro h
    rcases (Nat.dvd_prime hqP).1 ((ZMod.natCast_eq_zero_iff q p).1 h) with he | he
    · exact hp.ne_one he
    · omega
  have hNne : ((N - d * q:ℕ):ZMod p) ≠ 0 := by
    intro h
    rcases (Nat.dvd_prime hNP).1 ((ZMod.natCast_eq_zero_iff (N - d * q) p).1 h) with he | he
    · exact hp.ne_one he
    · omega
  have hdne : (d:ZMod p) ≠ 0 := fun h ↦ hpd ((ZMod.natCast_eq_zero_iff d p).1 h)
  have hrne : (q:ZMod p) ≠ (N:ZMod p) * (d:ZMod p)⁻¹ := by
    intro h
    apply hNne
    rw [Nat.cast_sub hmul, Nat.cast_mul, h, sub_eq_zero]
    calc
      (N:ZMod p) = (N:ZMod p) * ((d:ZMod p) * (d:ZMod p)⁻¹) := by simp [hdne]
      _ = _ := by ring
  simp [pairWeight, pairResidues, hqne, hrne]

private theorem pair_mass_ge_one {N y R : ℕ} (hR : 1 ≤ R) :
    1 ≤ sieveMass (pairSievePrimes y) R (pairG N) := by
  have hempty : (∅ : Finset ℕ) ∈ sieveIndices (pairSievePrimes y) R :=
    mem_sieveIndices.2 ⟨Finset.empty_subset _, by simpa [sieveModulus] using hR⟩
  have h := Finset.single_le_sum
    (f := fun s : Finset ℕ ↦ ∏ p ∈ s, pairG N p)
    (fun s hs ↦ Finset.prod_nonneg fun p hp ↦
      (pairG_bounds N (mem_pairSievePrimes.1 ((mem_sieveIndices.1 hs).1 hp)).2.2).1)
    hempty
  simpa [sieveMass] using h

private theorem pair_card_le_mass {N d y R : ℕ} (hd : 0 < d) (hR : 1 ≤ R)
    (hcop : ∀ p : ℕ, p.Prime → p < y → ¬p ∣ d) :
    ((chenRoughThreePrimePairs N d y).card:ℝ) ≤
      ((N/d:ℕ):ℝ) / sieveMass (pairSievePrimes y) R (pairG N) +
        1 / sieveMass (pairSievePrimes y) R (pairG N) + 6 * (R:ℝ)^4 := by
  let J := N / d + 1
  let S := chenRoughThreePrimePairs N d y
  -- Two free coordinates let the cube estimate give an interval estimate after division by J².
  let T := S ×ˢ ((range J) ×ˢ (range J))
  let P := pairSievePrimes y
  let G := sieveMass P R (pairG N)
  let u (p : ℕ) (x : ZMod p × ZMod p × ZMod p) := pairWeight N d p x.1
  have hT : T ⊆ sieveCube J := by
    intro x hx
    have hx' := (Finset.mem_product.1 hx).1
    have hj := (Finset.mem_Icc.1 (Finset.mem_filter.1 hx').1).2
    exact Finset.mem_product.2 ⟨Finset.mem_range.2 (by dsimp [J]; omega),
      (Finset.mem_product.1 hx).2⟩
  have hu (v : ℕ × ℕ × ℕ) (hv : v ∈ T) (p : ℕ) (hp : p ∈ P) :
      u p (v.1, v.2.1, v.2.2) = pairG N p := by
    obtain ⟨hp, hpy, _⟩ := mem_pairSievePrimes.1 hp
    exact pairWeight_of_mem hd (Finset.mem_product.1 hv).1 hp hpy (hcop p hp hpy)
  have habs (p : ℕ) (hp : p ∈ P) (x : ZMod p × ZMod p × ZMod p) : |u p x| ≤ 1 := by
    obtain ⟨_, _, hp₄⟩ := mem_pairSievePrimes.1 hp
    dsimp [u, pairWeight]
    split_ifs
    · norm_num
    · exact (abs_of_nonneg (pairG_bounds N hp₄).1).trans_le (pairG_bounds N hp₄).2
  have hz (p : ℕ) [NeZero p] (hp : p ∈ P) : (∑ x, u p x) = 0 := by
    obtain ⟨hp, hpy, hp₄⟩ := mem_pairSievePrimes.1 hp
    simp only [u, Fintype.sum_prod_type, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      ← Finset.mul_sum, pairWeight_sum hp hp₄ (hcop p hp hpy), mul_zero]
  have hsq (p : ℕ) [NeZero p] (hp : p ∈ P) : (∑ x, (u p x)^2) = (p:ℝ)^3 * pairG N p := by
    obtain ⟨hp, hpy, hp₄⟩ := mem_pairSievePrimes.1 hp
    simp only [u, Fintype.sum_prod_type, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Fintype.card_prod, ZMod.card, ← Finset.mul_sum,
      pairWeight_square_sum hp hp₄ (hcop p hp hpy)]
    rw [Nat.cast_mul]
    ring
  have h := sieveCube_card_mul_mass_sq_le J R P T hT
    (fun _ hp ↦ (mem_pairSievePrimes.1 hp).1) u (pairG N) hu habs hz hsq
  have hcard : (T.card:ℝ) = (S.card:ℝ) * (J:ℝ)^2 := by simp [T, pow_two]
  change (T.card:ℝ) * G^2 ≤ (J:ℝ)^3 * G + 6 * (J:ℝ)^2 * (R:ℝ)^4 at h
  rw [hcard] at h
  have hJ : (0:ℝ) < J := by exact_mod_cast (Nat.succ_pos (N / d))
  have hG₁ : 1 ≤ G := pair_mass_ge_one hR
  have hG : 0 < G := by linarith
  have hfin : (S.card:ℝ) * G^2 ≤ (J:ℝ) * G + 6 * (R:ℝ)^4 := by
    apply le_of_mul_le_mul_left _ (sq_pos_of_pos hJ)
    nlinarith only [h]
  have hexp : 1 ≤ G^2 := by nlinarith only [sq_nonneg (G - 1), hG₁]
  calc
    _ ≤ ((J:ℝ) * G + 6 * (R:ℝ)^4) / G^2 := (le_div_iff₀ (sq_pos_of_pos hG)).2 hfin
    _ = (J:ℝ) / G + (6 * (R:ℝ)^4) / G^2 := by
      rw [add_div]
      congr 1
      field_simp
    _ ≤ (J:ℝ) / G + 6 * (R:ℝ)^4 := by
      exact add_le_add (le_refl _) (div_le_self (by positivity) hexp)
    _ = _ := by simp [J, G, P, add_div]

private theorem pairV_pos (N y : ℕ) : 0 < pairV N y := by
  unfold pairV
  apply Finset.prod_pos
  intro p hp
  have hp' : (4:ℝ) ≤ p := by exact_mod_cast (mem_pairSievePrimes.1 hp).2.2
  have h := (pairRootCount_bounds N p).2
  exact sub_pos.mpr ((div_lt_iff₀ (by linarith : (0:ℝ) < p)).2 (by linarith))

private theorem pair_mass_reciprocal_le {N y R : ℕ} (hR : 1 < R)
    (hmean : ∑ p ∈ pairSievePrimes y,
      (pairRootCount N p / (p:ℝ)) * Real.log (p:ℝ) ≤ Real.log (R:ℝ) / 2) :
    1 / sieveMass (pairSievePrimes y) R (pairG N) ≤ 2 * pairV N y := by
  let P := pairSievePrimes y
  let g := pairG N
  let f := fun p : ℕ ↦ Real.log (p:ℝ)
  have hR' : (1:ℝ) < R := by exact_mod_cast hR
  have hg : ∀ p ∈ P, 0 ≤ g p :=
    fun p hp ↦ (pairG_bounds N (mem_pairSievePrimes.1 hp).2.2).1
  have hf : ∀ p ∈ P, 0 ≤ f p := fun p hp ↦
    Real.log_nonneg (by exact_mod_cast (mem_pairSievePrimes.1 hp).1.one_le)
  have hmean' : ∑ p ∈ P, (g p / (1 + g p)) * f p ≤ Real.log (R:ℝ) / 2 := by
    convert hmean using 1
    apply Finset.sum_congr rfl
    intro p hp
    rw [show g p / (1 + g p) = pairRootCount N p / (p:ℝ) from
      pairG_ratio N (mem_pairSievePrimes.1 hp).2.2]
  have htr := subset_product_truncation P g f hg hf (Real.log_pos hR') hmean'
  have hfilter :
      P.powerset.filter (fun s : Finset ℕ ↦ (∑ p ∈ s, f p) ≤ Real.log (R:ℝ)) =
      sieveIndices P R := by
    ext s
    simp only [sieveIndices, Finset.mem_filter, Finset.mem_powerset, and_congr_right_iff]
    intro hs
    have hp' {p : ℕ} (hp : p ∈ s) : (0:ℝ) < p := by
      exact_mod_cast (mem_pairSievePrimes.1 (hs hp)).1.pos
    have hpos : 0 < ∏ p ∈ s, (p:ℝ) := Finset.prod_pos fun _ hp ↦ hp' hp
    dsimp only [f, sieveModulus]
    rw [← Real.log_prod (fun _ hp ↦ (hp' hp).ne'),
      Real.log_le_log_iff hpos (by linarith : (0:ℝ) < R), ← Nat.cast_prod]
    exact Nat.cast_le
  rw [hfilter] at htr
  have hprod : (∏ p ∈ P, (1 + g p)) * pairV N y = 1 := by
    unfold pairV
    rw [← Finset.prod_mul_distrib]
    trans ∏ _ ∈ P, (1:ℝ)
    · apply Finset.prod_congr rfl
      intro p hp
      have hp' : (4:ℝ) ≤ p := by exact_mod_cast (mem_pairSievePrimes.1 hp).2.2
      have h := (pairRootCount_bounds N p).2
      have h₀ : (p:ℝ) ≠ 0 := by linarith
      have h₁ : (p:ℝ) - pairRootCount N p ≠ 0 := by linarith
      dsimp [g, pairG]
      field_simp
      ring
    · simp
  change (∏ p ∈ P, (1 + g p)) / 2 ≤ sieveMass P R g at htr
  have hm := mul_le_mul_of_nonneg_right htr (pairV_pos N y).le
  apply (div_le_iff₀ (zero_lt_one.trans_le (pair_mass_ge_one hR.le))).2
  linarith only [hm, hprod]

private theorem pair_local_factor (N : ℕ) {p : ℕ} (hp : p.Prime) :
    (1 - 1 / (p:ℝ))^2 * (1 + localFactor 1 N p) = 1 - pairRootCount N p / (p:ℝ) := by
  have hp₁ : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hp₀ : (p:ℝ) ≠ 0 := by linarith
  have h₁ : (p:ℝ) - 1 ≠ 0 := by linarith
  have hNd : ¬ p ∣ 1 := fun h ↦ hp.ne_one (Nat.dvd_one.1 h)
  unfold localFactor pairRootCount
  rw [ite_eq_right hNd]
  by_cases hN : p ∣ N <;> simp only [hN, ite_true, ite_false] <;> field_simp <;> ring

private theorem pairV_le_euler {N y : ℕ} (he : Even N) (hy : 3 < y) :
    pairV N y ≤ 6 * chenMertensProduct y ^ 2 * chenSingularAtCutoff N y := by
  let P := chenPrimesBelow y
  let I : Finset ℕ := {2, 3}
  let f := fun p : ℕ ↦ 1 - pairRootCount N p / (p:ℝ)
  have hI : I ⊆ P := by
    intro p hp
    rcases (show p = 2 ∨ p = 3 by simpa [I] using hp) with rfl | rfl
    · exact mem_primesBelow.2 ⟨Nat.prime_two, by omega⟩
    · exact mem_primesBelow.2 ⟨Nat.prime_three, hy⟩
  have hPI : P \ I = pairSievePrimes y := by
    apply Finset.ext
    intro p
    change p ∈ chenPrimesBelow y \ ({2, 3}:Finset ℕ) ↔ p ∈ pairSievePrimes y
    simp only [Finset.mem_sdiff, mem_pairSievePrimes, mem_primesBelow, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨hp, hpy⟩, hne⟩
      exact ⟨hp, hpy, by have := hp.two_le; omega⟩
    · rintro ⟨hp, hpy, hp₄⟩
      exact ⟨⟨hp, hpy⟩, by omega⟩
  have hfull : (∏ p ∈ P, f p) = chenMertensProduct y ^ 2 * chenSingularAtCutoff N y := by
    unfold chenMertensProduct chenSingularAtCutoff
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p hp ↦ (pair_local_factor N (mem_primesBelow.1 hp).1).symm
  have h2 : f 2 = 1 / 2 := by
    have hN : 2 ∣ N := even_iff_two_dvd.1 he
    norm_num [f, pairRootCount, hN]
  have h3 : (1:ℝ) / 3 ≤ f 3 := by
    dsimp [f]
    linarith only [(pairRootCount_bounds N 3).2]
  have hsmall : (1:ℝ) / 6 ≤ ∏ p ∈ I, f p := by
    simp only [I, Finset.prod_insert (show (2:ℕ) ∉ ({3}:Finset ℕ) by simp), Finset.prod_singleton, h2]
    linarith
  have hsplit := Finset.prod_sdiff (f:=f) hI
  rw [hPI, hfull] at hsplit
  change pairV N y * (∏ p ∈ I, f p) = _ at hsplit
  linarith only [hsplit, mul_le_mul_of_nonneg_left hsmall (pairV_pos N y).le]

private theorem pair_mertens_upper {y : ℕ} (hy : 1 < y) :
    Real.log (y:ℝ) * chenMertensProduct y ≤ 1 := by
  have hs : Nat.primesLE (y-1) = chenPrimesBelow y := by
    ext p
    simp only [Nat.mem_primesLE, mem_primesBelow]
    constructor
    · rintro ⟨hp, hprime⟩
      exact ⟨hprime, by omega⟩
    · rintro ⟨hprime, hp⟩
      exact ⟨by omega, hprime⟩
  have h := prime_euler_log_le (y-1)
  have hy' : ((y-1:ℕ):ℝ)+1 = (y:ℝ) := by rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
  rw [hs, hy', Finset.prod_inv_distrib] at h
  change Real.log (y:ℝ) ≤ (chenMertensProduct y)⁻¹ at h
  have hp : 0 < chenMertensProduct y := by
    apply Finset.prod_pos
    intro p hp
    have h' : (1:ℝ) < p := by exact_mod_cast (mem_primesBelow.1 hp).1.one_lt
    exact sub_pos.mpr ((div_lt_iff₀ (by linarith : (0:ℝ) < p)).2 (by linarith))
  exact (mul_le_mul_of_nonneg_right h hp.le).trans_eq (inv_mul_cancel₀ hp.ne')

private theorem pair_singular_comparison :
    ∀ᶠ N : ℕ in atTop, Even N →
      chenSingularAtCutoff N (chenPowerLevel (1/512) N + 1) ≤ (9:ℝ)/8 * chenCanonicalU N := by
  let w := chenPowerLevel (1/512)
  have hw := chenPowerLevel_tendsto_atTop (a:=1/512) (by norm_num)
  have hw' := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp hw
  have hlog := chenLogTwo_div_powerLevel_tendsto (a:=1/512) (by norm_num)
  have hdom : Tendsto (fun N : ℕ ↦
      2 * (Real.log (2 * (N:ℝ)) / (w N:ℝ)) + 2 / (w N:ℝ)) atTop (𝓝 0) := by
    simpa only [w, Function.comp_apply, mul_zero, add_zero] using
      (hlog.const_mul (2:ℝ)).add ((tendsto_const_nhds (x:=(2:ℝ))).div_atTop hw')
  have hexp := hdom.rexp.sub_const 1
  simp only [Real.exp_zero, sub_self] at hexp
  filter_upwards [hexp.eventually_lt_const (show (0:ℝ) < 1/9 by norm_num),
    hw.eventually_ge_atTop (4:ℕ), eventually_ge_atTop (2:ℕ)] with N hsmall hwN hN he
  let y := w N + 1
  have hNy : y ≤ N + 1 :=
    Nat.add_le_add_right (chenPowerLevel_le_self (a:=1/512) (by norm_num) (by omega)) 1
  have hy₄ : 4 ≤ y := by dsimp [y, w] at *; omega
  have hy₃ : 3 ≤ y := by omega
  have hSpos : 0 < chenSingularAtCutoff N y :=
    (by norm_num : (0:ℝ) < 1/2).trans_le (chenSingularAtCutoff_ge_half he hy₃)
  have hwR : (4:ℝ) ≤ w N := by exact_mod_cast hwN
  have hshift : 1 / ((y:ℝ) - 2) ≤ 2 / (w N:ℝ) := by
    dsimp [y]
    rw [Nat.cast_add, Nat.cast_one]
    exact (div_le_div_iff₀ (by linarith) (by linarith)).2 (by linarith)
  have hshift' : 2 * Real.log (2 * (N:ℝ)) / ((y:ℝ) - 1) =
      2 * (Real.log (2 * (N:ℝ)) / (w N:ℝ)) := by
    simp [y, mul_div_assoc]
  have hsmall' : Real.exp (2 * Real.log (2*(N:ℝ))/((y:ℝ)-1)+1/((y:ℝ)-2))-1 < 1/9 := by
    refine lt_of_le_of_lt (sub_le_sub_right (Real.exp_le_exp.2 ?_) _) hsmall
    rw [hshift']
    exact add_le_add (le_refl _) hshift
  have hratio := (abs_le.mp (chenCanonicalU_ratio_sub_one_le he hy₄ hNy)).1
  have hlo : (8:ℝ)/9 ≤ chenCanonicalU N / chenSingularAtCutoff N y := by
    linarith only [hratio, hsmall']
  have hmul := (le_div_iff₀ hSpos).1 hlo
  change chenSingularAtCutoff N y ≤ _
  linarith only [hmul]

private theorem pair_mean_eventually :
    ∀ᶠ N : ℕ in atTop,
      let y := chenPowerLevel (1/512) N + 1
      let R := chenPowerLevel (1/32) N
      ∑ p ∈ pairSievePrimes y,
        (pairRootCount N p / (p:ℝ)) * Real.log (p:ℝ) ≤ Real.log (R:ℝ) / 2 := by
  let w := chenPowerLevel (1/512)
  let R := chenPowerLevel (1/32)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hw := chenPowerLevel_tendsto_atTop (a:=1/512) (by norm_num)
  have hRlog := (chenLogPowerLevel_tendsto (a:=1/32) (by norm_num)).eventually_const_lt
    (show (1:ℝ)/64 < 1/32 by norm_num)
  filter_upwards [hRlog, hw.eventually_ge_atTop (1:ℕ), eventually_ge_atTop (2:ℕ),
    hlog.eventually_ge_atTop (512 * (Real.log 4 + 4))] with N hRlog hwN hN hLbig
  change ∑ p ∈ pairSievePrimes (w N + 1),
    (pairRootCount N p / (p:ℝ)) * Real.log (p:ℝ) ≤ Real.log (R N:ℝ) / 2
  have hN' : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < Real.log (N:ℝ) := Real.log_pos hN'
  have hwR : (1:ℝ) ≤ w N := by exact_mod_cast hwN
  have hwlog : Real.log (w N:ℝ) ≤ (1:ℝ)/512 * Real.log (N:ℝ) := by
    apply (Real.log_le_log (zero_lt_one.trans_le hwR) ?_).trans_eq
      (Real.log_rpow (zero_lt_one.trans hN') _)
    exact Nat.floor_le (by positivity)
  have hRlog' := (lt_div_iff₀ hL).1 hRlog
  change (1:ℝ)/64 * Real.log (N:ℝ) < Real.log (R N:ℝ) at hRlog'
  change 512 * (Real.log 4 + 4) ≤ Real.log (N:ℝ) at hLbig
  have hm := (abs_le.1 (Mertens.sum_log_prime_div_eq_log (x:=(w N:ℝ)) hwR)).2
  simp only [Nat.floor_natCast] at hm
  have hsum :
      (∑ p ∈ pairSievePrimes (w N + 1), Real.log (p:ℝ) / (p:ℝ)) ≤
        ∑ p ∈ (Finset.Ioc 0 (w N)).filter Nat.Prime, Real.log (p:ℝ) / (p:ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp, hpw, _⟩ := mem_pairSievePrimes.1 hp
      exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hp.pos, by omega⟩, hp⟩
    · intro p hp _
      have hp' : (1:ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.one_le
      exact div_nonneg (Real.log_nonneg hp') (by positivity)
  calc
    _ ≤ ∑ p ∈ pairSievePrimes (w N + 1), 2 * (Real.log (p:ℝ) / (p:ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' : (1:ℝ) ≤ p := by exact_mod_cast (mem_pairSievePrimes.1 hp).1.one_le
      calc
        _ ≤ (2 / (p:ℝ)) * Real.log (p:ℝ) := mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (pairRootCount_bounds N p).2 (by positivity))
          (Real.log_nonneg hp')
        _ = _ := by ring
    _ ≤ 2 * (Real.log (w N:ℝ) + (Real.log 4 + 4)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hsum.trans (by linarith only [hm])) (by norm_num)
    _ ≤ _ := by linarith only [hwlog, hRlog', hLbig]

private theorem pair_volume_eventually :
    ∀ᶠ N : ℕ in atTop, Even N →
      let y := chenPowerLevel (1/512) N + 1
      2 * pairV N y ≤ ((27:ℝ)/2 * 512^2) * chenCanonicalU N / Real.log (N:ℝ)^2 := by
  let w := chenPowerLevel (1/512)
  have hw := chenPowerLevel_tendsto_atTop (a:=1/512) (by norm_num)
  filter_upwards [pair_singular_comparison, hw.eventually_ge_atTop (3:ℕ),
    eventually_ge_atTop (2:ℕ)] with N hs hwN hN he
  let y := w N + 1
  have hy₄ : 3 < y := by dsimp [y, w]; omega
  have hN' : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < Real.log (N:ℝ) := Real.log_pos hN'
  have hylog : (1:ℝ)/512 * Real.log (N:ℝ) ≤ Real.log (y:ℝ) := by
    rw [← Real.log_rpow (zero_lt_one.trans hN')]
    apply Real.log_le_log (by positivity)
    simpa only [y, w, chenPowerLevel, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one ((N:ℝ)^(1/512:ℝ))).le
  have hMm := pair_mertens_upper (by omega : 1 < y)
  have hMpos : 0 ≤ chenMertensProduct y := by
    apply Finset.prod_nonneg
    intro p hp
    have h' : (1:ℝ) < p := by exact_mod_cast (mem_primesBelow.1 hp).1.one_lt
    exact sub_nonneg.mpr ((div_le_iff₀ (by linarith : (0:ℝ) < p)).2 (by linarith))
  have hM : chenMertensProduct y ≤ 512 / Real.log (N:ℝ) := by
    apply (le_div_iff₀ hL).2
    linarith only [mul_le_mul_of_nonneg_right hylog hMpos, hMm]
  have hUpos : 0 ≤ chenCanonicalU N := by linarith only [chenCanonicalU_ge_half he hN]
  have hSpos : 0 ≤ chenSingularAtCutoff N y := by
    linarith only [chenSingularAtCutoff_ge_half he (by omega : 3 ≤ y)]
  change 2 * pairV N y ≤ _
  calc
    _ ≤ 2 * (6 * chenMertensProduct y ^ 2 * chenSingularAtCutoff N y) :=
      mul_le_mul_of_nonneg_left (pairV_le_euler he hy₄) (by norm_num)
    _ ≤ 2 * (6 * (512 / Real.log (N:ℝ)) ^ 2 * ((9:ℝ)/8 * chenCanonicalU N)) := by
      gcongr
      exact hs he
    _ = _ := by rw [div_pow]; ring

private theorem pair_fourth_power_error {ε : ℝ} (hε₀ : ε < (1:ℝ)/524288) :
    ∀ᶠ N : ℕ in atTop,
      12 * (chenPowerLevel (1/32) N:ℝ)^4 * Real.log (N:ℝ)^2 ≤
        (chenPowerLevel (1/4 - ε) N:ℝ) := by
  have hpow := eventually_rpow_add_one_le_powerLevel (a:=1/5) (b:=1/4-ε)
    (by norm_num) (by linarith)
  have hlog := ((isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ) < 3/40)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hpow, hlog.eventually_lt_const (show (0:ℝ)<1/12 by norm_num),
    eventually_ge_atTop (2:ℕ)] with N hpow hlog hN
  have hN' : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hR : (chenPowerLevel (1/32) N:ℝ) ≤ (N:ℝ)^(1/32:ℝ) := Nat.floor_le (by positivity)
  have hmul : ((N:ℝ)^(1/32:ℝ))^4 = (N:ℝ)^(1/8:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN'.le]
    norm_num
  change Real.log (N:ℝ) ^ (2:ℝ) / (N:ℝ)^(3/40:ℝ) < 1/12 at hlog
  rw [Real.rpow_two] at hlog
  have hlog' := (div_lt_iff₀ (Real.rpow_pos_of_pos hN' _)).1 hlog
  calc
    _ ≤ 12 * ((N:ℝ)^(1/32:ℝ))^4 * Real.log (N:ℝ)^2 := by gcongr
    _ = (N:ℝ)^(1/8:ℝ) * (12 * Real.log (N:ℝ)^2) := by rw [hmul]; ring
    _ ≤ (N:ℝ)^(1/8:ℝ) * (N:ℝ)^(3/40:ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlog']) (by positivity)
    _ = (N:ℝ)^(1/5:ℝ) := by rw [← Real.rpow_add hN']; norm_num
    _ ≤ _ := by linarith only [hpow]

/-- The Selberg upper bound is uniform in the fixed product of the first three primes. -/
theorem chen_rough_three_pair_count_upper {ε : ℝ} (hε₀ : ε < (1:ℝ)/524288) :
    ∀ᶠ N : ℕ in atTop, Even N →
      let y := chenPowerLevel (1/512) N + 1
      ∀ d : ℕ, 0 < d → chenPowerLevel (1/4 - ε) N ≤ N / d →
        (∀ p : ℕ, p.Prime → p < y → ¬p ∣ d) →
        ((chenRoughThreePrimePairs N d y).card:ℝ) ≤
          (2:ℝ)^22 * chenSieveScale chenCanonicalU N / (d:ℝ) := by
  have hR := chenPowerLevel_tendsto_atTop (a:=1/32) (by norm_num)
  have hz := chenPowerLevel_tendsto_atTop (a:=1/4-ε) (by linarith)
  filter_upwards [pair_mean_eventually, pair_volume_eventually, pair_fourth_power_error hε₀,
    hR.eventually_ge_atTop (2:ℕ), hz.eventually_ge_atTop (16:ℕ),
    eventually_ge_atTop (2:ℕ)] with N hmean hvol hpow hR hz hN he
  let y := chenPowerLevel (1/512) N + 1
  change ∀ d : ℕ, 0 < d → chenPowerLevel (1/4 - ε) N ≤ N / d →
    (∀ p : ℕ, p.Prime → p < y → ¬p ∣ d) →
    ((chenRoughThreePrimePairs N d y).card:ℝ) ≤
      (2:ℝ)^22 * chenSieveScale chenCanonicalU N / (d:ℝ)
  intro d hd hdz hcop
  let R := chenPowerLevel (1/32) N
  let G := sieveMass (pairSievePrimes y) R (pairG N)
  let X := N / d
  let L := Real.log (N:ℝ)
  have hGinv : 1 / G ≤ 2 * pairV N y :=
    pair_mass_reciprocal_le (by dsimp [R]; omega) hmean
  have hX : (16:ℝ) ≤ X := by exact_mod_cast hz.trans hdz
  have hXd : (X:ℝ) ≤ (N:ℝ) / (d:ℝ) := Nat.cast_div_le
  have hd' : (0:ℝ) < d := Nat.cast_pos.2 hd
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hU := chenCanonicalU_ge_half he hN
  have hscale : chenSieveScale chenCanonicalU N / (d:ℝ) =
      ((N:ℝ)/(d:ℝ)) * (chenCanonicalU N / L^2) := by unfold chenSieveScale L; ring
  have hT : 0 ≤ chenCanonicalU N / L^2 := div_nonneg (by linarith) (sq_nonneg _)
  have hzX : (chenPowerLevel (1/4-ε) N:ℝ) ≤ (X:ℝ) := Nat.cast_le.2 hdz
  have htail : 6 * (R:ℝ)^4 ≤ chenSieveScale chenCanonicalU N / (d:ℝ) := by
    rw [hscale, ← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hL)).2
    have hU' := mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ (N:ℝ)/(d:ℝ))
    change 12 * (R:ℝ)^4 * L^2 ≤ _ at hpow
    linarith only [hpow, hzX, hXd, hU']
  have hmain : (X:ℝ) / G + 1 / G ≤
      ((15:ℝ) * 512^2) * (chenSieveScale chenCanonicalU N / (d:ℝ)) := by
    have hb : (X:ℝ) + 1 ≤ (17:ℝ)/16 * ((N:ℝ) / (d:ℝ)) := by linarith only [hX, hXd]
    calc
      _ = ((X:ℝ) + 1) * (1/G) := by ring
      _ ≤ ((X:ℝ) + 1) * (2 * pairV N y) := mul_le_mul_of_nonneg_left hGinv (by positivity)
      _ ≤ ((17:ℝ)/16 * ((N:ℝ)/(d:ℝ))) * (((27:ℝ)/2 * 512^2) * chenCanonicalU N / L^2) := by
        exact mul_le_mul hb (hvol he)
          (mul_nonneg (by norm_num) (pairV_pos N y).le) (by positivity)
      _ = (((17:ℝ)/16) * ((27:ℝ)/2) * 512^2) *
          (((N:ℝ)/(d:ℝ)) * (chenCanonicalU N / L^2)) := by ring
      _ ≤ _ := by
        rw [hscale]
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg (by positivity) hT)
  have h := pair_card_le_mass (N:=N) (R:=R) hd (by dsimp [R]; omega) hcop
  change ((chenRoughThreePrimePairs N d y).card:ℝ) ≤ (X:ℝ)/G + 1/G + 6*(R:ℝ)^4 at h
  have hnneg : 0 ≤ chenSieveScale chenCanonicalU N / (d:ℝ) := by
    rw [hscale]
    exact mul_nonneg (by positivity) hT
  calc
    _ ≤ _ := h
    _ ≤ ((15:ℝ) * 512^2) * (chenSieveScale chenCanonicalU N / (d:ℝ)) +
        chenSieveScale chenCanonicalU N / (d:ℝ) := add_le_add hmain htail
    _ = ((15:ℝ) * 512^2 + 1) * (chenSieveScale chenCanonicalU N / (d:ℝ)) := by ring
    _ ≤ (2:ℝ)^22 * (chenSieveScale chenCanonicalU N / (d:ℝ)) :=
      mul_le_mul_of_nonneg_right (by norm_num) hnneg
    _ = _ := by ring

end FareyGoldbach
