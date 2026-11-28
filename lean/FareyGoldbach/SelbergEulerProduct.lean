import FareyGoldbach.SharpRankin
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.PrimeCounting

/-! # An elementary lower bound for the finite Euler product at one -/

open scoped BigOperators

namespace FareyGoldbach

/-- The prime factors of every positive integer at most `z` are at most `z`.
    Their reciprocals therefore occur in the finite Euler product, with total
    weight at least the `z`th harmonic number. -/
theorem prime_euler_log_le (z : ℕ) :
    Real.log ((z : ℝ) + 1) ≤ ∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ))⁻¹ := by
  classical
  let f : ℕ → ℝ := fun n => (n:ℝ)⁻¹
  have h₁ : f 1 = 1 := by simp [f]
  have hmul : ∀ {m n}, Nat.Coprime m n → f (m*n) = f m*f n := by
    intro m n _; simp [f, mul_comm]
  have hg {p : ℕ} (hp : p.Prime) : (p:ℝ)⁻¹ < 1 := by
    have hp' : (1:ℝ) < p := by exact_mod_cast hp.one_lt
    rw [inv_lt_one₀ (by linarith : (0:ℝ) < p)]; exact hp'
  have hs {p : ℕ} (hp : p.Prime) : Summable (fun n : ℕ => ‖f (p^n)‖) := by
    simpa [f] using summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ (p:ℝ)⁻¹) (hg hp)
  have hEuler := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum h₁ hmul hs (z+1)).2
  let s := Finset.Icc 1 z
  let emb : {n // n ∈ s} ↪ (z+1).smoothNumbers :=
    ⟨fun n => ⟨n.val, Nat.mem_smoothNumbers_of_lt (Finset.mem_Icc.mp n.property).1
        (Nat.lt_succ_of_le (Finset.mem_Icc.mp n.property).2)⟩,
      fun _ _ h => Subtype.ext (congrArg (fun n : (z+1).smoothNumbers => (n.val : ℕ)) h)⟩
  have hsub := hEuler.summable.sum_le_tsum (s.attach.map emb) (fun i _ => show 0 ≤ (i.val:ℝ)⁻¹ by positivity)
  rw [hEuler.tsum_eq] at hsub
  have hleft : ∑ i ∈ s.attach.map emb, f i.val = ∑ i ∈ s, (i:ℝ)⁻¹ := by
    simp only [Finset.sum_map, emb, f]
    exact Finset.sum_attach s (fun n => (n:ℝ)⁻¹)
  have hright : (∏ p ∈ (z+1).primesBelow, ∑' n : ℕ, f (p^n)) =
      ∏ p ∈ Nat.primesLE z, (1-1/(p:ℝ))⁻¹ := by
    apply Finset.prod_congr rfl
    intro p hp
    simpa [f, one_div] using tsum_geometric_of_lt_one (by positivity : (0:ℝ) ≤ (p:ℝ)⁻¹)
      (hg (Nat.prime_of_mem_primesBelow hp))
  have hh := log_add_one_le_harmonic z
  simp only [Nat.cast_add, Nat.cast_one, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
  exact hh.trans (hleft ▸ hright ▸ hsub)

/-- Sieve primes available to a reduced progression, after discarding primes below 11. -/
def progressionSievePrimes (r z : ℕ) : Finset ℕ :=
  (Nat.primesLE z).filter fun p => 11 ≤ p ∧ ¬ p ∣ r

/-- The omitted small primes cost an absolute factor; the omitted prime divisors
    of the modulus cost at most `r/φ(r)`. -/
theorem prime_euler_log_le_progression {r z : ℕ} (hr : 0 < r) :
    Real.log ((z:ℝ)+1) ≤ (2:ℝ)^10 * ((r:ℝ)/r.totient) *
      ∏ p ∈ progressionSievePrimes r z, (1 - 1/(p:ℝ))⁻¹ := by
  classical
  let f := fun p : ℕ => (1-1/(p:ℝ))⁻¹
  let s := Nat.primesLE z
  let large := s.filter (fun p => 11 ≤ p)
  let small := s.filter (fun p => ¬ 11 ≤ p)
  let bad := large.filter (fun p => p ∣ r)
  let good := progressionSievePrimes r z
  have hv (p : ℕ) (hp : p.Prime) : f p = (p:ℝ)/((p:ℝ)-1) := by
    have h : (1:ℝ) < p := by exact_mod_cast hp.one_lt
    dsimp [f]; field_simp [show (p:ℝ) ≠ 0 by linarith, show (p:ℝ)-1 ≠ 0 by linarith]
  have hbds (p : ℕ) (hp : p.Prime) : 1 ≤ f p ∧ f p ≤ 2 := by
    have h : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [hv p hp]; constructor
    · rw [le_div_iff₀ (by linarith)]; linarith
    · rw [div_le_iff₀ (by linarith)]; linarith
  have hsp (p : ℕ) (hp : p ∈ small) := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
  have hcard : small.card ≤ 10 := by
    have hsub : small ⊆ Finset.Icc 1 10 := by
      intro p hp
      exact Finset.mem_Icc.mpr ⟨(hsp p hp).pos, by have h := (Finset.mem_filter.mp hp).2; omega⟩
    exact (Finset.card_le_card hsub).trans (by decide)
  have hsmall : (∏ p ∈ small, f p) ≤ (2:ℝ)^10 := by
    calc (∏ p ∈ small, f p) ≤ ∏ _p ∈ small, (2:ℝ) := Finset.prod_le_prod₀
            (fun p hp => zero_le_one.trans (hbds p (hsp p hp)).1) (fun p hp => (hbds p (hsp p hp)).2)
      _ = (2:ℝ)^small.card := by simp
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hcard
  have hsub : bad ⊆ r.primeFactors := by
    intro p hp
    have hd := Finset.mem_filter.mp hp
    have hprime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hd.1).1).2
    exact Nat.mem_primeFactors.mpr ⟨hprime,hd.2,hr.ne'⟩
  have hnonneg : 0 ≤ (∏ p ∈ bad, f p) := Finset.prod_nonneg fun p hp =>
    zero_le_one.trans (hbds p (Nat.prime_of_mem_primeFactors (hsub hp))).1
  have hrest : 1 ≤ (∏ p ∈ r.primeFactors \ bad, f p) := by
    calc (1:ℝ) = ∏ _p ∈ r.primeFactors \ bad, (1:ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun p hp =>
        (hbds p (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1)).1)
  have hall : (∏ p ∈ r.primeFactors, f p) = (r:ℝ)/r.totient := by
    rw [div_totient_eq_prod_primeFactors hr]
    exact Finset.prod_congr rfl fun p hp => hv p (Nat.prime_of_mem_primeFactors hp)
  have hbad : (∏ p ∈ bad, f p) ≤ (r:ℝ)/r.totient := by
    rw [← hall, ← Finset.prod_sdiff hsub]; exact le_mul_of_one_le_left hnonneg hrest
  have heq : large.filter (fun p => ¬ p ∣ r) = good := by
    ext p; simp [large,good,s,progressionSievePrimes,and_assoc]
  have hbig := Finset.prod_filter_mul_prod_filter_not large (fun p => p ∣ r) f
  rw [heq] at hbig
  change (∏ p ∈ bad, f p) * (∏ p ∈ good, f p) = ∏ p ∈ large, f p at hbig
  have hparts := Finset.prod_filter_not_mul_prod_filter s (fun p => 11 ≤ p) f
  change (∏ p ∈ small, f p) * (∏ p ∈ large, f p) = ∏ p ∈ s, f p at hparts
  have hgood : 0 ≤ ∏ p ∈ good, f p := Finset.prod_nonneg fun p hp =>
    zero_le_one.trans (hbds p (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2).1
  apply (prime_euler_log_le z).trans
  change (∏ p ∈ s, f p) ≤ (2:ℝ)^10 * ((r:ℝ)/r.totient) * ∏ p ∈ good, f p
  rw [←hparts,←hbig,←mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hsmall hbad hnonneg (by positivity)) hgood

end FareyGoldbach

