import FareyGoldbach.Defs
import FareyGoldbach.CharacterBound
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factors
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Module C: Ramanujan Sums, Finite Euler Product Lower Bound & Quartic Convolution

This module proves (for **arbitrary positive integers** `r ≥ 1`, odd or even, prime or composite):
1. `ramanujanSum_mul_coprime`: invariance under multiplication by a coprime integer.
2. `ramanujanSum_one`, `ramanujanSum_prime`, `ramanujanSum_mul_of_coprime`: exact evaluation
   and multiplicativity of Ramanujan sums.
3. `ramanujanSum_right_one_eq_moebius`: `ramanujanSum q 1 = μ(q)` for all `q ≥ 1`.
4. `finiteEulerProd_ge_half`: for all `r ≥ 1`, `Even n`, `2 ≤ Q₀`, the finite Euler product
   `∏_{p ≤ Q₀, p ∤ r} (1 + A_p(r, n)) ≥ 1 / 2`.
5. `singularTrunc_re_lower`: via Rankin's trick (`Q₀^(-1/2) ∏ (1 + √p |A_p|)`) with an
   explicit telescoping `k^(-3/2)` bound and elementary `p^(1/16)` bound for `p ∣ n`,
   `Re(singularTrunc r n Q₀) ≥ 1 / 4` whenever `Q₀` is large enough relative to `n^(1/8)`.
6. `quarticBump_conv_lower`: elementary interval lower bound on the discrete
   quartic-bump convolution `∑_{j₁ + j₂ = k} w((r*j₁+b₁)/Y) w((r*j₂+b₂)/Y) ≥ (1/32768) * (Y/r)`.
-/

open scoped BigOperators

namespace FareyGoldbach

section RealProdHelpers

lemma real_prod_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hfga : f a ≤ g a := hfg a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfgs : ∀ i ∈ s, f i ≤ g i := fun i hi => hfg i (Finset.mem_insert_of_mem hi)
    exact mul_le_mul hfga (ih hfs hfgs) (Finset.prod_nonneg hfs) (hfa.trans hfga)

lemma real_prod_le_one {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ s, f i ≤ 1) :
    ∏ i ∈ s, f i ≤ 1 := by
  simpa using real_prod_le_prod s f (fun _ => 1) hf0 hf1

end RealProdHelpers

section Ramanujan

lemma ramanujanSum_one (n : ℕ) : ramanujanSum 1 n = 1 := by
  unfold ramanujanSum
  have h : (Finset.range 1).filter (fun a => Nat.Coprime a 1) = {0} := by
    ext a; simp
  rw [h, Finset.sum_singleton]
  simp [e_zero]

/-- Multiplying `n` by an integer `m` coprime to `q` preserves `ramanujanSum q n`. -/
lemma ramanujanSum_mul_coprime {q m : ℕ} (hq : 0 < q) (hm : Nat.Coprime m q) (n : ℕ) :
    ramanujanSum q (m * n) = ramanujanSum q n := by
  unfold ramanujanSum
  have : NeZero q := ⟨hq.ne'⟩
  refine Finset.sum_bij (fun a _ => (a * m) % q) ?_ ?_ ?_ ?_
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hq, ?_⟩
    rw [Nat.Coprime, Nat.ModEq.gcd_eq (Nat.mod_modEq (a * m) q)]
    exact ha'.2.mul_left hm
  · intro a₁ ha₁ a₂ ha₂ hEq
    have h1 := Finset.mem_filter.mp ha₁
    have h2 := Finset.mem_filter.mp ha₂
    have hlt1 : a₁ < q := Finset.mem_range.mp h1.1
    have hlt2 : a₂ < q := Finset.mem_range.mp h2.1
    have hmod : a₁ * m ≡ a₂ * m [MOD q] := hEq
    have hcancel : a₁ ≡ a₂ [MOD q] := Nat.ModEq.cancel_right_of_coprime hm.symm hmod
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hcancel
  · intro b hb
    have hb' := Finset.mem_filter.mp hb
    have hblt : b < q := Finset.mem_range.mp hb'.1
    have hm_unit : IsUnit (m : ZMod q) := (ZMod.isUnit_iff_coprime m q).2 hm
    let a : ℕ := ((b : ZMod q) * (m : ZMod q)⁻¹).val
    have halt : a < q := ZMod.val_lt _
    have ham_cast : ((a * m : ℕ) : ZMod q) = (b : ZMod q) := by
      simp only [a, Nat.cast_mul, ZMod.natCast_zmod_val, mul_assoc]
      have h1 : (m : ZMod q)⁻¹ * (m : ZMod q) = 1 :=
        (ZMod.inv_mul_eq_one_of_isUnit hm_unit (m : ZMod q)).2 rfl
      rw [h1, mul_one]
    have ham_mod : (a * m) % q = b := by
      have h := (ZMod.natCast_eq_natCast_iff _ _ _).1 ham_cast
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hblt] at h
    have ha_cop : Nat.Coprime a q := by
      have hmul_cop : Nat.Coprime (a * m) q := by
        rw [Nat.Coprime, ← Nat.ModEq.gcd_eq (Nat.mod_modEq (a * m) q), ham_mod]
        exact hb'.2
      exact hmul_cop.coprime_dvd_left (dvd_mul_right a m)
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr halt, ha_cop⟩, ham_mod⟩
  · intro a _
    have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
    let k : ℕ := (a * m) / q
    let rem : ℕ := (a * m) % q
    have hdiv : q * k + rem = a * m := Nat.div_add_mod (a * m) q
    change e ((a : ℝ) * ((m * n : ℕ) : ℝ) / (q : ℝ)) = e ((rem : ℝ) * (n : ℝ) / (q : ℝ))
    refine e_eq_of_sub_int (k := ((k * n : ℕ) : ℤ)) ?_
    have hdivR : (q : ℝ) * (k : ℝ) + (rem : ℝ) = (a : ℝ) * (m : ℝ) := by exact_mod_cast hdiv
    field_simp [hqR]
    push_cast
    linear_combination (n : ℝ) * hdivR.symm

/-- Exact value of `ramanujanSum p n` for prime `p`. -/
lemma ramanujanSum_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ramanujanSum p n = if p ∣ n then ((p - 1 : ℕ) : ℂ) else -1 := by
  unfold ramanujanSum
  have hp_pos : 0 < p := hp.pos
  have hfilt : (Finset.range p).filter (fun a => Nat.Coprime a p) =
      (Finset.range p).erase 0 := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    constructor
    · rintro ⟨hlt, hcop⟩
      refine ⟨?_, hlt⟩
      intro ha0; subst ha0
      have : p = 1 := by simpa [Nat.coprime_zero_left] using hcop
      exact hp.ne_one this
    · rintro ⟨hne0, hlt⟩
      refine ⟨hlt, ?_⟩
      exact (hp.coprime_iff_not_dvd.2 (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hne0) hlt)).symm
  rw [hfilt]
  have hfull : ∑ a ∈ Finset.range p, e ((a : ℝ) * (n : ℝ) / (p : ℝ)) =
      if p ∣ n then (p : ℂ) else 0 := by
    have hpow : ∀ a : ℕ, e ((a : ℝ) * (n : ℝ) / (p : ℝ)) = (e ((n : ℝ) / (p : ℝ))) ^ a := by
      intro a
      rw [← e_nat_mul]
      congr 1; ring
    have hsum : ∑ a ∈ Finset.range p, e ((a : ℝ) * (n : ℝ) / (p : ℝ)) =
        ∑ a ∈ Finset.range p, (e ((n : ℝ) / (p : ℝ))) ^ a :=
      Finset.sum_congr rfl fun a _ => hpow a
    rw [hsum]
    split_ifs with hdvd
    · obtain ⟨k, rfl⟩ := hdvd
      have he1 : e (((p * k : ℕ) : ℝ) / (p : ℝ)) = 1 := by
        have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp_pos.ne'
        have h : ((p * k : ℕ) : ℝ) / (p : ℝ) = (k : ℝ) := by push_cast; field_simp [hpR]
        rw [h]; exact_mod_cast e_int (k : ℤ)
      have he1' : e ((p : ℝ) * (k : ℝ) / (p : ℝ)) = 1 := by simpa [Nat.cast_mul] using he1
      have hterm : ∀ a ∈ Finset.range p, (e (((p * k : ℕ) : ℝ) / (p : ℝ))) ^ a = 1 := by
        intro a _; rw [he1, one_pow]
      have : ∑ a ∈ Finset.range p, (e (((p * k : ℕ) : ℝ) / (p : ℝ))) ^ a = (p : ℂ) := by
        rw [Finset.sum_congr rfl hterm]; simp
      simpa [Nat.cast_mul] using this
    · set z : ℂ := e ((n : ℝ) / (p : ℝ))
      have hz_ne : z ≠ 1 := by
        intro h1
        obtain ⟨k, hk⟩ := (e_eq_one_iff _).1 h1
        have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp_pos.ne'
        have hnR : (n : ℝ) = (k : ℝ) * (p : ℝ) := (div_eq_iff hpR).1 hk
        have hnZ : (n : ℤ) = k * (p : ℤ) := by exact_mod_cast hnR
        have hdivZ : (p : ℤ) ∣ (n : ℤ) := ⟨k, by linarith⟩
        exact hdvd (Int.ofNat_dvd.1 hdivZ)
      have hz_pow : z ^ p = 1 := by
        rw [← e_nat_mul]
        have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp_pos.ne'
        have h : (p : ℝ) * ((n : ℝ) / (p : ℝ)) = (n : ℝ) := mul_div_cancel₀ _ hpR
        rw [h]; exact_mod_cast e_int (n : ℤ)
      have hmul : (z - 1) * ∑ a ∈ Finset.range p, z ^ a = 0 := by
        rw [mul_comm, geom_sum_mul, hz_pow, sub_self]
      exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hz_ne)
  have h0_mem : (0 : ℕ) ∈ Finset.range p := Finset.mem_range.mpr hp_pos
  have hsplit := Finset.add_sum_erase (Finset.range p)
    (fun a => e ((a : ℝ) * (n : ℝ) / (p : ℝ))) h0_mem
  have h0val : e ((0 : ℕ) * (n : ℝ) / (p : ℝ)) = 1 := by simp [e_zero]
  rw [h0val, hfull] at hsplit
  split_ifs at hsplit ⊢ with hdvd
  · have hp1 : ((p - 1 : ℕ) : ℂ) + 1 = (p : ℂ) := by
      have : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
      exact_mod_cast this
    linear_combination hsplit - hp1
  · linear_combination hsplit

/-- Multiplicativity of `ramanujanSum` in `q` for coprime `q₁, q₂`. -/
lemma ramanujanSum_mul_of_coprime {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hcop : Nat.Coprime q₁ q₂) (n : ℕ) :
    ramanujanSum (q₁ * q₂) n = ramanujanSum q₁ n * ramanujanSum q₂ n := by
  unfold ramanujanSum
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij
    (fun p _ => (p.1 * q₂ + p.2 * q₁) % (q₁ * q₂)) ?_ ?_ ?_ ?_
  · intro p hp
    have hp' := Finset.mem_product.mp hp
    have h1 := (Finset.mem_filter.mp hp'.1).2
    have h2 := (Finset.mem_filter.mp hp'.2).2
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq₁ hq₂), ?_⟩
    have hgcd_mod : ∀ m, m ∣ q₁ * q₂ → Nat.Coprime (p.1 * q₂ + p.2 * q₁) m →
        Nat.Coprime ((p.1 * q₂ + p.2 * q₁) % (q₁ * q₂)) m := by
      intro m hm hc
      have hmod : (p.1 * q₂ + p.2 * q₁) % (q₁ * q₂) ≡ p.1 * q₂ + p.2 * q₁ [MOD m] :=
        (Nat.mod_modEq _ _).of_dvd hm
      rw [Nat.Coprime, Nat.ModEq.gcd_eq hmod]
      exact hc
    apply Nat.Coprime.mul_right
    · apply hgcd_mod q₁ (dvd_mul_right q₁ q₂)
      have hmod1 : p.1 * q₂ + p.2 * q₁ ≡ p.1 * q₂ [MOD q₁] := by
        rw [Nat.ModEq, Nat.add_mul_mod_self_right]
      rw [Nat.Coprime, Nat.ModEq.gcd_eq hmod1]
      exact h1.mul_left hcop.symm
    · apply hgcd_mod q₂ (dvd_mul_left q₂ q₁)
      have hmod2 : p.1 * q₂ + p.2 * q₁ ≡ p.2 * q₁ [MOD q₂] := by
        rw [Nat.ModEq, add_comm, Nat.add_mul_mod_self_right]
      rw [Nat.Coprime, Nat.ModEq.gcd_eq hmod2]
      exact h2.mul_left hcop
  · intro p₁ hp₁ p₂ hp₂ hEq
    have h1 := Finset.mem_product.mp hp₁
    have h2 := Finset.mem_product.mp hp₂
    have h11 := Finset.mem_range.mp (Finset.mem_filter.mp h1.1).1
    have h12 := Finset.mem_range.mp (Finset.mem_filter.mp h1.2).1
    have h21 := Finset.mem_range.mp (Finset.mem_filter.mp h2.1).1
    have h22 := Finset.mem_range.mp (Finset.mem_filter.mp h2.2).1
    have hmod : p₁.1 * q₂ + p₁.2 * q₁ ≡ p₂.1 * q₂ + p₂.2 * q₁ [MOD q₁ * q₂] := hEq
    have hmod1 : p₁.1 * q₂ ≡ p₂.1 * q₂ [MOD q₁] := by
      have hm := hmod.of_dvd (dvd_mul_right q₁ q₂)
      simpa [Nat.ModEq, Nat.add_mul_mod_self_right] using hm
    have hmod2 : p₁.2 * q₁ ≡ p₂.2 * q₁ [MOD q₂] := by
      have hm := hmod.of_dvd (dvd_mul_left q₂ q₁)
      simpa [Nat.ModEq, add_comm, Nat.add_mul_mod_self_right] using hm
    have heq1 : p₁.1 = p₂.1 := by
      have hc := Nat.ModEq.cancel_right_of_coprime hcop hmod1
      rwa [Nat.ModEq, Nat.mod_eq_of_lt h11, Nat.mod_eq_of_lt h21] at hc
    have heq2 : p₁.2 = p₂.2 := by
      have hc := Nat.ModEq.cancel_right_of_coprime hcop.symm hmod2
      rwa [Nat.ModEq, Nat.mod_eq_of_lt h12, Nat.mod_eq_of_lt h22] at hc
    exact Prod.ext heq1 heq2
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    have halt : a < q₁ * q₂ := Finset.mem_range.mp ha'.1
    have : NeZero q₁ := ⟨hq₁.ne'⟩
    have : NeZero q₂ := ⟨hq₂.ne'⟩
    have hq2_unit : IsUnit (q₂ : ZMod q₁) := (ZMod.isUnit_iff_coprime q₂ q₁).2 hcop.symm
    have hq1_unit : IsUnit (q₁ : ZMod q₂) := (ZMod.isUnit_iff_coprime q₁ q₂).2 hcop
    let a₁ : ℕ := ((a : ZMod q₁) * (q₂ : ZMod q₁)⁻¹).val
    let a₂ : ℕ := ((a : ZMod q₂) * (q₁ : ZMod q₂)⁻¹).val
    have ha1_lt : a₁ < q₁ := ZMod.val_lt _
    have ha2_lt : a₂ < q₂ := ZMod.val_lt _
    have h1_mod : a₁ * q₂ ≡ a [MOD q₁] := by
      have hc : ((a₁ * q₂ : ℕ) : ZMod q₁) = (a : ZMod q₁) := by
        simp only [a₁, Nat.cast_mul, ZMod.natCast_zmod_val, mul_assoc]
        rw [(ZMod.inv_mul_eq_one_of_isUnit hq2_unit (q₂ : ZMod q₁)).2 rfl, mul_one]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hc
    have h2_mod : a₂ * q₁ ≡ a [MOD q₂] := by
      have hc : ((a₂ * q₁ : ℕ) : ZMod q₂) = (a : ZMod q₂) := by
        simp only [a₂, Nat.cast_mul, ZMod.natCast_zmod_val, mul_assoc]
        rw [(ZMod.inv_mul_eq_one_of_isUnit hq1_unit (q₁ : ZMod q₂)).2 rfl, mul_one]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hc
    have hcomb1 : a₁ * q₂ + a₂ * q₁ ≡ a [MOD q₁] := by
      have h0 : a₁ * q₂ + a₂ * q₁ ≡ a₁ * q₂ [MOD q₁] := by
        rw [Nat.ModEq, Nat.add_mul_mod_self_right]
      exact h0.trans h1_mod
    have hcomb2 : a₁ * q₂ + a₂ * q₁ ≡ a [MOD q₂] := by
      have h0 : a₁ * q₂ + a₂ * q₁ ≡ a₂ * q₁ [MOD q₂] := by
        rw [Nat.ModEq, add_comm, Nat.add_mul_mod_self_right]
      exact h0.trans h2_mod
    have hcomb : a₁ * q₂ + a₂ * q₁ ≡ a [MOD q₁ * q₂] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hcomb1, hcomb2⟩
    have ha1_cop : Nat.Coprime a₁ q₁ := by
      have hca : Nat.Coprime a q₁ := ha'.2.coprime_dvd_right (dvd_mul_right q₁ q₂)
      have hmul : Nat.Coprime (a₁ * q₂) q₁ := by
        rw [Nat.Coprime, Nat.ModEq.gcd_eq h1_mod]; exact hca
      exact hmul.coprime_dvd_left (dvd_mul_right a₁ q₂)
    have ha2_cop : Nat.Coprime a₂ q₂ := by
      have hca : Nat.Coprime a q₂ := ha'.2.coprime_dvd_right (dvd_mul_left q₂ q₁)
      have hmul : Nat.Coprime (a₂ * q₁) q₂ := by
        rw [Nat.Coprime, Nat.ModEq.gcd_eq h2_mod]; exact hca
      exact hmul.coprime_dvd_left (dvd_mul_right a₂ q₁)
    refine ⟨(a₁, a₂), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha1_lt, ha1_cop⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha2_lt, ha2_cop⟩⟩, ?_⟩
    rwa [Nat.ModEq, Nat.mod_eq_of_lt halt] at hcomb
  · intro p _
    rw [← e_add]
    have hq1R : (q₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq₁.ne'
    have hq2R : (q₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq₂.ne'
    let k : ℕ := (p.1 * q₂ + p.2 * q₁) / (q₁ * q₂)
    let rem : ℕ := (p.1 * q₂ + p.2 * q₁) % (q₁ * q₂)
    have hdiv : (q₁ * q₂) * k + rem = p.1 * q₂ + p.2 * q₁ := Nat.div_add_mod _ _
    change e ((p.1 : ℝ) * (n : ℝ) / (q₁ : ℝ) + (p.2 : ℝ) * (n : ℝ) / (q₂ : ℝ)) =
      e ((rem : ℝ) * (n : ℝ) / ((q₁ * q₂ : ℕ) : ℝ))
    refine e_eq_of_sub_int (k := ((k * n : ℕ) : ℤ)) ?_
    have hdivR : ((q₁ : ℝ) * (q₂ : ℝ)) * (k : ℝ) + (rem : ℝ) =
        (p.1 : ℝ) * (q₂ : ℝ) + (p.2 : ℝ) * (q₁ : ℝ) := by exact_mod_cast hdiv
    push_cast
    field_simp [hq1R, hq2R]
    linear_combination (n : ℝ) * hdivR.symm

/-- For every `q ≥ 1`, `ramanujanSum q 1 = μ(q)`. -/
theorem ramanujanSum_right_one_eq_moebius {q : ℕ} (hq : 0 < q) :
    ramanujanSum q 1 = (ArithmeticFunction.moebius q : ℂ) := by
  by_cases hsf : Squarefree q
  · induction hcard : q.primeFactors.card generalizing q with
    | zero =>
      have hq1 : q = 1 := by
        by_contra hne
        obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hne
        have hmem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdvd, hq.ne'⟩
        have hpos : 0 < q.primeFactors.card := Finset.card_pos.mpr ⟨p, hmem⟩
        omega
      subst hq1
      simp [ramanujanSum_one]
    | succ k ih =>
      have hne : q.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨p, hp_mem⟩ := hne
      have hp : p.Prime := (Nat.mem_primeFactors.mp hp_mem).1
      have hp_dvd : p ∣ q := (Nat.mem_primeFactors.mp hp_mem).2.1
      obtain ⟨m, rfl⟩ := hp_dvd
      have hm_pos : 0 < m := Nat.pos_of_mul_pos_left hq
      have hcop : Nat.Coprime p m := by
        apply hp.coprime_iff_not_dvd.2
        intro hdvd
        have hsq : p * p ∣ p * m := mul_dvd_mul_left p hdvd
        exact hp.not_isUnit (hsf p hsq)
      have hmsf : Squarefree m := hsf.of_mul_right
      have hpf : (p * m).primeFactors = insert p m.primeFactors := by
        rw [Nat.primeFactors_mul hp.ne_zero hm_pos.ne', hp.primeFactors]
        simp
      have hp_not_mem : p ∉ m.primeFactors := by
        intro hm'
        have hd := (Nat.mem_primeFactors.mp hm').2.1
        exact (hp.coprime_iff_not_dvd.1 hcop) hd
      have hcard_m : m.primeFactors.card = k := by
        rw [hpf, Finset.card_insert_of_notMem hp_not_mem] at hcard
        omega
      rw [ramanujanSum_mul_of_coprime hp.pos hm_pos hcop 1,
          ramanujanSum_prime hp 1, ih hm_pos hmsf hcard_m]
      have hnot_dvd : ¬ (p ∣ 1) := fun h => hp.ne_one (Nat.dvd_one.mp h)
      simp only [hnot_dvd, ↓reduceIte]
      have hmu_mul : ArithmeticFunction.moebius (p * m) =
          ArithmeticFunction.moebius p * ArithmeticFunction.moebius m :=
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
      rw [hmu_mul, ArithmeticFunction.moebius_apply_prime hp]
      push_cast; ring
  · have hmu0 : ArithmeticFunction.moebius q = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
    rw [hmu0, Int.cast_zero]
    rw [Nat.squarefree_iff_prime_squarefree] at hsf
    push Not at hsf
    obtain ⟨p, hp, hpp_dvd⟩ := hsf
    obtain ⟨t, ht⟩ := hpp_dvd
    have ht_pos : 0 < t := by
      by_contra ht0
      have : t = 0 := by omega
      subst this; simp at ht; omega
    have hq_eq : q = p * (p * t) := by rw [ht]; ring
    let d : ℕ := p * t
    have hqd : q = p * d := hq_eq
    have hsum_eq : ramanujanSum q 1 = e (1 / (p : ℝ)) * ramanujanSum q 1 := by
      unfold ramanujanSum
      rw [Finset.mul_sum]
      symm
      refine Finset.sum_bij (fun a _ => (a + d) % q) ?_ ?_ ?_ ?_
      · intro a ha
        have ha' := Finset.mem_filter.mp ha
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨Nat.mod_lt _ hq, ?_⟩
        rw [Nat.Coprime, Nat.ModEq.gcd_eq (Nat.mod_modEq (a + d) q), ← Nat.Coprime]
        apply Nat.coprime_of_dvd
        intro s hs hs1 hs2
        by_cases hsp : s = p
        · have hsd : s ∣ d := hsp ▸ dvd_mul_right p t
          have hsa : s ∣ a := (Nat.dvd_add_left hsd).mp hs1
          have h1 : s ∣ 1 := by
            have := Nat.dvd_gcd hsa hs2
            rwa [ha'.2.gcd_eq_one] at this
          exact hs.ne_one (Nat.dvd_one.mp h1)
        · have hsd : s ∣ d := by
            rw [hqd] at hs2
            exact (hs.dvd_mul.mp hs2).resolve_left fun h =>
              hsp ((Nat.prime_dvd_prime_iff_eq hs hp).mp h)
          have hsa : s ∣ a := (Nat.dvd_add_left hsd).mp hs1
          have h1 : s ∣ 1 := by
            have := Nat.dvd_gcd hsa hs2
            rwa [ha'.2.gcd_eq_one] at this
          exact hs.ne_one (Nat.dvd_one.mp h1)
      · intro a₁ ha₁ a₂ ha₂ hEq
        have hlt1 := Finset.mem_range.mp (Finset.mem_filter.mp ha₁).1
        have hlt2 := Finset.mem_range.mp (Finset.mem_filter.mp ha₂).1
        have hmod : a₁ + d ≡ a₂ + d [MOD q] := hEq
        have hc := Nat.ModEq.add_right_cancel' d hmod
        rwa [Nat.ModEq, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hc
      · intro b hb
        have hb' := Finset.mem_filter.mp hb
        have hblt := Finset.mem_range.mp hb'.1
        let a : ℕ := (b + (p - 1) * d) % q
        have hab : (a + d) % q = b := by
          have hmod1 : a + d ≡ b + (p - 1) * d + d [MOD q] :=
            Nat.ModEq.add_right d (Nat.mod_modEq _ q)
          have hsum_d : b + (p - 1) * d + d = b + q := by
            have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
            calc b + (p - 1) * d + d = b + (p - 1 + 1) * d := by ring
              _ = b + p * d := by rw [hp1]
              _ = b + q := by rw [hqd]
          have hmod2 : a + d ≡ b [MOD q] := by
            rw [hsum_d] at hmod1
            exact hmod1.trans (by rw [Nat.ModEq, Nat.add_mod_right])
          rwa [Nat.ModEq, Nat.mod_eq_of_lt hblt] at hmod2
        have ha_cop : Nat.Coprime a q := by
          apply Nat.coprime_of_dvd
          intro s hs hs1 hs2
          have hsa_mod : s ∣ b + (p - 1) * d := by
            have hmod : a ≡ b + (p - 1) * d [MOD q] := Nat.mod_modEq _ q
            exact (Nat.ModEq.dvd_iff (hmod.of_dvd hs2) (dvd_refl s)).1 hs1
          by_cases hsp : s = p
          · subst hsp
            have hpd : s ∣ (s - 1) * d := dvd_mul_of_dvd_right (dvd_mul_right s t) _
            have hsb : s ∣ b := (Nat.dvd_add_left hpd).mp hsa_mod
            have h1 : s ∣ 1 := by
              have := Nat.dvd_gcd hsb hs2
              rwa [hb'.2.gcd_eq_one] at this
            exact hs.ne_one (Nat.dvd_one.mp h1)
          · have hsd : s ∣ d := by
              rw [hqd] at hs2
              exact (hs.dvd_mul.mp hs2).resolve_left fun h =>
                hsp ((Nat.prime_dvd_prime_iff_eq hs hp).mp h)
            have hpd : s ∣ (p - 1) * d := dvd_mul_of_dvd_right hsd _
            have hsb : s ∣ b := (Nat.dvd_add_left hpd).mp hsa_mod
            have h1 : s ∣ 1 := by
              have := Nat.dvd_gcd hsb hs2
              rwa [hb'.2.gcd_eq_one] at this
            exact hs.ne_one (Nat.dvd_one.mp h1)
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq), ha_cop⟩, hab⟩
      · intro a _
        rw [← e_add]
        have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
        have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
        let k : ℕ := (a + d) / q
        let rem : ℕ := (a + d) % q
        have hdiv : q * k + rem = a + d := Nat.div_add_mod _ _
        change e (1 / (p : ℝ) + (a : ℝ) * ((1 : ℕ) : ℝ) / (q : ℝ)) =
          e ((rem : ℝ) * ((1 : ℕ) : ℝ) / (q : ℝ))
        refine e_eq_of_sub_int (k := (k : ℤ)) ?_
        have hdivR : (q : ℝ) * (k : ℝ) + (rem : ℝ) = (a : ℝ) + (d : ℝ) := by exact_mod_cast hdiv
        have hqdR : (q : ℝ) = (p : ℝ) * (d : ℝ) := by exact_mod_cast hqd
        push_cast
        field_simp [hqR, hpR]
        linear_combination (p : ℝ) * hdivR.symm + hqdR
    have he_ne : e (1 / (p : ℝ)) ≠ 1 := by
      intro h1
      obtain ⟨k, hk⟩ := (e_eq_one_iff _).1 h1
      have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
      have h1R : (1 : ℝ) = (k : ℝ) * (p : ℝ) := (div_eq_iff hpR).1 hk
      have h1Z : (1 : ℤ) = k * (p : ℤ) := by exact_mod_cast h1R
      have hdvd : p ∣ 1 := Int.ofNat_dvd.1 ⟨k, by rw [mul_comm]; exact_mod_cast h1Z⟩
      exact hp.ne_one (Nat.dvd_one.mp hdvd)
    have hmul : (e (1 / (p : ℝ)) - 1) * ramanujanSum q 1 = 0 := by
      linear_combination -hsum_eq
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr he_ne)

end Ramanujan

section FiniteEulerProduct

/-- Real local factor `A_p(r, n)` in the finite Euler product for `singularTrunc r n Q₀`. -/
noncomputable def localFactor (r n p : ℕ) : ℝ :=
  if p ∣ r then 0
  else if p ∣ n then 1 / ((p : ℝ) - 1)
  else -(1 / (((p : ℝ) - 1) ^ 2))

lemma localFactor_eq_complex {r n p : ℕ} (hp : p.Prime) :
    (localFactor r n p : ℂ) =
      if Nat.Coprime p r then
        (ArithmeticFunction.moebius p : ℂ) ^ 2 * ramanujanSum p n / (p.totient : ℂ) ^ 2
      else 0 := by
  unfold localFactor
  by_cases hpr : p ∣ r
  · have hncop : ¬ Nat.Coprime p r := by rwa [hp.coprime_iff_not_dvd, not_not]
    simp [hpr, hncop]
  · have hcop : Nat.Coprime p r := hp.coprime_iff_not_dvd.2 hpr
    rw [ite_eq_right hpr, ite_eq_left hcop]
    rw [ramanujanSum_prime hp n, ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
    have hp1 : ((p - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.sub_pos_of_lt hp.one_lt).ne'
    have hpR : ((p : ℝ) - 1) = ((p - 1 : ℕ) : ℝ) := (Nat.cast_sub hp.one_lt.le).symm
    by_cases hpn : p ∣ n
    · simp only [hpn, ↓reduceIte, hpR]
      push_cast
      field_simp [hp1]
    · simp only [hpn, ↓reduceIte, hpR]
      push_cast
      ring

/-- Telescoping product: `∏_{j=2}^{m} (1 - 1/j²) = (m + 1) / (2 * m)` for `m ≥ 2`. -/
lemma prod_one_sub_inv_sq (m : ℕ) (hm : 2 ≤ m) :
    ∏ j ∈ Finset.Icc 2 m, (1 - 1 / ((j : ℝ) ^ 2)) = ((m : ℝ) + 1) / (2 * (m : ℝ)) := by
  induction m, hm using Nat.le_induction with
  | base =>
    norm_num [Finset.Icc_self]
  | succ k hk ih =>
    have hIcc : Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k + 1 ∉ Finset.Icc 2 k := by simp
    rw [hIcc, Finset.prod_insert hnot, ih]
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp [hk0, hk1]
    ring

/-- **Theorem C2.1 (Finite Euler product lower bound — odd and even composite `r`):**
For every `r ≥ 1`, `Even n`, and `2 ≤ Q₀`:
`∏_{p ≤ Q₀, p.Prime} (1 + localFactor r n p) ≥ 1 / 2`. -/
theorem finiteEulerProd_ge_half (r n Q₀ : ℕ) (hn : Even n) (hQ₀ : 2 ≤ Q₀) :
    (1 : ℝ) / 2 ≤
      ∏ p ∈ (Finset.Icc 1 Q₀).filter Nat.Prime, (1 + localFactor r n p) := by
  set S := (Finset.Icc 1 Q₀).filter Nat.Prime
  have h2_mem : 2 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hQ₀⟩, Nat.prime_two⟩
  have h2_ge : (1 : ℝ) ≤ 1 + localFactor r n 2 := by
    unfold localFactor
    have h2n : 2 ∣ n := even_iff_two_dvd.mp hn
    by_cases h2r : 2 ∣ r
    · simp [h2r]
    · simp only [h2r, h2n, ↓reduceIte]; norm_num
  rw [← Finset.mul_prod_erase S _ h2_mem]
  have hodd_ge : ∏ j ∈ Finset.Icc 2 Q₀, (1 - 1 / ((j : ℝ) ^ 2)) ≤
      ∏ p ∈ S.erase 2, (1 + localFactor r n p) := by
    let T : Finset ℕ := (S.erase 2).image (fun p => p - 1)
    have hT_sub : T ⊆ Finset.Icc 2 Q₀ := by
      intro j hj
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
      have hp_ne : p ≠ 2 := (Finset.mem_erase.mp hp).1
      have hp_mem := (Finset.mem_erase.mp hp).2
      have hprime : p.Prime := (Finset.mem_filter.mp hp_mem).2
      have hp_le : p ≤ Q₀ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp_mem).1).2
      have hp3 : 3 ≤ p := by have := hprime.two_le; omega
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hterm_le : ∀ j ∈ Finset.Icc 2 Q₀, (0 : ℝ) ≤ 1 - 1 / ((j : ℝ) ^ 2) ∧
        1 - 1 / ((j : ℝ) ^ 2) ≤ 1 := by
      intro j hj
      have hj2 : (2 : ℝ) ≤ j := Nat.cast_le.mpr (Finset.mem_Icc.mp hj).1
      have hsq : (4 : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
      constructor
      · have : 1 / ((j : ℝ) ^ 2) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
        linarith
      · have : (0 : ℝ) ≤ 1 / ((j : ℝ) ^ 2) := by positivity
        linarith
    have hprod_sub : ∏ j ∈ Finset.Icc 2 Q₀, (1 - 1 / ((j : ℝ) ^ 2)) ≤
        ∏ j ∈ T, (1 - 1 / ((j : ℝ) ^ 2)) := by
      rw [← Finset.prod_sdiff hT_sub]
      have h1 : ∏ j ∈ Finset.Icc 2 Q₀ \ T, (1 - 1 / ((j : ℝ) ^ 2)) ≤ 1 :=
        real_prod_le_one _ _
          (fun j hj => (hterm_le j (Finset.mem_sdiff.mp hj).1).1)
          (fun j hj => (hterm_le j (Finset.mem_sdiff.mp hj).1).2)
      have h2 : 0 ≤ ∏ j ∈ T, (1 - 1 / ((j : ℝ) ^ 2)) :=
        Finset.prod_nonneg fun j hj => (hterm_le j (hT_sub hj)).1
      nlinarith
    have hprod_T : ∏ j ∈ T, (1 - 1 / ((j : ℝ) ^ 2)) =
        ∏ p ∈ S.erase 2, (1 - 1 / (((p : ℝ) - 1) ^ 2)) := by
      rw [Finset.prod_image]
      · refine Finset.prod_congr rfl fun p hp => ?_
        have hprime : p.Prime := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2
        have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := Nat.cast_sub hprime.one_lt.le
        rw [hcast]
      · intro p₁ hp₁ p₂ hp₂ hEq
        have h1 : 1 ≤ p₁ := (Finset.mem_filter.mp (Finset.mem_erase.mp hp₁).2).2.one_lt.le
        have h2 : 1 ≤ p₂ := (Finset.mem_filter.mp (Finset.mem_erase.mp hp₂).2).2.one_lt.le
        dsimp at hEq
        omega
    have hprod_cmp : ∏ p ∈ S.erase 2, (1 - 1 / (((p : ℝ) - 1) ^ 2)) ≤
        ∏ p ∈ S.erase 2, (1 + localFactor r n p) := by
      refine real_prod_le_prod (S.erase 2) _ _ (fun p hp => ?_) (fun p hp => ?_)
      · have hp_ne : p ≠ 2 := (Finset.mem_erase.mp hp).1
        have hprime : p.Prime := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2
        have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hprime.two_le; omega)
        have hsq : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
        have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
        linarith
      · have hprime : p.Prime := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2
        have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr hprime.two_le
        unfold localFactor
        split_ifs
        · have : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
          linarith
        · have h1 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := by
            have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
            exact div_nonneg zero_le_one this.le
          have h2 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
          linarith
        · linarith
    exact hprod_sub.trans (hprod_T ▸ hprod_cmp)
  have hteles : (1 : ℝ) / 2 ≤ ∏ j ∈ Finset.Icc 2 Q₀, (1 - 1 / ((j : ℝ) ^ 2)) := by
    rw [prod_one_sub_inv_sq Q₀ hQ₀]
    have hQ0 : (0 : ℝ) < Q₀ := by positivity
    rw [div_le_div_iff₀ two_pos (by positivity)]
    linarith
  have hodd_half : (1 : ℝ) / 2 ≤ ∏ p ∈ S.erase 2, (1 + localFactor r n p) :=
    hteles.trans hodd_ge
  nlinarith

/-- Telescoping bound: `∑_{k ∈ Icc 2 m} 1 / (k * √k) ≤ 2`. -/
lemma sum_inv_mul_sqrt_le_two (m : ℕ) :
    ∑ k ∈ Finset.Icc 2 m, 1 / ((k : ℝ) * Real.sqrt (k : ℝ)) ≤ 2 := by
  have hstep : ∀ k ∈ Finset.Icc 2 m,
      1 / ((k : ℝ) * Real.sqrt (k : ℝ)) ≤
        2 * (1 / Real.sqrt ((k - 1 : ℕ) : ℝ) - 1 / Real.sqrt (k : ℝ)) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk_pos : (0 : ℝ) < k := by positivity
    have hk1_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
      have : 1 ≤ k - 1 := by omega
      exact_mod_cast Nat.pos_of_ne_zero (by omega : k - 1 ≠ 0)
    have hsk_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk_pos
    have hsk1_pos : 0 < Real.sqrt ((k - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hk1_pos
    have hsk1_le : Real.sqrt ((k - 1 : ℕ) : ℝ) ≤ Real.sqrt (k : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast Nat.sub_le k 1
    have hsq_diff : Real.sqrt (k : ℝ) ^ 2 - Real.sqrt ((k - 1 : ℕ) : ℝ) ^ 2 = 1 := by
      rw [Real.sq_sqrt hk_pos.le, Real.sq_sqrt hk1_pos.le, Nat.cast_sub (by omega : 1 ≤ k)]
      ring
    have hdiff : (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ)) *
        (Real.sqrt (k : ℝ) + Real.sqrt ((k - 1 : ℕ) : ℝ)) = 1 := by
      linarith [hsq_diff]
    have hsum_le : Real.sqrt (k : ℝ) + Real.sqrt ((k - 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (k : ℝ) := by
      linarith
    have hsub_ge : 1 / (2 * Real.sqrt (k : ℝ)) ≤
        Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hdiff, hsum_le, hsk_pos, hsk1_pos]
    have hprod_le : Real.sqrt ((k - 1 : ℕ) : ℝ) * Real.sqrt (k : ℝ) ≤ (k : ℝ) := by
      have h1 : Real.sqrt ((k - 1 : ℕ) : ℝ) * Real.sqrt (k : ℝ) ≤ Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) :=
        mul_le_mul_of_nonneg_right hsk1_le hsk_pos.le
      rw [Real.mul_self_sqrt hk_pos.le] at h1
      exact h1
    have hfrac : 1 / Real.sqrt ((k - 1 : ℕ) : ℝ) - 1 / Real.sqrt (k : ℝ) =
        (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ)) /
          (Real.sqrt ((k - 1 : ℕ) : ℝ) * Real.sqrt (k : ℝ)) := by
      field_simp [hsk1_pos.ne', hsk_pos.ne']
    rw [hfrac]
    have h1 : 1 / (2 * (k : ℝ) * Real.sqrt (k : ℝ)) ≤
        (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ)) /
          (Real.sqrt ((k - 1 : ℕ) : ℝ) * Real.sqrt (k : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (mul_pos hsk1_pos hsk_pos)]
      calc 1 * (Real.sqrt ((k - 1 : ℕ) : ℝ) * Real.sqrt (k : ℝ))
          ≤ (k : ℝ) := by linarith
        _ = (2 * (k : ℝ) * Real.sqrt (k : ℝ)) * (1 / (2 * Real.sqrt (k : ℝ))) := by
            field_simp [hsk_pos.ne']
        _ ≤ (2 * (k : ℝ) * Real.sqrt (k : ℝ)) * (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hsub_ge (by positivity)
        _ = (Real.sqrt (k : ℝ) - Real.sqrt ((k - 1 : ℕ) : ℝ)) * (2 * (k : ℝ) * Real.sqrt (k : ℝ)) :=
            mul_comm _ _
    linarith [show 2 * (1 / (2 * (k : ℝ) * Real.sqrt (k : ℝ))) = 1 / ((k : ℝ) * Real.sqrt (k : ℝ)) by ring]
  have hteles : ∀ m : ℕ, 2 ≤ m →
      ∑ k ∈ Finset.Icc 2 m, (1 / Real.sqrt ((k - 1 : ℕ) : ℝ) - 1 / Real.sqrt (k : ℝ)) =
        1 - 1 / Real.sqrt (m : ℝ) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      simp [Finset.Icc_self]
    | succ t ht ih =>
      have hIcc : Finset.Icc 2 (t + 1) = insert (t + 1) (Finset.Icc 2 t) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : t + 1 ∉ Finset.Icc 2 t := by simp
      rw [hIcc, Finset.sum_insert hnot, ih]
      simp only [Nat.add_sub_cancel]
      ring
  by_cases hm2 : 2 ≤ m
  · calc ∑ k ∈ Finset.Icc 2 m, 1 / ((k : ℝ) * Real.sqrt (k : ℝ))
        ≤ ∑ k ∈ Finset.Icc 2 m, 2 * (1 / Real.sqrt ((k - 1 : ℕ) : ℝ) - 1 / Real.sqrt (k : ℝ)) :=
          Finset.sum_le_sum hstep
      _ = 2 * ∑ k ∈ Finset.Icc 2 m, (1 / Real.sqrt ((k - 1 : ℕ) : ℝ) - 1 / Real.sqrt (k : ℝ)) := by
          rw [← Finset.mul_sum]
      _ = 2 * (1 - 1 / Real.sqrt (m : ℝ)) := by rw [hteles m hm2]
      _ ≤ 2 := by
          have : (0 : ℝ) ≤ 1 / Real.sqrt (m : ℝ) := by positivity
          linarith
  · have hemp : Finset.Icc 2 m = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hemp, Finset.sum_empty]
    norm_num

/-- Explicit constant for Rankin's product bound (written via `Real.exp` to avoid `npowRec` unfolding). -/
noncomputable def rankinConst : ℝ := Real.exp 2008

lemma rankinConst_pos : 0 < rankinConst := Real.exp_pos 2008

/-- Product bound for Rankin's trick:
`∏_{p ≤ Q₀, p.Prime} (1 + √p * |localFactor r n p|) ≤ rankinConst * n^(1/16)`. -/
lemma rankin_euler_product_bound (r n Q₀ : ℕ) (hn : 1 ≤ n) :
    ∏ p ∈ (Finset.Icc 1 Q₀).filter Nat.Prime, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) ≤
      rankinConst * (n : ℝ) ^ ((1 : ℝ) / 16) := by
  set S := (Finset.Icc 1 Q₀).filter Nat.Prime
  set S₁ := S.filter (fun p => p ∣ n)
  set S₂ := S.filter (fun p => ¬ (p ∣ n))
  have hsplit : ∏ p ∈ S, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) =
      (∏ p ∈ S₁, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|)) *
      (∏ p ∈ S₂, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|)) :=
    (Finset.prod_filter_mul_prod_filter_not S (fun p => p ∣ n) _).symm
  rw [hsplit]
  have hS2 : ∏ p ∈ S₂, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) ≤ Real.exp 8 := by
    have hle_exp : ∏ p ∈ S₂, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) ≤
        ∏ p ∈ S₂, Real.exp (4 / ((p : ℝ) * Real.sqrt (p : ℝ))) := by
      refine real_prod_le_prod S₂ _ _ (fun _ _ => by positivity) (fun p hp => ?_)
      have hp_mem := (Finset.mem_filter.mp hp).1
      have hndvd : ¬ (p ∣ n) := (Finset.mem_filter.mp hp).2
      have hprime : p.Prime := (Finset.mem_filter.mp hp_mem).2
      have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr hprime.two_le
      have hsp_pos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by linarith)
      have hterm : Real.sqrt (p : ℝ) * |localFactor r n p| ≤ 4 / ((p : ℝ) * Real.sqrt (p : ℝ)) := by
        unfold localFactor
        simp only [hndvd, ↓reduceIte]
        split_ifs
        · simp; positivity
        · rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2)]
          have hinv : 1 / ((p : ℝ) - 1) ^ 2 ≤ 4 / ((p : ℝ) ^ 2) := by
            rw [div_le_div_iff₀ (by nlinarith : (0 : ℝ) < ((p : ℝ) - 1) ^ 2) (by positivity)]
            nlinarith
          calc Real.sqrt (p : ℝ) * (1 / ((p : ℝ) - 1) ^ 2)
              ≤ Real.sqrt (p : ℝ) * (4 / (p : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hinv hsp_pos.le
            _ = 4 / ((p : ℝ) * Real.sqrt (p : ℝ)) := by
                have hpsq : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) :=
                  Real.mul_self_sqrt (by linarith)
                field_simp [hsp_pos.ne', (by linarith : (p : ℝ) ≠ 0)]
                nlinarith [hpsq]
      linarith [hterm, Real.add_one_le_exp (4 / ((p : ℝ) * Real.sqrt (p : ℝ)))]
    have hsum_le : ∑ p ∈ S₂, 4 / ((p : ℝ) * Real.sqrt (p : ℝ)) ≤ 8 := by
      have hsub : S₂ ⊆ Finset.Icc 2 Q₀ := by
        intro p hp
        have hp_mem := (Finset.mem_filter.mp hp).1
        have hprime : p.Prime := (Finset.mem_filter.mp hp_mem).2
        have hp_le := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp_mem).1).2
        exact Finset.mem_Icc.mpr ⟨hprime.two_le, hp_le⟩
      calc ∑ p ∈ S₂, 4 / ((p : ℝ) * Real.sqrt (p : ℝ))
          ≤ ∑ k ∈ Finset.Icc 2 Q₀, 4 / ((k : ℝ) * Real.sqrt (k : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ = 4 * ∑ k ∈ Finset.Icc 2 Q₀, 1 / ((k : ℝ) * Real.sqrt (k : ℝ)) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
        _ ≤ 4 * 2 := mul_le_mul_of_nonneg_left (sum_inv_mul_sqrt_le_two Q₀) (by norm_num)
        _ = 8 := by norm_num
    rw [← Real.exp_sum] at hle_exp
    exact hle_exp.trans (Real.exp_le_exp.mpr hsum_le)
  have hS1 : ∏ p ∈ S₁, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) ≤
      Real.exp 2000 * (n : ℝ) ^ ((1 : ℝ) / 16) := by
    set S1a := S₁.filter (fun p => p < 1000)
    set S1b := S₁.filter (fun p => ¬ (p < 1000))
    rw [← Finset.prod_filter_mul_prod_filter_not S₁ (fun p => p < 1000)]
    have hSmall : ∏ p ∈ S1a, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) ≤ Real.exp 2000 := by
      have hcard : S1a.card ≤ 1000 := by
        have hsub : S1a ⊆ Finset.range 1000 := fun p hp =>
          Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
        exact (Finset.card_le_card hsub).trans (by simp)
      have hterm : ∀ p ∈ S1a, 1 + Real.sqrt (p : ℝ) * |localFactor r n p| ≤ 3 := by
        intro p hp
        have hp_mem := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        have hprime : p.Prime := (Finset.mem_filter.mp hp_mem).2
        have hdvd : p ∣ n := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr hprime.two_le
        unfold localFactor
        simp only [hdvd, ↓reduceIte]
        split_ifs
        · norm_num
        · have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
          rw [abs_of_nonneg (div_nonneg zero_le_one hp1_pos.le)]
          have hsp_le : Real.sqrt (p : ℝ) ≤ (p : ℝ) :=
            Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
          have h2 : Real.sqrt (p : ℝ) * (1 / ((p : ℝ) - 1)) ≤ 2 := by
            rw [mul_one_div, div_le_iff₀ hp1_pos]
            linarith
          linarith
      have h3_le : (3 : ℝ) ≤ Real.exp 2 := by
        have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have h2 : (4 : ℝ) ≤ (Real.exp 1) ^ 2 := by nlinarith only [h1]
        rw [← Real.exp_nat_mul] at h2
        have h2eq : ((2 : ℕ) : ℝ) * 1 = 2 := by norm_num
        rw [h2eq] at h2
        linarith only [h2]
      calc ∏ p ∈ S1a, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|)
          ≤ ∏ _p ∈ S1a, Real.exp 2 :=
            real_prod_le_prod S1a _ _ (fun _ _ => by positivity) (fun p hp => (hterm p hp).trans h3_le)
        _ = (Real.exp 2) ^ S1a.card := by simp
        _ = Real.exp ((S1a.card : ℝ) * 2) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp 2000 := Real.exp_le_exp.mpr (by
            have : (S1a.card : ℝ) ≤ 1000 := Nat.cast_le.mpr hcard
            linarith)
    have hBig : ∏ p ∈ S1b, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) ≤
        (n : ℝ) ^ ((1 : ℝ) / 16) := by
      have hterm16 : ∀ p ∈ S1b, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) ^ 16 ≤ (p : ℝ) := by
        intro p hp
        have hge : 1000 ≤ p := not_lt.mp (Finset.mem_filter.mp hp).2
        have hdvd : p ∣ n := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        have hp1000 : (1000 : ℝ) ≤ p := Nat.cast_le.mpr hge
        have hle17 : 1 + Real.sqrt (p : ℝ) * |localFactor r n p| ≤ (17 : ℝ) / 16 := by
          unfold localFactor
          simp only [hdvd, ↓reduceIte]
          split_ifs
          · norm_num
          · have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
            rw [abs_of_nonneg (div_nonneg zero_le_one hp1_pos.le)]
            have hsq_le : (p : ℝ) ≤ (((p : ℝ) - 1) / 16) ^ 2 := by
              have : 256 * (p : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith only [hp1000]
              linarith
            have hsp_le : Real.sqrt (p : ℝ) ≤ ((p : ℝ) - 1) / 16 :=
              Real.sqrt_le_iff.2 ⟨by linarith, hsq_le⟩
            have hfrac : Real.sqrt (p : ℝ) * (1 / ((p : ℝ) - 1)) ≤ 1 / 16 := by
              rw [mul_one_div, div_le_iff₀ hp1_pos]
              linarith
            linarith
        calc (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) ^ 16
            ≤ ((17 : ℝ) / 16) ^ 16 := pow_le_pow_left₀ (by positivity) hle17 16
          _ ≤ 1000 := by norm_num
          _ ≤ (p : ℝ) := hp1000
      have hprod16 : (∏ p ∈ S1b, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|)) ^ 16 ≤ (n : ℝ) := by
        rw [← Finset.prod_pow]
        calc ∏ p ∈ S1b, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) ^ 16
            ≤ ∏ p ∈ S1b, (p : ℝ) := real_prod_le_prod S1b _ _ (fun _ _ => by positivity) hterm16
          _ = ((∏ p ∈ S1b, p : ℕ) : ℝ) := by rw [Nat.cast_prod]
          _ ≤ (n : ℝ) := by
              exact_mod_cast Nat.le_of_dvd hn (by
                have hsub : S1b ⊆ n.primeFactors := by
                  intro p hp
                  have h1 := (Finset.mem_filter.mp hp).1
                  have hprime : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
                  have hdvd : p ∣ n := (Finset.mem_filter.mp h1).2
                  exact Nat.mem_primeFactors.mpr ⟨hprime, hdvd, (by omega : n ≠ 0)⟩
                exact (Finset.prod_dvd_prod_of_subset S1b n.primeFactors id hsub).trans
                  (Nat.prod_primeFactors_dvd n))
      have hnn : 0 ≤ ∏ p ∈ S1b, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) :=
        Finset.prod_nonneg fun _ _ => by positivity
      calc ∏ p ∈ S1b, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|)
          = ((∏ p ∈ S1b, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|)) ^ (16 : ℕ)) ^ ((1 : ℝ) / 16) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
            norm_num
        _ ≤ (n : ℝ) ^ ((1 : ℝ) / 16) :=
            Real.rpow_le_rpow (pow_nonneg hnn 16) hprod16 (by norm_num)
    exact mul_le_mul hSmall hBig (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)
  have hmul := mul_le_mul hS1 hS2 (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)
  have hexp_eq : Real.exp 2000 * (n : ℝ) ^ ((1 : ℝ) / 16) * Real.exp 8 =
      Real.exp 2008 * (n : ℝ) ^ ((1 : ℝ) / 16) := by
    calc Real.exp 2000 * (n : ℝ) ^ ((1 : ℝ) / 16) * Real.exp 8
        = (Real.exp 2000 * Real.exp 8) * (n : ℝ) ^ ((1 : ℝ) / 16) := by ring
      _ = Real.exp (2000 + 8) * (n : ℝ) ^ ((1 : ℝ) / 16) := by rw [← Real.exp_add]
      _ = Real.exp 2008 * (n : ℝ) ^ ((1 : ℝ) / 16) := by norm_num
  unfold rankinConst
  linarith only [hmul, hexp_eq]

/-- Exact expansion of the finite Euler product into `Re(singularTrunc r n Q₀)` plus Rankin tail,
yielding `Re(singularTrunc r n Q₀) ≥ 1/4` once `Q₀` is large enough relative to `n^(1/8)`. -/
theorem singularTrunc_re_lower (r n Q₀ : ℕ) (hn_pos : 1 ≤ n) (hn_even : Even n) (hQ₀ : 2 ≤ Q₀)
    (hQ₀_large : rankinConst * (n : ℝ) ^ ((1 : ℝ) / 16) ≤ (1 / 4 : ℝ) * Real.sqrt (Q₀ : ℝ)) :
    (1 : ℝ) / 4 ≤ (singularTrunc r n Q₀).re := by
  set S := (Finset.Icc 1 Q₀).filter Nat.Prime
  have hexp : ∏ p ∈ S, (1 + localFactor r n p) =
      ∑ T ∈ S.powerset, ∏ p ∈ T, localFactor r n p := by
    have h := Finset.prod_add (f := localFactor r n) (g := fun _ => (1 : ℝ)) S
    simpa [add_comm] using h
  set P_le := S.powerset.filter (fun T => ∏ p ∈ T, p ≤ Q₀)
  set P_gt := S.powerset.filter (fun T => ¬ (∏ p ∈ T, p ≤ Q₀))
  have hsplit : ∑ T ∈ S.powerset, ∏ p ∈ T, localFactor r n p =
      (∑ T ∈ P_le, ∏ p ∈ T, localFactor r n p) + (∑ T ∈ P_gt, ∏ p ∈ T, localFactor r n p) :=
    (Finset.sum_filter_add_sum_filter_not S.powerset (fun T => ∏ p ∈ T, p ≤ Q₀) _).symm
  have hmain_eq : ∑ T ∈ P_le, ∏ p ∈ T, localFactor r n p = (singularTrunc r n Q₀).re := by
    have hprod_term : ∀ T ∈ S.powerset,
        ((∏ p ∈ T, localFactor r n p : ℝ) : ℂ) =
          if Nat.Coprime (∏ p ∈ T, p) r then
            (ArithmeticFunction.moebius (∏ p ∈ T, p) : ℂ) ^ 2 *
              ramanujanSum (∏ p ∈ T, p) n / ((∏ p ∈ T, p).totient : ℂ) ^ 2
          else 0 := by
      intro T hT
      have hT_sub : T ⊆ S := Finset.mem_powerset.mp hT
      induction T using Finset.induction with
      | empty =>
        simp [ramanujanSum_one]
      | insert p T' hp_not ih =>
        have hp_mem : p ∈ S := hT_sub (Finset.mem_insert_self p T')
        have hp : p.Prime := (Finset.mem_filter.mp hp_mem).2
        have hT'_sub : T' ⊆ S := fun x hx => hT_sub (Finset.mem_insert_of_mem hx)
        have hih := ih (Finset.mem_powerset.mpr hT'_sub) hT'_sub
        have hq'_pos : 0 < ∏ x ∈ T', x :=
          Finset.prod_pos fun x hx => (Finset.mem_filter.mp (hT'_sub hx)).2.pos
        have hcop_pT' : Nat.Coprime p (∏ x ∈ T', x) := by
          apply Nat.Coprime.prod_right
          intro x hx
          have hx_prime : x.Prime := (Finset.mem_filter.mp (hT'_sub hx)).2
          have hne : p ≠ x := fun h => hp_not (h ▸ hx)
          exact (Nat.coprime_primes hp hx_prime).2 hne
        rw [Finset.prod_insert hp_not, Finset.prod_insert hp_not, Complex.ofReal_mul,
            localFactor_eq_complex hp, hih]
        by_cases h1 : Nat.Coprime p r
        · by_cases h2 : Nat.Coprime (∏ x ∈ T', x) r
          · have h12 : Nat.Coprime (p * ∏ x ∈ T', x) r := h1.mul_left h2
            rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h12]
            rw [ramanujanSum_mul_of_coprime hp.pos hq'_pos hcop_pT' n,
                ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_pT',
                Nat.totient_mul hcop_pT']
            push_cast; ring
          · have h12 : ¬ Nat.Coprime (p * ∏ x ∈ T', x) r := fun h =>
              h2 (h.coprime_dvd_left (dvd_mul_left _ p))
            rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right h12]
            ring
        · have h12 : ¬ Nat.Coprime (p * ∏ x ∈ T', x) r := fun h =>
            h1 (h.coprime_dvd_left (dvd_mul_right p _))
          rw [ite_eq_right h1, ite_eq_right h12]
          ring
    have hC_eq : ((∑ T ∈ P_le, ∏ p ∈ T, localFactor r n p : ℝ) : ℂ) = singularTrunc r n Q₀ := by
      rw [Complex.ofReal_sum]
      unfold singularTrunc
      let P_le_cop := P_le.filter (fun T => Nat.Coprime (∏ p ∈ T, p) r)
      let Q_sf := ((Finset.Icc 1 Q₀).filter (fun q => Nat.Coprime q r)).filter Squarefree
      have hLHS_filt : ∑ T ∈ P_le, ((∏ p ∈ T, localFactor r n p : ℝ) : ℂ) =
          ∑ T ∈ P_le_cop,
            (ArithmeticFunction.moebius (∏ p ∈ T, p) : ℂ) ^ 2 *
              ramanujanSum (∏ p ∈ T, p) n / ((∏ p ∈ T, p).totient : ℂ) ^ 2 := by
        calc ∑ T ∈ P_le, ((∏ p ∈ T, localFactor r n p : ℝ) : ℂ)
            = ∑ T ∈ P_le, (if Nat.Coprime (∏ p ∈ T, p) r then
                (ArithmeticFunction.moebius (∏ p ∈ T, p) : ℂ) ^ 2 *
                  ramanujanSum (∏ p ∈ T, p) n / ((∏ p ∈ T, p).totient : ℂ) ^ 2 else 0) :=
              Finset.sum_congr rfl fun T hT => hprod_term T (Finset.mem_filter.mp hT).1
          _ = ∑ T ∈ P_le_cop, _ := by
              rw [← Finset.sum_filter]
      have hRHS_filt : ∑ q ∈ (Finset.Icc 1 Q₀).filter (fun q => Nat.Coprime q r),
            (ArithmeticFunction.moebius q : ℂ) ^ 2 * ramanujanSum q n / (q.totient : ℂ) ^ 2 =
          ∑ q ∈ Q_sf,
            (ArithmeticFunction.moebius q : ℂ) ^ 2 * ramanujanSum q n / (q.totient : ℂ) ^ 2 := by
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun q _ hq_not => ?_
        have hnsf : ¬ Squarefree q := fun hsf =>
          hq_not (Finset.mem_filter.mpr ⟨‹_›, hsf⟩)
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]
        simp
      rw [hLHS_filt, hRHS_filt]
      refine Finset.sum_bij (fun T _ => ∏ p ∈ T, p) ?_ ?_ ?_ ?_
      · intro T hT
        have hT1 := (Finset.mem_filter.mp hT).1
        have hT_cop := (Finset.mem_filter.mp hT).2
        have hT_sub : T ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hT1).1
        have hT_le : ∏ p ∈ T, p ≤ Q₀ := (Finset.mem_filter.mp hT1).2
        have hT_pos : 1 ≤ ∏ p ∈ T, p := Finset.prod_pos fun p hp => (Finset.mem_filter.mp (hT_sub hp)).2.pos
        have hT_sf : Squarefree (∏ p ∈ T, p) := by
          rw [Nat.squarefree_iff_prime_squarefree]
          intro p hp hpp
          have hpdvd : p ∣ ∏ x ∈ T, x := dvd_trans (dvd_mul_left p p) hpp
          obtain ⟨x, hx, hpx⟩ := Prime.exists_mem_finset_dvd hp.prime hpdvd
          have hx_prime : x.Prime := (Finset.mem_filter.mp (hT_sub hx)).2
          have hpx_eq : p = x := (Nat.prime_dvd_prime_iff_eq hp hx_prime).mp hpx
          subst hpx_eq
          rw [← Finset.mul_prod_erase T _ hx] at hpp
          have hpdvd' : p ∣ ∏ y ∈ T.erase p, y := (mul_dvd_mul_iff_left hp.ne_zero).mp hpp
          obtain ⟨y, hy, hpy⟩ := Prime.exists_mem_finset_dvd hp.prime hpdvd'
          have hy_prime : y.Prime := (Finset.mem_filter.mp (hT_sub (Finset.mem_of_mem_erase hy))).2
          exact (Finset.mem_erase.mp hy).1 ((Nat.prime_dvd_prime_iff_eq hp hy_prime).mp hpy).symm
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hT_pos, hT_le⟩, hT_cop⟩, hT_sf⟩
      · intro T₁ hT₁ T₂ hT₂ hEq
        have h1_sub : T₁ ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hT₁).1).1
        have h2_sub : T₂ ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hT₂).1).1
        ext p
        constructor
        · intro hp1
          have hprime : p.Prime := (Finset.mem_filter.mp (h1_sub hp1)).2
          have hdvd : p ∣ ∏ x ∈ T₂, x := hEq ▸ Finset.dvd_prod_of_mem _ hp1
          obtain ⟨x, hx2, hpx⟩ := Prime.exists_mem_finset_dvd hprime.prime hdvd
          have hx_prime : x.Prime := (Finset.mem_filter.mp (h2_sub hx2)).2
          rwa [(Nat.prime_dvd_prime_iff_eq hprime hx_prime).mp hpx]
        · intro hp2
          have hprime : p.Prime := (Finset.mem_filter.mp (h2_sub hp2)).2
          have hdvd : p ∣ ∏ x ∈ T₁, x := hEq.symm ▸ Finset.dvd_prod_of_mem _ hp2
          obtain ⟨x, hx1, hpx⟩ := Prime.exists_mem_finset_dvd hprime.prime hdvd
          have hx_prime : x.Prime := (Finset.mem_filter.mp (h1_sub hx1)).2
          rwa [(Nat.prime_dvd_prime_iff_eq hprime hx_prime).mp hpx]
      · intro q hq
        have hq1 := (Finset.mem_filter.mp hq).1
        have hq_sf := (Finset.mem_filter.mp hq).2
        have hq_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hq1).1
        have hq_cop := (Finset.mem_filter.mp hq1).2
        have hprod_eq : ∏ p ∈ q.primeFactors, p = q := Nat.prod_primeFactors_of_squarefree hq_sf
        have hsub : q.primeFactors ⊆ S := by
          intro p hp
          have hpm := Nat.mem_primeFactors.mp hp
          have hple : p ≤ Q₀ := (Nat.le_of_dvd (by omega) hpm.2.1).trans hq_Icc.2
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpm.1.pos, hple⟩, hpm.1⟩
        refine ⟨q.primeFactors, ?_, hprod_eq⟩
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨⟨hsub, hprod_eq.le.trans hq_Icc.2⟩, hprod_eq.symm ▸ hq_cop⟩
      · intro _ _; rfl
    have hre := congrArg Complex.re hC_eq
    rw [Complex.ofReal_re] at hre
    exact hre
  have htail_le : |∑ T ∈ P_gt, ∏ p ∈ T, localFactor r n p| ≤ (1 : ℝ) / 4 := by
    have hQ0_pos : (0 : ℝ) < Real.sqrt (Q₀ : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have h1 : |∑ T ∈ P_gt, ∏ p ∈ T, localFactor r n p| ≤
        ∑ T ∈ P_gt, (1 / Real.sqrt (Q₀ : ℝ)) * ∏ p ∈ T, (Real.sqrt (p : ℝ) * |localFactor r n p|) := by
      calc |∑ T ∈ P_gt, ∏ p ∈ T, localFactor r n p|
          ≤ ∑ T ∈ P_gt, |∏ p ∈ T, localFactor r n p| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ T ∈ P_gt, (1 / Real.sqrt (Q₀ : ℝ)) * ∏ p ∈ T, (Real.sqrt (p : ℝ) * |localFactor r n p|) := by
            refine Finset.sum_le_sum fun T hT => ?_
            have hgt : Q₀ < ∏ p ∈ T, p := not_le.mp (Finset.mem_filter.mp hT).2
            have hsqrt_ge : (1 : ℝ) ≤ Real.sqrt ((∏ p ∈ T, p : ℕ) : ℝ) / Real.sqrt (Q₀ : ℝ) := by
              rw [one_le_div hQ0_pos]
              exact Real.sqrt_le_sqrt (Nat.cast_le.mpr hgt.le)
            have hprod_sqrt : Real.sqrt ((∏ p ∈ T, p : ℕ) : ℝ) = ∏ p ∈ T, Real.sqrt (p : ℝ) := by
              rw [Nat.cast_prod, Real.sqrt_prod _ fun _ _ => Nat.cast_nonneg _]
            rw [Finset.abs_prod, Finset.prod_mul_distrib, ← hprod_sqrt, ← mul_assoc, one_div_mul_eq_div]
            exact le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => abs_nonneg _) hsqrt_ge
    have h2 : ∑ T ∈ P_gt, (1 / Real.sqrt (Q₀ : ℝ)) * ∏ p ∈ T, (Real.sqrt (p : ℝ) * |localFactor r n p|) ≤
        (1 / Real.sqrt (Q₀ : ℝ)) * ∏ p ∈ S, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) := by
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hexp2 : ∏ p ∈ S, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) =
          ∑ T ∈ S.powerset, ∏ p ∈ T, (Real.sqrt (p : ℝ) * |localFactor r n p|) := by
        have h := Finset.prod_add
          (f := fun p : ℕ => Real.sqrt (p : ℝ) * |localFactor r n p|)
          (g := fun _ => (1 : ℝ)) S
        simpa [add_comm] using h
      rw [hexp2]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity
    have h3 := rankin_euler_product_bound r n Q₀ hn_pos
    calc |∑ T ∈ P_gt, ∏ p ∈ T, localFactor r n p|
        ≤ (1 / Real.sqrt (Q₀ : ℝ)) * (rankinConst * (n : ℝ) ^ ((1 : ℝ) / 16)) :=
          h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
      _ ≤ (1 / Real.sqrt (Q₀ : ℝ)) * ((1 / 4 : ℝ) * Real.sqrt (Q₀ : ℝ)) :=
          mul_le_mul_of_nonneg_left hQ₀_large (by positivity)
      _ = 1 / 4 := by field_simp [hQ0_pos.ne']
  have heuler : (1 : ℝ) / 2 ≤ ∏ p ∈ S, (1 + localFactor r n p) :=
    finiteEulerProd_ge_half r n Q₀ hn_even hQ₀
  have htail_le_upper : ∑ T ∈ P_gt, ∏ p ∈ T, localFactor r n p ≤ (1 : ℝ) / 4 :=
    (abs_le.mp htail_le).2
  linarith [hexp, hsplit, hmain_eq, heuler, htail_le_upper]

end FiniteEulerProduct

section QuarticConvolution

lemma quarticBump_nonneg (x : ℝ) : 0 ≤ quarticBump x := by
  unfold quarticBump
  split_ifs <;> positivity

lemma quarticBump_le_one (x : ℝ) : quarticBump x ≤ 1 := by
  unfold quarticBump
  split_ifs with h
  · have h1 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
    have h0 : 0 ≤ x * (1 - x) := by nlinarith [h.1, h.2]
    have h2 : (x * (1 - x)) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith
    nlinarith
  · norm_num

lemma quarticBump_ge_on_core {x : ℝ} (hx1 : (1 : ℝ) / 8 ≤ x) (hx2 : x ≤ 3 / 4) :
    (1 : ℝ) / 64 ≤ quarticBump x := by
  unfold quarticBump
  have hc : 0 < x ∧ x < 1 := ⟨by linarith, by linarith⟩
  simp only [hc, and_self, ↓reduceIte]
  have h1 : (1 : ℝ) / 8 ≤ x := hx1
  have h2 : (1 : ℝ) / 4 ≤ 1 - x := by linarith
  have h3 : (1 : ℝ) / 32 ≤ x * (1 - x) := by nlinarith
  nlinarith

/-- **Theorem C2b (Elementary discrete quartic-bump convolution lower bound):**
For any `n ∈ (Y/2, Y]` with `n = r * k + b₁ + b₂`, `b₁, b₂ < r`, and `16 * r ≤ Y`,
`∑_{j₁ + j₂ = k} w((r*j₁ + b₁)/Y) * w((r*j₂ + b₂)/Y) ≥ (1 / 32768) * (Y / r)`. -/
theorem quarticBump_conv_lower {r b₁ b₂ Y k : ℕ} (hr : 0 < r) (hb₁ : b₁ < r) (hb₂ : b₂ < r)
    (hYr : 16 * r ≤ Y) (hn_lo : Y / 2 < r * k + b₁ + b₂) (hn_hi : r * k + b₁ + b₂ ≤ Y) :
    ((1 : ℝ) / 32768) * ((Y : ℝ) / (r : ℝ)) ≤
      ∑ j₁ ∈ Finset.range (k + 1),
        quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
          quarticBump (((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ)) := by
  set n := r * k + b₁ + b₂
  have hY_pos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  let J := (Finset.range (k + 1)).filter fun j₁ =>
    n / 4 + 1 ≤ r * j₁ + b₁ ∧ r * j₁ + b₁ ≤ 3 * n / 4
  have hterm : ∀ j₁ ∈ J,
      (1 : ℝ) / 4096 ≤
        quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
          quarticBump (((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ)) := by
    intro j₁ hj₁
    have hmem := Finset.mem_filter.mp hj₁
    have hj_le : j₁ ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem.1)
    have hlo1 : n / 4 + 1 ≤ r * j₁ + b₁ := hmem.2.1
    have hhi1 : r * j₁ + b₁ ≤ 3 * n / 4 := hmem.2.2
    have hsum_eq : (r * j₁ + b₁) + (r * (k - j₁) + b₂) = n := by
      have : r * j₁ + r * (k - j₁) = r * k := by
        rw [← mul_add, Nat.add_sub_of_le hj_le]
      omega
    have hx1_lo : (1 : ℝ) / 8 ≤ ((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) hY_pos]
      exact_mod_cast (by omega : 1 * Y ≤ (r * j₁ + b₁) * 8)
    have hx1_hi : ((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ) ≤ 3 / 4 := by
      rw [div_le_div_iff₀ hY_pos (by norm_num)]
      exact_mod_cast (by omega : (r * j₁ + b₁) * 4 ≤ 3 * Y)
    have hx2_lo : (1 : ℝ) / 8 ≤ ((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) hY_pos]
      exact_mod_cast (by omega : 1 * Y ≤ (r * (k - j₁) + b₂) * 8)
    have hx2_hi : ((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ) ≤ 3 / 4 := by
      rw [div_le_div_iff₀ hY_pos (by norm_num)]
      exact_mod_cast (by omega : (r * (k - j₁) + b₂) * 4 ≤ 3 * Y)
    have hw1 := quarticBump_ge_on_core hx1_lo hx1_hi
    have hw2 := quarticBump_ge_on_core hx2_lo hx2_hi
    nlinarith
  let j_lo := n / (4 * r) + 1
  let j_hi := (3 * n) / (4 * r) - 1
  have hIcc_sub : Finset.Icc j_lo j_hi ⊆ J := by
    intro j₁ hj₁
    have h1 : j_lo ≤ j₁ := (Finset.mem_Icc.mp hj₁).1
    have h2 : j₁ ≤ j_hi := (Finset.mem_Icc.mp hj₁).2
    have h4rj : 4 * r * j₁ = 4 * (r * j₁) := by ring
    have hj_lo_spec : n / 4 + 1 ≤ r * j₁ + b₁ := by
      have hdiv : n < 4 * r * j_lo := by
        have := Nat.div_add_mod n (4 * r)
        have := Nat.mod_lt n (by omega : 0 < 4 * r)
        have hstep : 4 * r * j_lo = 4 * r * (n / (4 * r)) + 4 * r := by
          dsimp [j_lo]; ring
        omega
      have hmul : 4 * r * j_lo ≤ 4 * r * j₁ := Nat.mul_le_mul_left _ h1
      omega
    have hj_hi_spec : r * j₁ + b₁ ≤ 3 * n / 4 := by
      have hdiv : 4 * r * ((3 * n) / (4 * r)) ≤ 3 * n := Nat.mul_div_le (3 * n) (4 * r)
      have hpos : 1 ≤ (3 * n) / (4 * r) := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        omega
      have hj1_le : j₁ + 1 ≤ (3 * n) / (4 * r) := by omega
      have hmul : 4 * r * (j₁ + 1) ≤ 3 * n := (Nat.mul_le_mul_left (4 * r) hj1_le).trans hdiv
      have h4rj1 : 4 * r * (j₁ + 1) = 4 * (r * j₁) + 4 * r := by ring
      omega
    have hj_le_k : j₁ ≤ k := by
      have hlt : r * j₁ < r * (k + 1) := by
        have hstep : r * (k + 1) = r * k + r := by ring
        omega
      exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left hlt)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hj_le_k), hj_lo_spec, hj_hi_spec⟩
  have hcard_ge : (Y : ℝ) / (8 * (r : ℝ)) ≤ (J.card : ℝ) := by
    have h1 : (Finset.Icc j_lo j_hi).card ≤ J.card := Finset.card_le_card hIcc_sub
    have h2 : j_hi + 1 - j_lo ≤ (Finset.Icc j_lo j_hi).card := by simp
    have hnat : Y ≤ 8 * r * (j_hi + 1 - j_lo) := by
      have hd1 := Nat.div_add_mod (3 * n) (4 * r)
      have hm1 := Nat.mod_lt (3 * n) (by omega : 0 < 4 * r)
      have hd2 := Nat.mul_div_le n (4 * r)
      have hpos_jh : 1 ≤ (3 * n) / (4 * r) := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        omega
      have h_jh1 : j_hi + 1 = (3 * n) / (4 * r) := by dsimp [j_hi]; omega
      have h_jlo : 4 * r * j_lo = 4 * r * (n / (4 * r)) + 4 * r := by dsimp [j_lo]; ring
      have h_step : 4 * r * j_lo ≤ 4 * r * (j_hi + 1) := by
        rw [h_jh1, h_jlo]; omega
      have hj_le : j_lo ≤ j_hi + 1 := Nat.le_of_mul_le_mul_left h_step (by omega)
      have hdiff : 4 * r * (j_hi + 1 - j_lo) = 4 * r * (j_hi + 1) - 4 * r * j_lo :=
        Nat.mul_sub_left_distrib _ _ _
      have h8 : 8 * r * (j_hi + 1 - j_lo) = 2 * (4 * r * (j_hi + 1 - j_lo)) := by ring
      rw [h8, hdiff, h_jh1, h_jlo]
      omega
    have hnat' : Y ≤ 8 * r * J.card := hnat.trans (Nat.mul_le_mul_left _ (h2.trans h1))
    rw [div_le_iff₀ (by positivity)]
    exact_mod_cast (by simpa [mul_comm, mul_assoc] using hnat')
  calc ((1 : ℝ) / 32768) * ((Y : ℝ) / (r : ℝ))
      = ((Y : ℝ) / (8 * (r : ℝ))) * ((1 : ℝ) / 4096) := by ring
    _ ≤ (J.card : ℝ) * ((1 : ℝ) / 4096) := mul_le_mul_of_nonneg_right hcard_ge (by norm_num)
    _ = ∑ _j₁ ∈ J, ((1 : ℝ) / 4096) := by simp
    _ ≤ ∑ j₁ ∈ J,
          quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
            quarticBump (((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ)) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ j₁ ∈ Finset.range (k + 1),
          quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) *
            quarticBump (((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
          mul_nonneg (quarticBump_nonneg _) (quarticBump_nonneg _)

end QuarticConvolution

end FareyGoldbach
