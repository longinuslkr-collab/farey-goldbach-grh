import FareyGoldbach.Defs
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.MeanInequalities

/-!
# Module B1: Global `H₀`-Subgroup Character Expansion & `ℓ¹` Bound

This module proves, for **arbitrary positive integers** `r, q ≥ 1` and `a, b ∈ ℕ` with
`Nat.Coprime a q` and `Nat.Coprime b r` (no primality assumption on `r`, no prime
factorization, no case split between `(q, r) = 1` and `r ∣ q`):

1. `charExpansion_eval`: Fourier inversion on `(ZMod (r * q))ˣ`.
2. `charCoeff_one_eq_zero_of_one_lt_gcd`: if `1 < gcd r q`, the principal coefficient vanishes.
3. `charCoeff_sum_norm_sq`: Parseval identity `∑ χ, ‖charCoeff r q a b χ‖² = 1 / φ(r)`.
4. `charCoeff_l1_le_sharp`: `∑ χ, ‖charCoeff r q a b χ‖ ≤ √(φ(rq) / (gcd r q * φ(r)))`.
5. `charCoeff_l1_le`: `∑ χ, ‖charCoeff r q a b χ‖ ≤ √(q / gcd r q)`.
-/

open scoped BigOperators

namespace FareyGoldbach

section ExpHelpers

lemma e_zero : e 0 = 1 := by
  simp [e]

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma e_nat_mul (n : ℕ) (x : ℝ) : e ((n : ℝ) * x) = (e x) ^ n := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma e_int (k : ℤ) : e (k : ℝ) = 1 := by
  unfold e
  have h : 2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    ring
  rw [Complex.ofReal_intCast, h, Complex.exp_int_mul_two_pi_mul_I]

lemma e_add_int (x : ℝ) (k : ℤ) : e (x + k) = e x := by
  rw [e_add, e_int, mul_one]

lemma e_eq_of_sub_int {x y : ℝ} {k : ℤ} (h : x - y = k) : e x = e y := by
  have hx : x = y + k := by linarith
  rw [hx, e_add_int]

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  have h : 2 * (Real.pi : ℂ) * (x : ℂ) * Complex.I = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma e_mul_star_e (x : ℝ) : e x * star (e x) = 1 := by
  rw [Complex.star_def, Complex.mul_conj', norm_e]
  norm_num

lemma e_eq_one_iff (x : ℝ) : e x = 1 ↔ ∃ k : ℤ, x = k := by
  unfold e
  have h : 2 * (Real.pi : ℂ) * (x : ℂ) * Complex.I = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hpi : (2 * Real.pi : ℂ) * Complex.I ≠ 0 := by
      have h1 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero two_ne_zero h1) Complex.I_ne_zero
    have hEq : (x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) =
        (k : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) := by
      calc (x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)
          = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
        _ = (k : ℂ) * (2 * Real.pi * Complex.I) := hk
        _ = (k : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) := by ring
    have hcx : (x : ℂ) = (k : ℂ) := mul_right_cancel₀ hpi hEq
    exact_mod_cast hcx
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast; ring

end ExpHelpers

section GlobalSubgroup

/-- The support of `f(u) = 1_{u ≡ b mod r} e(au/(rq))` inside `ZMod (r * q)`. -/
noncomputable def charSupp (r q b : ℕ) [NeZero (r * q)] : Finset (ZMod (r * q)) := by
  classical
  exact Finset.univ.filter fun u => IsUnit u ∧ u.val % r = b % r

/-- For any unit `u` in `ZMod n`, `star (χ u) = χ u⁻¹`. -/
lemma star_char_apply_eq_inv {n : ℕ} (χ : DirichletCharacter ℂ n) {u : ZMod n} (hu : IsUnit u) :
    star (χ u) = χ u⁻¹ := by
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_of_isUnit hu]
  congr 1
  apply hu.mul_left_cancel
  calc u * (↑hu.unit⁻¹ : ZMod n) = (↑hu.unit : ZMod n) * (↑hu.unit⁻¹ : ZMod n) := rfl
    _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    _ = u * u⁻¹ := by rw [mul_comm]; exact ((ZMod.inv_mul_eq_one_of_isUnit hu u).2 rfl).symm

/-- Exact cardinality of `charSupp`: `φ(r) * |charSupp r q b| = φ(r * q)`. -/
lemma totient_mul_card_charSupp (r q b : ℕ) (hr : 0 < r)
    (hb : Nat.Coprime b r) [NeZero (r * q)] :
    r.totient * (charSupp r q b).card = (r * q).totient := by
  classical
  have : NeZero r := ⟨hr.ne'⟩
  let f : (ZMod (r * q))ˣ →* (ZMod r)ˣ := ZMod.unitsMap (dvd_mul_right r q)
  have hf_surj : Function.Surjective f := ZMod.unitsMap_surjective (dvd_mul_right r q)
  have hb_unit : IsUnit (b : ZMod r) := (ZMod.isUnit_iff_coprime b r).2 hb
  let b₀ : (ZMod r)ˣ := hb_unit.unit
  let fiber : Finset (ZMod (r * q))ˣ := Finset.univ.filter fun u => f u = b₀
  have hcard_eq : (charSupp r q b).card = fiber.card := by
    refine Finset.card_bij (fun u hu => (Finset.mem_filter.mp hu).2.1.unit) ?_ ?_ ?_
    · intro u hu
      have hu' := (Finset.mem_filter.mp hu).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      ext
      change ZMod.castHom (dvd_mul_right r q) (ZMod r) u = (b : ZMod r)
      have hcast : ZMod.castHom (dvd_mul_right r q) (ZMod r) u = (u.val : ZMod r) := by
        simp
      rw [hcast, ZMod.natCast_eq_natCast_iff]
      exact hu'.2
    · intro u₁ _ u₂ _ hEq
      have hval := congrArg Units.val hEq
      simpa using hval
    · intro u hu
      have hfEq : f u = b₀ := (Finset.mem_filter.mp hu).2
      refine ⟨(u : ZMod (r * q)), ?_, by ext; rfl⟩
      rw [charSupp, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, u.isUnit, ?_⟩
      have hvalEq : ZMod.castHom (dvd_mul_right r q) (ZMod r) (u : ZMod (r * q)) = (b : ZMod r) :=
        congrArg Units.val hfEq
      have hcast : ZMod.castHom (dvd_mul_right r q) (ZMod r) (u : ZMod (r * q)) =
          ((u : ZMod (r * q)).val : ZMod r) := by
        simp
      rw [hcast, ZMod.natCast_eq_natCast_iff] at hvalEq
      exact hvalEq
  have hfiber_const : ∀ y : (ZMod r)ˣ,
      (Finset.univ.filter fun u : (ZMod (r * q))ˣ => f u = y).card = fiber.card := by
    intro y
    obtain ⟨u₀, hu₀⟩ := hf_surj b₀
    obtain ⟨u₁, hu₁⟩ := hf_surj y
    refine Finset.card_bij (fun u _ => u * u₁⁻¹ * u₀) ?_ ?_ ?_
    · intro u hu
      rw [Finset.mem_filter] at hu ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      simp [map_mul, map_inv, hu.2, hu₀, hu₁]
    · intro u₁' _ u₂' _ hEq
      have h1 : u₁' * u₁⁻¹ = u₂' * u₁⁻¹ := mul_right_cancel hEq
      exact mul_right_cancel h1
    · intro v hv
      rw [Finset.mem_filter] at hv
      refine ⟨v * u₀⁻¹ * u₁, ?_, by group⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp [map_mul, map_inv, hv.2, hu₀, hu₁]
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := fun u : (ZMod (r * q))ˣ => f u)
    (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have hsum' : Fintype.card (ZMod (r * q))ˣ = Fintype.card (ZMod r)ˣ * fiber.card := by
    calc Fintype.card (ZMod (r * q))ˣ
        = (Finset.univ : Finset (ZMod (r * q))ˣ).card := rfl
      _ = ∑ y ∈ (Finset.univ : Finset (ZMod r)ˣ),
            (Finset.univ.filter fun u : (ZMod (r * q))ˣ => f u = y).card := hsum
      _ = ∑ _y ∈ (Finset.univ : Finset (ZMod r)ˣ), fiber.card := by
            refine Finset.sum_congr rfl fun y _ => hfiber_const y
      _ = Fintype.card (ZMod r)ˣ * fiber.card := by simp
  rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient] at hsum'
  rw [hcard_eq, ← hsum']

lemma card_charSupp_eq (r q b : ℕ) (hr : 0 < r)
    (hb : Nat.Coprime b r) [NeZero (r * q)] :
    ((charSupp r q b).card : ℝ) = ((r * q).totient : ℝ) / (r.totient : ℝ) := by
  have h := totient_mul_card_charSupp r q b hr hb
  have hφ : (r.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hr).ne'
  rw [eq_div_iff hφ]
  exact_mod_cast (by simpa [mul_comm] using h)

/-- Helper: `(r * q) ∣ (Nat.lcm r q) ^ 2`. -/
lemma mul_dvd_lcm_sq (r q : ℕ) : r * q ∣ (Nat.lcm r q) ^ 2 := by
  have h1 : r ∣ Nat.lcm r q := Nat.dvd_lcm_left r q
  have h2 : q ∣ Nat.lcm r q := Nat.dvd_lcm_right r q
  rw [sq]
  exact mul_dvd_mul h1 h2

/-- The generator `h₁ = 1 + lcm(r, q)` of the order-`gcd(r, q)` subgroup `H₀ ⊂ (ZMod (r*q))ˣ`. -/
def hGen (r q : ℕ) : ZMod (r * q) :=
  1 + ((Nat.lcm r q : ℕ) : ZMod (r * q))

lemma hGen_pow (r q m : ℕ) :
    (hGen r q) ^ m = 1 + ((m * Nat.lcm r q : ℕ) : ZMod (r * q)) := by
  induction m with
  | zero => simp [hGen]
  | succ m ih =>
    rw [pow_succ, ih, hGen]
    have hsq : (((Nat.lcm r q : ℕ) : ZMod (r * q)) * ((Nat.lcm r q : ℕ) : ZMod (r * q))) = 0 := by
      have hd : r * q ∣ Nat.lcm r q * Nat.lcm r q := by
        simpa [sq] using mul_dvd_lcm_sq r q
      have hcast : ((Nat.lcm r q * Nat.lcm r q : ℕ) : ZMod (r * q)) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 hd
      simpa [Nat.cast_mul] using hcast
    calc (1 + ((m * Nat.lcm r q : ℕ) : ZMod (r * q))) * (1 + ((Nat.lcm r q : ℕ) : ZMod (r * q)))
        = 1 + ((m : ZMod (r * q)) + 1) * ((Nat.lcm r q : ℕ) : ZMod (r * q)) +
            (m : ZMod (r * q)) * (((Nat.lcm r q : ℕ) : ZMod (r * q)) * ((Nat.lcm r q : ℕ) : ZMod (r * q))) := by
          push_cast; ring
      _ = 1 + (((m + 1) * Nat.lcm r q : ℕ) : ZMod (r * q)) := by
          rw [hsq, mul_zero, add_zero]
          push_cast; ring

lemma hGen_pow_gcd (r q : ℕ) : (hGen r q) ^ (Nat.gcd r q) = 1 := by
  rw [hGen_pow, Nat.gcd_mul_lcm]
  simp

lemma isUnit_hGen (r q : ℕ) (hr : 0 < r) : IsUnit (hGen r q) := by
  have hg : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_left q hr
  have hpow : (hGen r q) ^ (Nat.gcd r q) = 1 := hGen_pow_gcd r q
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hg.ne'
  rw [hk, pow_succ'] at hpow
  exact isUnit_iff_exists_inv.2 ⟨(hGen r q) ^ k, hpow⟩

lemma hGen_pow_ne_one (r q m : ℕ) (hr : 0 < r) (hq : 0 < q) (hm0 : 0 < m)
    (hmg : m < Nat.gcd r q) : (hGen r q) ^ m ≠ 1 := by
  rw [hGen_pow]
  intro hEq
  have hzero : ((m * Nat.lcm r q : ℕ) : ZMod (r * q)) = 0 := by
    have := congrArg (fun z : ZMod (r * q) => z - 1) hEq
    simpa using this
  have hdvd : r * q ∣ m * Nat.lcm r q := (ZMod.natCast_eq_zero_iff _ _).1 hzero
  have hlcm_pos : 0 < Nat.lcm r q := Nat.lcm_pos hr hq
  have hlt : m * Nat.lcm r q < r * q := by
    calc m * Nat.lcm r q < Nat.gcd r q * Nat.lcm r q := Nat.mul_lt_mul_of_pos_right hmg hlcm_pos
      _ = r * q := Nat.gcd_mul_lcm r q
  have hpos : 0 < m * Nat.lcm r q := Nat.mul_pos hm0 hlcm_pos
  exact absurd (Nat.le_of_dvd hpos hdvd) (not_le_of_gt hlt)

/-- Action of `hGen r q` on `u ∈ charSupp r q b`: `u * hGen = u + b * lcm(r, q)` in `ZMod (r * q)`. -/
lemma mul_hGen_eq_add (r q b : ℕ) [NeZero (r * q)] {u : ZMod (r * q)}
    (hu : u.val % r = b % r) :
    u * hGen r q = u + ((b * Nat.lcm r q : ℕ) : ZMod (r * q)) := by
  unfold hGen
  rw [mul_add, mul_one]
  congr 1
  have hcong : u.val * Nat.lcm r q ≡ b * Nat.lcm r q [MOD r * q] := by
    have hq_dvd : q ∣ Nat.lcm r q := Nat.dvd_lcm_right r q
    obtain ⟨t, ht⟩ := hq_dvd
    rw [ht]
    have hmul : u.val * q ≡ b * q [MOD r * q] := by
      rw [Nat.ModEq, Nat.mul_mod_mul_right, Nat.mul_mod_mul_right, hu]
    have hmul2 : u.val * q * t ≡ b * q * t [MOD r * q] := Nat.ModEq.mul_right t hmul
    simpa [mul_assoc] using hmul2
  have hcast : ((u.val * Nat.lcm r q : ℕ) : ZMod (r * q)) =
      ((b * Nat.lcm r q : ℕ) : ZMod (r * q)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hcong
  simpa [Nat.cast_mul, ZMod.natCast_zmod_val] using hcast

/-- Exponential transformation under `u ↦ u * hGen r q` on `charSupp r q b`. -/
lemma e_mul_hGen (r q a b : ℕ) (hr : 0 < r) (hq : 0 < q) [NeZero (r * q)]
    {u : ZMod (r * q)} (hu : u.val % r = b % r) :
    e ((a : ℝ) * ((u * hGen r q).val : ℝ) / ((r * q : ℕ) : ℝ)) =
      e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) *
        e (((a * b : ℕ) : ℝ) / ((Nat.gcd r q : ℕ) : ℝ)) := by
  have hEq : u * hGen r q = u + ((b * Nat.lcm r q : ℕ) : ZMod (r * q)) :=
    mul_hGen_eq_add r q b hu
  have hmod : (u * hGen r q).val ≡ u.val + b * Nat.lcm r q [MOD r * q] := by
    have hc : (((u * hGen r q).val : ℕ) : ZMod (r * q)) =
        (((u.val + b * Nat.lcm r q : ℕ) : ZMod (r * q))) := by
      simp [hEq, Nat.cast_add]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hc
  have hdvd : ((r * q : ℕ) : ℤ) ∣ (((u * hGen r q).val : ℤ) - ((u.val + b * Nat.lcm r q : ℕ) : ℤ)) :=
    Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.2 hmod).symm
  obtain ⟨k, hk⟩ := hdvd
  have hrq_pos : ((r * q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.mul_pos hr hq).ne'
  have hg_pos : ((Nat.gcd r q : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.gcd_pos_of_pos_left q hr).ne'
  have hgl : ((Nat.gcd r q : ℕ) : ℝ) * ((Nat.lcm r q : ℕ) : ℝ) = ((r * q : ℕ) : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm r q
  rw [← e_add]
  refine e_eq_of_sub_int (k := (a : ℤ) * k) ?_
  have hkR : ((u * hGen r q).val : ℝ) - ((u.val : ℝ) + (b : ℝ) * (Nat.lcm r q : ℝ)) =
      ((r * q : ℕ) : ℝ) * (k : ℝ) := by
    have hk' := congrArg (fun z : ℤ => (z : ℝ)) hk
    push_cast at hk' ⊢
    linarith
  field_simp [hrq_pos, hg_pos]
  push_cast at hkR hgl ⊢
  linear_combination (a : ℝ) * (Nat.gcd r q : ℝ) * hkR + (a : ℝ) * (b : ℝ) * hgl

/-- `charCoeff` transforms by `e(ab/g) * star (χ (hGen r q))` under reindexing `u ↦ u * hGen`. -/
lemma charCoeff_invariant (r q a b : ℕ) (hr : 0 < r) (hq : 0 < q) [NeZero (r * q)]
    (χ : DirichletCharacter ℂ (r * q)) :
    charCoeff r q a b χ =
      e (((a * b : ℕ) : ℝ) / ((Nat.gcd r q : ℕ) : ℝ)) * star (χ (hGen r q)) *
        charCoeff r q a b χ := by
  classical
  have hh_unit : IsUnit (hGen r q) := isUnit_hGen r q hr
  have hsum :
      ∑ u ∈ charSupp r q b,
          e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) * star (χ u) =
      ∑ u ∈ charSupp r q b,
          e ((a : ℝ) * ((u * hGen r q).val : ℝ) / ((r * q : ℕ) : ℝ)) *
            star (χ (u * hGen r q)) := by
    symm
    refine Finset.sum_bij (fun u _ => u * hGen r q) ?_ ?_ ?_ ?_
    · intro u hu
      have hu' := (Finset.mem_filter.mp hu).2
      rw [charSupp, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hu'.1.mul hh_unit, ?_⟩
      have hadd := mul_hGen_eq_add r q b hu'.2
      have hmod : (u * hGen r q).val ≡ u.val + b * Nat.lcm r q [MOD r * q] := by
        have hc : (((u * hGen r q).val : ℕ) : ZMod (r * q)) =
            ((u.val + b * Nat.lcm r q : ℕ) : ZMod (r * q)) := by
          simp [hadd, Nat.cast_add]
        exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hc
      have hmod_r : (u * hGen r q).val ≡ u.val + b * Nat.lcm r q [MOD r] :=
        hmod.of_dvd (dvd_mul_right r q)
      have hlcm_r : r ∣ Nat.lcm r q := Nat.dvd_lcm_left r q
      have h0 : (u.val + b * Nat.lcm r q) % r = u.val % r := by
        obtain ⟨t, ht⟩ := hlcm_r
        rw [ht, ← mul_assoc, mul_comm b r, mul_assoc, Nat.add_mul_mod_self_left]
      exact hmod_r.trans (by rw [Nat.ModEq, h0, hu'.2])
    · intro u₁ _ u₂ _ hEq
      exact hh_unit.mul_right_cancel hEq
    · intro v hv
      have hv' := (Finset.mem_filter.mp hv).2
      let hinv : ZMod (r * q) := ↑(hh_unit.unit⁻¹)
      have hhinv : hinv * hGen r q = 1 := by
        change (↑(hh_unit.unit⁻¹) : ZMod (r * q)) * (↑hh_unit.unit : ZMod (r * q)) = 1
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      refine ⟨v * hinv, ?_, by rw [mul_assoc, hhinv, mul_one]⟩
      rw [charSupp, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hv'.1.mul hh_unit.unit⁻¹.isUnit, ?_⟩
      have hg : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_left q hr
      have hinv_eq : hinv = (hGen r q) ^ (Nat.gcd r q - 1) := by
        have h1 : (hGen r q) ^ (Nat.gcd r q - 1) * hGen r q = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel hg, hGen_pow_gcd]
        exact hh_unit.mul_right_cancel (hhinv.trans h1.symm)
      rw [hinv_eq, hGen_pow]
      have hmod : (v * (1 + (((Nat.gcd r q - 1) * Nat.lcm r q : ℕ) : ZMod (r * q)))).val ≡
          v.val + v.val * ((Nat.gcd r q - 1) * Nat.lcm r q) [MOD r * q] := by
        have hc : (((v * (1 + (((Nat.gcd r q - 1) * Nat.lcm r q : ℕ) : ZMod (r * q)))).val : ℕ) : ZMod (r * q)) =
            ((v.val + v.val * ((Nat.gcd r q - 1) * Nat.lcm r q) : ℕ) : ZMod (r * q)) := by
          simp only [ZMod.natCast_zmod_val, Nat.cast_add, Nat.cast_mul]
          ring
        exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hc
      have hmod_r : (v * (1 + (((Nat.gcd r q - 1) * Nat.lcm r q : ℕ) : ZMod (r * q)))).val ≡
          v.val + v.val * ((Nat.gcd r q - 1) * Nat.lcm r q) [MOD r] :=
        hmod.of_dvd (dvd_mul_right r q)
      have hlcm_r : r ∣ Nat.lcm r q := Nat.dvd_lcm_left r q
      have hdiv : r ∣ v.val * ((Nat.gcd r q - 1) * Nat.lcm r q) :=
        dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hlcm_r _) _
      obtain ⟨t, ht⟩ := hdiv
      have h0 : (v.val + v.val * ((Nat.gcd r q - 1) * Nat.lcm r q)) % r = v.val % r := by
        rw [ht, Nat.add_mul_mod_self_left]
      exact hmod_r.trans (by rw [Nat.ModEq, h0, hv'.2])
    · intro u _
      rfl
  have hterm :
      ∑ u ∈ charSupp r q b,
          e ((a : ℝ) * ((u * hGen r q).val : ℝ) / ((r * q : ℕ) : ℝ)) * star (χ (u * hGen r q)) =
      e (((a * b : ℕ) : ℝ) / ((Nat.gcd r q : ℕ) : ℝ)) * star (χ (hGen r q)) *
        ∑ u ∈ charSupp r q b, e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) * star (χ u) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu' := (Finset.mem_filter.mp hu).2
    rw [e_mul_hGen r q a b hr hq hu'.2, map_mul, star_mul']
    ring
  change ((1 : ℂ) / ((r * q).totient : ℂ)) *
      ∑ u ∈ charSupp r q b, e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) * star (χ u) =
    e (((a * b : ℕ) : ℝ) / ((Nat.gcd r q : ℕ) : ℝ)) * star (χ (hGen r q)) *
      (((1 : ℂ) / ((r * q).totient : ℂ)) *
        ∑ u ∈ charSupp r q b, e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) * star (χ u))
  conv_lhs => rw [hsum, hterm]
  ring

/-- Key support restriction: `charCoeff r q a b χ ≠ 0 → χ (hGen r q) = e(ab / gcd(r, q))`. -/
lemma char_hGen_eq_of_charCoeff_ne_zero (r q a b : ℕ) (hr : 0 < r) (hq : 0 < q) [NeZero (r * q)]
    (χ : DirichletCharacter ℂ (r * q)) (hnez : charCoeff r q a b χ ≠ 0) :
    χ (hGen r q) = e (((a * b : ℕ) : ℝ) / ((Nat.gcd r q : ℕ) : ℝ)) := by
  have hinv := charCoeff_invariant r q a b hr hq χ
  have h1 : e (((a * b : ℕ) : ℝ) / ((Nat.gcd r q : ℕ) : ℝ)) * star (χ (hGen r q)) = 1 := by
    have hmul : (e (((a * b : ℕ) : ℝ) / ((Nat.gcd r q : ℕ) : ℝ)) * star (χ (hGen r q))) *
        charCoeff r q a b χ = 1 * charCoeff r q a b χ := by
      rw [one_mul]; exact hinv.symm
    exact mul_right_cancel₀ hnez hmul
  have hh_unit : IsUnit (hGen r q) := isUnit_hGen r q hr
  have hmul_star : χ (hGen r q) * star (χ (hGen r q)) = 1 := by
    rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel,
        MulChar.one_apply hh_unit]
  have h2 : e (((a * b : ℕ) : ℝ) / ((Nat.gcd r q : ℕ) : ℝ)) * star (χ (hGen r q)) =
      χ (hGen r q) * star (χ (hGen r q)) := h1.trans hmul_star.symm
  have hstar_ne : star (χ (hGen r q)) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h1
    exact zero_ne_one h1
  exact (mul_right_cancel₀ hstar_ne h2).symm

/-- **Theorem B1.1 (Principal character vanishing):** whenever `1 < gcd(r, q)`, `charCoeff ... 1 = 0`. -/
theorem charCoeff_one_eq_zero_of_one_lt_gcd (r q a b : ℕ) (hr : 0 < r) (hq : 0 < q)
    (ha : Nat.Coprime a q) (hb : Nat.Coprime b r) (hg : 1 < Nat.gcd r q) [NeZero (r * q)] :
    charCoeff r q a b (1 : DirichletCharacter ℂ (r * q)) = 0 := by
  by_contra hnez
  have hEq := char_hGen_eq_of_charCoeff_ne_zero r q a b hr hq 1 hnez
  have hh_unit : IsUnit (hGen r q) := isUnit_hGen r q hr
  rw [MulChar.one_apply hh_unit] at hEq
  have h1 := (e_eq_one_iff _).1 hEq.symm
  obtain ⟨k, hk⟩ := h1
  have hg_pos : ((Nat.gcd r q : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.gcd_pos_of_pos_left q hr).ne'
  have hdiv : ((Nat.gcd r q : ℕ) : ℤ) ∣ ((a * b : ℕ) : ℤ) := by
    refine ⟨k, ?_⟩
    have hR : ((a * b : ℕ) : ℝ) = (k : ℝ) * ((Nat.gcd r q : ℕ) : ℝ) := (div_eq_iff hg_pos).1 hk
    have hZ : ((a * b : ℕ) : ℤ) = k * ((Nat.gcd r q : ℕ) : ℤ) := by exact_mod_cast hR
    linarith
  have hdvd_nat : Nat.gcd r q ∣ a * b := Int.ofNat_dvd.1 hdiv
  have hcop_a : Nat.Coprime a (Nat.gcd r q) := ha.coprime_dvd_right (Nat.gcd_dvd_right r q)
  have hcop_b : Nat.Coprime b (Nat.gcd r q) := hb.coprime_dvd_right (Nat.gcd_dvd_left r q)
  have hcop : Nat.Coprime (a * b) (Nat.gcd r q) := hcop_a.mul_left hcop_b
  have hle : Nat.gcd r q ∣ 1 := by
    have := Nat.dvd_gcd hdvd_nat (dvd_refl (Nat.gcd r q))
    rwa [hcop.gcd_eq_one] at this
  exact absurd (Nat.le_of_dvd one_pos hle) (not_le_of_gt hg)

/-- The fiber of characters `χ mod (r * q)` matching the `H₀`-character `e(ab / gcd(r, q))`. -/
noncomputable def charFiber (r q a b : ℕ) [NeZero (r * q)] :
    Finset (DirichletCharacter ℂ (r * q)) := by
  classical
  exact Finset.univ.filter fun χ =>
    χ (hGen r q) = e (((a * b : ℕ) : ℝ) / ((Nat.gcd r q : ℕ) : ℝ))

/-- Exact count of characters in `charFiber`: `gcd(r, q) * |charFiber| = φ(r * q)`. -/
lemma card_charFiber (r q a b : ℕ) (hr : 0 < r) (hq : 0 < q) [NeZero (r * q)] :
    Nat.gcd r q * (charFiber r q a b).card = (r * q).totient := by
  classical
  set ψ₁ : ℂ := e (((a * b : ℕ) : ℝ) / ((Nat.gcd r q : ℕ) : ℝ))
  have hg_pos : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_left q hr
  have hψ_pow : ψ₁ ^ (Nat.gcd r q) = 1 := by
    change (e (((a * b : ℕ) : ℝ) / ((Nat.gcd r q : ℕ) : ℝ))) ^ (Nat.gcd r q) = 1
    rw [← e_nat_mul]
    have hg0 : ((Nat.gcd r q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hg_pos.ne'
    have hmul : ((Nat.gcd r q : ℕ) : ℝ) * (((a * b : ℕ) : ℝ) / ((Nat.gcd r q : ℕ) : ℝ)) =
        ((a * b : ℕ) : ℝ) := mul_div_cancel₀ _ hg0
    rw [hmul]
    exact_mod_cast e_int (a * b : ℤ)
  have hψ_ne : ψ₁ ≠ 0 := by
    intro hz
    rw [hz, zero_pow hg_pos.ne'] at hψ_pow
    exact zero_ne_one hψ_pow
  have hgeom : ∀ χ : DirichletCharacter ℂ (r * q),
      ∑ m ∈ Finset.range (Nat.gcd r q), (χ (hGen r q) * ψ₁⁻¹) ^ m =
        if χ (hGen r q) = ψ₁ then (Nat.gcd r q : ℂ) else 0 := by
    intro χ
    split_ifs with hEq
    · have h1 : χ (hGen r q) * ψ₁⁻¹ = 1 := by rw [hEq, mul_inv_cancel₀ hψ_ne]
      simp [h1]
    · set z : ℂ := χ (hGen r q) * ψ₁⁻¹
      have hz_ne : z ≠ 1 := by
        intro h1
        apply hEq
        have := congrArg (fun w : ℂ => w * ψ₁) h1
        simp only [z, mul_assoc, inv_mul_cancel₀ hψ_ne, mul_one, one_mul] at this
        exact this
      have hz_pow : z ^ (Nat.gcd r q) = 1 := by
        calc z ^ (Nat.gcd r q)
            = χ (hGen r q) ^ (Nat.gcd r q) * (ψ₁ ^ (Nat.gcd r q))⁻¹ := by
              rw [mul_pow, inv_pow]
          _ = χ ((hGen r q) ^ (Nat.gcd r q)) * 1 := by rw [← map_pow, hψ_pow, inv_one]
          _ = 1 := by rw [hGen_pow_gcd, map_one, mul_one]
      have hmul : (z - 1) * ∑ m ∈ Finset.range (Nat.gcd r q), z ^ m = 0 := by
        rw [mul_comm, geom_sum_mul, hz_pow, sub_self]
      exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hz_ne)
  have hLHS : ∑ χ : DirichletCharacter ℂ (r * q),
      ∑ m ∈ Finset.range (Nat.gcd r q), (χ (hGen r q) * ψ₁⁻¹) ^ m =
        (Nat.gcd r q : ℂ) * ((charFiber r q a b).card : ℂ) := by
    calc ∑ χ : DirichletCharacter ℂ (r * q),
            ∑ m ∈ Finset.range (Nat.gcd r q), (χ (hGen r q) * ψ₁⁻¹) ^ m
        = ∑ χ : DirichletCharacter ℂ (r * q),
            (if χ (hGen r q) = ψ₁ then (Nat.gcd r q : ℂ) else 0) :=
          Finset.sum_congr rfl fun χ _ => hgeom χ
      _ = ∑ _χ ∈ charFiber r q a b, (Nat.gcd r q : ℂ) := by
          rw [charFiber, Finset.sum_filter]
      _ = (Nat.gcd r q : ℂ) * ((charFiber r q a b).card : ℂ) := by
          simp [mul_comm]
  have hRHS : ∑ χ : DirichletCharacter ℂ (r * q),
      ∑ m ∈ Finset.range (Nat.gcd r q), (χ (hGen r q) * ψ₁⁻¹) ^ m =
        ((r * q).totient : ℂ) := by
    rw [Finset.sum_comm]
    have hterm : ∀ m ∈ Finset.range (Nat.gcd r q),
        ∑ χ : DirichletCharacter ℂ (r * q), (χ (hGen r q) * ψ₁⁻¹) ^ m =
          if m = 0 then ((r * q).totient : ℂ) else 0 := by
      intro m hm
      have hm_lt : m < Nat.gcd r q := Finset.mem_range.mp hm
      have hpull : ∑ χ : DirichletCharacter ℂ (r * q), (χ (hGen r q) * ψ₁⁻¹) ^ m =
          (ψ₁⁻¹) ^ m * ∑ χ : DirichletCharacter ℂ (r * q), χ ((hGen r q) ^ m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [mul_pow, ← map_pow, mul_comm]
      rw [hpull, DirichletCharacter.sum_characters_eq]
      by_cases hm0 : m = 0
      · subst hm0; simp
      · have hne : (hGen r q) ^ m ≠ 1 :=
          hGen_pow_ne_one r q m hr hq (Nat.pos_of_ne_zero hm0) hm_lt
        simp [hm0, hne]
    calc ∑ m ∈ Finset.range (Nat.gcd r q),
            ∑ χ : DirichletCharacter ℂ (r * q), (χ (hGen r q) * ψ₁⁻¹) ^ m
        = ∑ m ∈ Finset.range (Nat.gcd r q),
            (if m = 0 then ((r * q).totient : ℂ) else 0) :=
          Finset.sum_congr rfl hterm
      _ = ((r * q).totient : ℂ) := by
          simp [hg_pos]
  have hC : ((Nat.gcd r q * (charFiber r q a b).card : ℕ) : ℂ) = ((r * q).totient : ℂ) := by
    push_cast
    exact hLHS.symm.trans hRHS
  exact_mod_cast hC

/-- **Theorem B1.2 (Fourier inversion on units):** `∑ χ, charCoeff r q a b χ * χ u = f(u)`. -/
theorem charExpansion_eval (r q a b : ℕ) (hr : 0 < r) (hq : 0 < q) [NeZero (r * q)]
    {u : ZMod (r * q)} (hu : IsUnit u) :
    ∑ χ : DirichletCharacter ℂ (r * q), charCoeff r q a b χ * χ u =
      if u.val % r = b % r then e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) else 0 := by
  classical
  have hφ : ((r * q).totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.mul_pos hr hq)).ne'
  calc ∑ χ : DirichletCharacter ℂ (r * q), charCoeff r q a b χ * χ u
      = ∑ χ : DirichletCharacter ℂ (r * q),
          ((1 : ℂ) / ((r * q).totient : ℂ)) *
            ∑ v ∈ charSupp r q b,
              e ((a : ℝ) * (v.val : ℝ) / ((r * q : ℕ) : ℝ)) * (star (χ v) * χ u) := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        unfold charCoeff
        change (((1 : ℂ) / ((r * q).totient : ℂ)) *
            ∑ v ∈ charSupp r q b,
              e ((a : ℝ) * (v.val : ℝ) / ((r * q : ℕ) : ℝ)) * star (χ v)) * χ u = _
        rw [mul_assoc, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun v _ => by ring
    _ = ((1 : ℂ) / ((r * q).totient : ℂ)) *
          ∑ v ∈ charSupp r q b,
            e ((a : ℝ) * (v.val : ℝ) / ((r * q : ℕ) : ℝ)) *
              ∑ χ : DirichletCharacter ℂ (r * q), χ v⁻¹ * χ u := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun v hv => ?_
        have hv_unit : IsUnit v := (Finset.mem_filter.mp hv).2.1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [star_char_apply_eq_inv χ hv_unit]
    _ = ((1 : ℂ) / ((r * q).totient : ℂ)) *
          ∑ v ∈ charSupp r q b,
            e ((a : ℝ) * (v.val : ℝ) / ((r * q : ℕ) : ℝ)) *
              (if v = u then ((r * q).totient : ℂ) else 0) := by
        congr 1
        refine Finset.sum_congr rfl fun v hv => ?_
        have hv_unit : IsUnit v := (Finset.mem_filter.mp hv).2.1
        rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hv_unit u]
    _ = if u ∈ charSupp r q b then e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) else 0 := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq']
        split_ifs
        · field_simp [hφ]
        · simp
    _ = if u.val % r = b % r then e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) else 0 := by
        simp [charSupp, hu]

/-- **Theorem B1.3 (Parseval identity):** `∑ χ, ‖charCoeff r q a b χ‖² = 1 / φ(r)`. -/
theorem charCoeff_sum_norm_sq (r q a b : ℕ) (hr : 0 < r) (hq : 0 < q)
    (hb : Nat.Coprime b r) [NeZero (r * q)] :
    ∑ χ : DirichletCharacter ℂ (r * q), ‖charCoeff r q a b χ‖ ^ 2 = 1 / (r.totient : ℝ) := by
  classical
  have hφ_pos : 0 < (r * q).totient := Nat.totient_pos.mpr (Nat.mul_pos hr hq)
  have hφC : ((r * q).totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hφ_pos.ne'
  have hC :
      ∑ χ : DirichletCharacter ℂ (r * q),
          charCoeff r q a b χ * star (charCoeff r q a b χ) =
        ((charSupp r q b).card : ℂ) / ((r * q).totient : ℂ) := by
    have hcoeff_star : ∀ χ : DirichletCharacter ℂ (r * q),
        charCoeff r q a b χ * star (charCoeff r q a b χ) =
          ((1 : ℂ) / (((r * q).totient : ℂ) ^ 2)) *
            ∑ u ∈ charSupp r q b, ∑ v ∈ charSupp r q b,
              (e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) *
                star (e ((a : ℝ) * (v.val : ℝ) / ((r * q : ℕ) : ℝ)))) *
                (χ u⁻¹ * χ v) := by
      intro χ
      unfold charCoeff
      change (((1 : ℂ) / ((r * q).totient : ℂ)) *
          ∑ u ∈ charSupp r q b,
            e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) * star (χ u)) *
        star (((1 : ℂ) / ((r * q).totient : ℂ)) *
          ∑ v ∈ charSupp r q b,
            e ((a : ℝ) * (v.val : ℝ) / ((r * q : ℕ) : ℝ)) * star (χ v)) = _
      rw [star_mul', star_div₀, star_one, star_sum]
      have hstar_nat : star ((r * q).totient : ℂ) = ((r * q).totient : ℂ) := by simp
      rw [hstar_nat]
      have hprod :
          (∑ u ∈ charSupp r q b, e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) * star (χ u)) *
          (∑ v ∈ charSupp r q b, star (e ((a : ℝ) * (v.val : ℝ) / ((r * q : ℕ) : ℝ)) * star (χ v))) =
          ∑ u ∈ charSupp r q b, ∑ v ∈ charSupp r q b,
            (e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) *
              star (e ((a : ℝ) * (v.val : ℝ) / ((r * q : ℕ) : ℝ)))) *
              (χ u⁻¹ * χ v) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun u hu => ?_
        have hu_unit : IsUnit u := (Finset.mem_filter.mp hu).2.1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [star_mul', star_star, star_char_apply_eq_inv χ hu_unit]
        ring
      have hring : ((1 : ℂ) / ((r * q).totient : ℂ) *
            ∑ u ∈ charSupp r q b, e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) * star (χ u)) *
          ((1 / ((r * q).totient : ℂ)) *
            ∑ v ∈ charSupp r q b, star (e ((a : ℝ) * (v.val : ℝ) / ((r * q : ℕ) : ℝ)) * star (χ v))) =
          ((1 : ℂ) / ((r * q).totient : ℂ) ^ 2) *
            ((∑ u ∈ charSupp r q b, e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) * star (χ u)) *
             (∑ v ∈ charSupp r q b, star (e ((a : ℝ) * (v.val : ℝ) / ((r * q : ℕ) : ℝ)) * star (χ v)))) := by
        ring
      rw [hring, hprod]
    calc ∑ χ : DirichletCharacter ℂ (r * q),
            charCoeff r q a b χ * star (charCoeff r q a b χ)
        = ∑ χ : DirichletCharacter ℂ (r * q),
            ((1 : ℂ) / ((r * q).totient : ℂ) ^ 2) *
              ∑ u ∈ charSupp r q b, ∑ v ∈ charSupp r q b,
                (e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) *
                  star (e ((a : ℝ) * (v.val : ℝ) / ((r * q : ℕ) : ℝ)))) *
                  (χ u⁻¹ * χ v) :=
          Finset.sum_congr rfl fun χ _ => hcoeff_star χ
      _ = ((1 : ℂ) / ((r * q).totient : ℂ) ^ 2) *
            ∑ u ∈ charSupp r q b, ∑ v ∈ charSupp r q b,
              (e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) *
                star (e ((a : ℝ) * (v.val : ℝ) / ((r * q : ℕ) : ℝ)))) *
                ∑ χ : DirichletCharacter ℂ (r * q), χ u⁻¹ * χ v := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.mul_sum]
      _ = ((1 : ℂ) / ((r * q).totient : ℂ) ^ 2) *
            ∑ u ∈ charSupp r q b, ∑ v ∈ charSupp r q b,
              (e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) *
                star (e ((a : ℝ) * (v.val : ℝ) / ((r * q : ℕ) : ℝ)))) *
                (if u = v then ((r * q).totient : ℂ) else 0) := by
          congr 1
          refine Finset.sum_congr rfl fun u hu => ?_
          have hu_unit : IsUnit u := (Finset.mem_filter.mp hu).2.1
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu_unit v]
      _ = ((1 : ℂ) / ((r * q).totient : ℂ) ^ 2) *
            ∑ _u ∈ charSupp r q b, ((r * q).totient : ℂ) := by
          congr 1
          refine Finset.sum_congr rfl fun u hu => ?_
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq, hu, ↓reduceIte]
          rw [e_mul_star_e, one_mul]
      _ = ((charSupp r q b).card : ℂ) / ((r * q).totient : ℂ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp [hφC]
  have hRe : ∑ χ : DirichletCharacter ℂ (r * q), ‖charCoeff r q a b χ‖ ^ 2 =
      ((charSupp r q b).card : ℝ) / ((r * q).totient : ℝ) := by
    have h1 := congrArg Complex.re hC
    rw [Complex.re_sum] at h1
    have hterm : ∀ χ : DirichletCharacter ℂ (r * q),
        (charCoeff r q a b χ * star (charCoeff r q a b χ)).re = ‖charCoeff r q a b χ‖ ^ 2 := by
      intro χ
      rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
    have h2 : (((charSupp r q b).card : ℂ) / ((r * q).totient : ℂ)).re =
        ((charSupp r q b).card : ℝ) / ((r * q).totient : ℝ) := by
      have : ((charSupp r q b).card : ℂ) / ((r * q).totient : ℂ) =
          ((((charSupp r q b).card : ℝ) / ((r * q).totient : ℝ) : ℝ) : ℂ) := by
        push_cast; rfl
      rw [this, Complex.ofReal_re]
    rw [← h2, ← h1]
    exact Finset.sum_congr rfl fun χ _ => (hterm χ).symm
  rw [hRe, card_charSupp_eq r q b hr hb]
  have hφR : ((r * q).totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hφ_pos.ne'
  have hφr : (r.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hr).ne'
  field_simp [hφR, hφr]

/-- Elementary totient inequality: `φ(r * q) ≤ q * φ(r)` for all `r, q ≥ 1`. -/
lemma totient_mul_le_mul_totient (r q : ℕ) (hr : 0 < r) (hq : 0 < q) :
    (r * q).totient ≤ q * r.totient := by
  have : NeZero (r * q) := ⟨(Nat.mul_pos hr hq).ne'⟩
  have hcard := totient_mul_card_charSupp r q 1 hr (Nat.coprime_one_left r)
  have hsub : (charSupp r q 1).card ≤ q := by
    have hmem : charSupp r q 1 ⊆
        Finset.univ.image (fun j : Fin q => ((r * j.val + 1 % r : ℕ) : ZMod (r * q))) := by
      intro u hu
      have hu' := (Finset.mem_filter.mp hu).2
      have hlt : u.val / r < q :=
        (Nat.div_lt_iff_lt_mul hr).2 (by simpa [mul_comm] using u.val_lt)
      refine Finset.mem_image.mpr ⟨⟨u.val / r, hlt⟩, Finset.mem_univ _, ?_⟩
      have hdiv : r * (u.val / r) + 1 % r = u.val := by
        rw [← hu'.2]
        exact Nat.div_add_mod u.val r
      rw [hdiv, ZMod.natCast_zmod_val]
    calc (charSupp r q 1).card
        ≤ (Finset.univ.image (fun j : Fin q => ((r * j.val + 1 % r : ℕ) : ZMod (r * q)))).card :=
          Finset.card_le_card hmem
      _ ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_image_le
      _ = q := Fintype.card_fin q
  calc (r * q).totient = r.totient * (charSupp r q 1).card := hcard.symm
    _ ≤ r.totient * q := Nat.mul_le_mul_left _ hsub
    _ = q * r.totient := mul_comm _ _

/-- Self-contained finite Cauchy–Schwarz: `(∑_{x ∈ s} f x)² ≤ s.card * ∑_{x ∈ s} (f x)²`. -/
lemma sq_sum_le_card_mul_sum_sq_real {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ x ∈ s, f x) ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, (f x) ^ 2 := by
  have hnonneg : 0 ≤ ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexpand : ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 =
      2 * ((s.card : ℝ) * ∑ x ∈ s, (f x) ^ 2 - (∑ x ∈ s, f x) ^ 2) := by
    have h1 : ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 =
        ∑ x ∈ s, ∑ y ∈ s, ((f x) ^ 2 - 2 * f x * f y + (f y) ^ 2) :=
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [h1]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ x ∈ s, ∑ y ∈ s, 2 * f x * f y = 2 * (∑ x ∈ s, f x) ^ 2 := by
      have hmul : ∑ x ∈ s, ∑ y ∈ s, 2 * f x * f y =
          2 * ∑ x ∈ s, f x * ∑ y ∈ s, f y := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => by ring
      rw [hmul, ← Finset.sum_mul, sq]
    have h3 : ∑ x ∈ s, (s.card : ℝ) * (f x) ^ 2 = (s.card : ℝ) * ∑ x ∈ s, (f x) ^ 2 := by
      rw [← Finset.mul_sum]
    rw [h2, h3]
    ring
  linarith

/-- **Theorem B1.4 (Sharp global `H₀`-subgroup `ℓ¹` bound):**
`∑ χ, ‖charCoeff r q a b χ‖ ≤ √(φ(rq) / (gcd(r, q) * φ(r)))`. -/
theorem charCoeff_l1_le_sharp (r q a b : ℕ) (hr : 0 < r) (hq : 0 < q)
    (hb : Nat.Coprime b r) [NeZero (r * q)] :
    ∑ χ : DirichletCharacter ℂ (r * q), ‖charCoeff r q a b χ‖ ≤
      Real.sqrt (((r * q).totient : ℝ) / ((Nat.gcd r q : ℝ) * (r.totient : ℝ))) := by
  classical
  have hsum_eq : ∑ χ : DirichletCharacter ℂ (r * q), ‖charCoeff r q a b χ‖ =
      ∑ χ ∈ charFiber r q a b, ‖charCoeff r q a b χ‖ := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun χ _ hχ => ?_
    have hz : charCoeff r q a b χ = 0 := by
      by_contra hnez
      apply hχ
      rw [charFiber, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, char_hGen_eq_of_charCoeff_ne_zero r q a b hr hq χ hnez⟩
    simp [hz]
  have hcs := sq_sum_le_card_mul_sum_sq_real (charFiber r q a b) fun χ => ‖charCoeff r q a b χ‖
  have hsq_le : ∑ χ ∈ charFiber r q a b, ‖charCoeff r q a b χ‖ ^ 2 ≤ 1 / (r.totient : ℝ) := by
    rw [← charCoeff_sum_norm_sq r q a b hr hq hb]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  have hS_card : ((charFiber r q a b).card : ℝ) = ((r * q).totient : ℝ) / (Nat.gcd r q : ℝ) := by
    have hc := card_charFiber r q a b hr hq
    have hg0 : (Nat.gcd r q : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.gcd_pos_of_pos_left q hr).ne'
    rw [eq_div_iff hg0]
    exact_mod_cast (by simpa [mul_comm] using hc)
  have hsq_bound : (∑ χ : DirichletCharacter ℂ (r * q), ‖charCoeff r q a b χ‖) ^ 2 ≤
      ((r * q).totient : ℝ) / ((Nat.gcd r q : ℝ) * (r.totient : ℝ)) := by
    rw [hsum_eq]
    calc (∑ χ ∈ charFiber r q a b, ‖charCoeff r q a b χ‖) ^ 2
        ≤ ((charFiber r q a b).card : ℝ) * ∑ χ ∈ charFiber r q a b, ‖charCoeff r q a b χ‖ ^ 2 := hcs
      _ ≤ ((charFiber r q a b).card : ℝ) * (1 / (r.totient : ℝ)) :=
          mul_le_mul_of_nonneg_left hsq_le (Nat.cast_nonneg _)
      _ = ((r * q).totient : ℝ) / ((Nat.gcd r q : ℝ) * (r.totient : ℝ)) := by
          rw [hS_card]; ring
  exact Real.le_sqrt_of_sq_le hsq_bound

/-- **Theorem B1.5 (Clean `ℓ¹` bound for arbitrary composite `r, q ≥ 1`):**
`∑ χ, ‖charCoeff r q a b χ‖ ≤ √(q / gcd(r, q))`. -/
theorem charCoeff_l1_le (r q a b : ℕ) (hr : 0 < r) (hq : 0 < q)
    (hb : Nat.Coprime b r) [NeZero (r * q)] :
    ∑ χ : DirichletCharacter ℂ (r * q), ‖charCoeff r q a b χ‖ ≤
      Real.sqrt ((q : ℝ) / (Nat.gcd r q : ℝ)) := by
  refine (charCoeff_l1_le_sharp r q a b hr hq hb).trans ?_
  apply Real.sqrt_le_sqrt
  have hφ : (r.totient : ℝ) > 0 := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hg : (Nat.gcd r q : ℝ) > 0 := Nat.cast_pos.mpr (Nat.gcd_pos_of_pos_left q hr)
  rw [div_le_div_iff₀ (mul_pos hg hφ) hg]
  have hle : ((r * q).totient : ℝ) ≤ (q : ℝ) * (r.totient : ℝ) := by
    exact_mod_cast totient_mul_le_mul_totient r q hr hq
  nlinarith

end GlobalSubgroup

end FareyGoldbach
