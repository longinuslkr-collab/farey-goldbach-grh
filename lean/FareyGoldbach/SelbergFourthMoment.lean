import FareyGoldbach.SharpRankin
import FareyGoldbach.SelbergFiniteSieve
import FareyGoldbach.SelbergTruncation
import FareyGoldbach.SelbergEulerProduct
import FareyGoldbach.SelbergScale
import FareyGoldbach.SingleAverageLogEdge

/-! # A finite Selberg sieve for the fourth moment of a fixed prime progression -/

open scoped BigOperators Classical Topology
open Filter

namespace FareyGoldbach

/-- Finite fourth-moment identity on the circle. Each triple determines the fourth frequency. -/
theorem integral_norm_fourth_trigPoly (J : ℕ) (f : ℕ → ℝ) :
    (∫ α in (0 : ℝ)..1, ‖∑ j ∈ Finset.range J, (f j : ℂ) * e (α * (j : ℝ))‖ ^ 4) =
      ∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
        if k ≤ i + j ∧ i + j - k < J
        then f i * f j * f k * f (i + j - k) else 0 := by
  let S (α : ℝ) := ∑ j ∈ Finset.range J, (f j : ℂ) * e (α * (j : ℝ))
  let t (i j k l : ℕ) (α : ℝ) :=
    (f i * f j * f k * f l : ℂ) * e ((((k : ℤ) + l - i - j : ℤ) : ℝ) * α)
  have hstar_e (x : ℝ) : star (e x) = e (-x) := by
    apply mul_left_cancel₀ (show e x ≠ 0 from by unfold e; exact Complex.exp_ne_zero _)
    rw [e_mul_star_e, ← e_add, add_neg_cancel, e_zero]
  have hSstar (α : ℝ) :
      star (S α) = ∑ j ∈ Finset.range J, (f j : ℂ) * e (-(α * (j : ℝ))) := by
    dsimp only [S]
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', hstar_e, Complex.star_def, Complex.conj_ofReal]
  have hpoint (α : ℝ) : ((‖S α‖ ^ 4 : ℝ) : ℂ) =
      ∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, ∑ l ∈ Finset.range J,
        t i j k l α := by
    have hnorm : ‖S α‖ ^ 4 = ‖S α ^ 2‖ ^ 2 := by rw [norm_pow]; ring
    rw [hnorm, Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def, pow_two,
      star_mul', hSstar]
    dsimp only [S]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have hexp : e (α * (k : ℝ)) * e (α * (l : ℝ)) *
        (e (-(α * (i : ℝ))) * e (-(α * (j : ℝ)))) =
        e ((((k : ℤ) + l - i - j : ℤ) : ℝ) * α) := by
      rw [← e_add, ← e_add, ← e_add]
      congr 1
      push_cast
      ring
    unfold t
    rw [← hexp]
    ring
  have ht (i j k l : ℕ) : IntervalIntegrable (t i j k l) MeasureTheory.volume 0 1 := by
    exact (continuous_const.mul (continuous_e_mul _)).intervalIntegrable 0 1
  have h₃ (i j k : ℕ) : IntervalIntegrable
      (fun α => ∑ l ∈ Finset.range J, t i j k l α) MeasureTheory.volume 0 1 :=
    intervalIntegrable_finset_sum _ fun l _ => ht i j k l
  have h₂ (i j : ℕ) : IntervalIntegrable
      (fun α => ∑ k ∈ Finset.range J, ∑ l ∈ Finset.range J, t i j k l α) MeasureTheory.volume 0 1 :=
    intervalIntegrable_finset_sum _ fun k _ => h₃ i j k
  have h₁ (i : ℕ) : IntervalIntegrable
      (fun α => ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, ∑ l ∈ Finset.range J,
        t i j k l α) MeasureTheory.volume 0 1 :=
    intervalIntegrable_finset_sum _ fun j _ => h₂ i j
  have hC : ((∫ α in (0 : ℝ)..1, ‖S α‖ ^ 4 : ℝ) : ℂ) =
      (∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
        if k ≤ i + j ∧ i + j - k < J then f i * f j * f k * f (i + j - k) else 0 : ℝ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [hpoint, Complex.ofReal_sum]
    rw [intervalIntegral_finset_sum (fun i _ => h₁ i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral_finset_sum (fun j _ => h₂ i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral_finset_sum (fun k _ => h₃ i j k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral_finset_sum (fun l _ => ht i j k l)]
    simp_rw [t, intervalIntegral.integral_const_mul, integral_e_int]
    by_cases h : k ≤ i + j ∧ i + j - k < J
    · rw [ite_eq_left h, Finset.sum_eq_single (i+j-k)]
      · have he : (k : ℤ) + (↑(i + j - k) : ℤ) - i - j = 0 := by omega
        rw [ite_eq_left he, mul_one]
        push_cast
        ring
      · intro l _ hl
        have he : (k : ℤ) + l - i - j ≠ 0 := by omega
        simp only [he, ite_false, mul_zero]
      · exact fun hn => (hn (Finset.mem_range.mpr h.2)).elim
    · rw [ite_eq_right h, Complex.ofReal_zero]
      refine Finset.sum_eq_zero fun l hl => ?_
      have hlJ := Finset.mem_range.mp hl
      have he : (k : ℤ) + l - i - j ≠ 0 := by omega
      simp only [he, ite_false, mul_zero]
  exact_mod_cast hC

/-- Three residue coordinates for which all four coordinates of the additive quadruple
are nonzero. -/
def fourFormsGood {F : Type*} [AddGroup F] (v : F × F × F) : Prop :=
  v.1 ≠ 0 ∧ v.2.1 ≠ 0 ∧ v.2.2 ≠ 0 ∧ v.1 + v.2.1 - v.2.2 ≠ 0

private lemma pairFirst_heq {F : Type*} [Zero F] {s t : F} (h : s = t)
    {x z : {v : F // v ≠ 0 ∧ v ≠ s}} {y w : {v : F // v ≠ 0 ∧ v ≠ t}}
    (hx : x.1 = y.1) (hz : z.1 = w.1) : HEq (x, z) (y, w) := by
  subst t
  exact heq_of_eq (Prod.ext (Subtype.ext hx) (Subtype.ext hz))

private def fourFormsGoodEquiv (F : Type*) [AddCommGroup F] :
    {v : F × F × F // fourFormsGood v} ≃
      Σ t : F, {x : F // x ≠ 0 ∧ x ≠ t} × {z : F // z ≠ 0 ∧ z ≠ t} where
  toFun v := by
    obtain ⟨⟨x, y, z⟩, hx, hy, hz, hw⟩ := v
    exact ⟨x + y, ⟨x, hx, fun h => hy (add_eq_left.mp h.symm)⟩,
      ⟨z, hz, fun h => hw (sub_eq_zero.mpr h.symm)⟩⟩
  invFun v := by
    obtain ⟨t, ⟨x, hx, hxt⟩, ⟨z, hz, hzt⟩⟩ := v
    exact ⟨(x, t - x, z), hx, sub_ne_zero.mpr hxt.symm, hz, by
      have he : x + (t - x) - z = t - z := by abel
      rw [he]
      exact sub_ne_zero.mpr hzt.symm⟩
  left_inv v := by
    obtain ⟨⟨x, y, z⟩, hv⟩ := v
    apply Subtype.ext
    change (x, x + y - x, z) = (x, y, z)
    have he : x + y - x = y := by abel
    rw [he]
  right_inv v := by
    obtain ⟨t, ⟨x, hx⟩, ⟨z, hz⟩⟩ := v
    have he : x + (t - x) = t := by abel
    refine Sigma.ext he ?_
    apply pairFirst_heq he <;> rfl

/-- Exact number of residue triples avoiding the four linear forms. -/
theorem fourFormsGood_card (F : Type*) [AddCommGroup F] [Fintype F] :
    Fintype.card {v : F × F × F // fourFormsGood v} =
      (Fintype.card F - 1)^2 + (Fintype.card F - 1) * (Fintype.card F - 2)^2 := by
  classical
  have hpair (t : F) : Fintype.card {x : F // x ≠ 0 ∧ x ≠ t} =
      if t = 0 then Fintype.card F - 1 else Fintype.card F - 2 := by
    rw [Fintype.card_subtype]
    have hf : (Finset.univ.filter (fun x : F => x ≠ 0 ∧ x ≠ t)) =
        ((Finset.univ : Finset F).erase 0).erase t := by ext x; simp [and_comm]
    rw [hf]
    split_ifs with ht
    · subst t
      simp [Finset.card_erase_of_mem]
    · rw [Finset.card_erase_of_mem (by simp [ht]), Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ]
      omega
  rw [Fintype.card_congr (fourFormsGoodEquiv F), Fintype.card_sigma]
  simp_rw [Fintype.card_prod, hpair, ← pow_two]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))]
  have hsum : ∑ t ∈ (Finset.univ : Finset F).erase 0,
      ((if t = 0 then Fintype.card F - 1 else Fintype.card F - 2) : ℕ)^2 =
        (Fintype.card F - 1) * (Fintype.card F - 2)^2 := by
    calc _ = ∑ _t ∈ (Finset.univ : Finset F).erase 0, ((Fintype.card F - 2) : ℕ)^2 :=
              Finset.sum_congr rfl fun t ht => by rw [ite_eq_right (Finset.ne_of_mem_erase ht)]
         _ = _ := by simp [Finset.card_erase_of_mem]
  rw [hsum, ite_eq_left rfl]

/-- Local condition on the four progression values over a residue field. -/
def progressionFormsGood (r b p : ℕ) (v : ZMod p × ZMod p × ZMod p) : Prop :=
  (r : ZMod p) * v.1 + b ≠ 0 ∧
  (r : ZMod p) * v.2.1 + b ≠ 0 ∧
  (r : ZMod p) * v.2.2 + b ≠ 0 ∧
  (r : ZMod p) * (v.1 + v.2.1 - v.2.2) + b ≠ 0

theorem progressionFormsGood_card {r b p : ℕ} [Fact p.Prime] (hrp : (r : ZMod p) ≠ 0) :
    Fintype.card {v : ZMod p × ZMod p × ZMod p // progressionFormsGood r b p v} =
      (p - 1)^2 + (p - 1) * (p - 2)^2 := by
  let A : Equiv.Perm (ZMod p) := (Equiv.mulLeft₀ (r : ZMod p) hrp).trans (Equiv.addRight (b : ZMod p))
  let E := Equiv.prodCongr A (Equiv.prodCongr A A)
  have heq : ∀ v : ZMod p × ZMod p × ZMod p, progressionFormsGood r b p v ↔ fourFormsGood (E v) := by
    intro ⟨x, y, z⟩
    have h : (r : ZMod p) * (x+y-z) + b =
        ((r : ZMod p) * x + b) + ((r : ZMod p) * y + b) - ((r : ZMod p) * z + b) := by ring
    unfold progressionFormsGood fourFormsGood
    change _ ∧ _ ∧ _ ∧ (r : ZMod p) * (x+y-z)+b ≠ 0 ↔ _ ∧ _ ∧ _ ∧
      (((r : ZMod p) * x + b) + ((r : ZMod p) * y + b) - ((r : ZMod p) * z + b)) ≠ 0
    rw [h]
    rfl
  rw [Fintype.card_congr (E.subtypeEquiv heq), fourFormsGood_card, ZMod.card]

/-- Fraction of residues surviving the four-form local sieve at a prime. -/
noncomputable def progressionSieveSurvival (p : ℕ) : ℝ :=
  (((p : ℝ) - 1)^2 + ((p : ℝ) - 1) * ((p : ℝ) - 2)^2) / (p : ℝ)^3

noncomputable def progressionSieveG (p : ℕ) : ℝ :=
  (1 - progressionSieveSurvival p) / progressionSieveSurvival p

noncomputable def progressionSieveWeight (r b p : ℕ) (v : ZMod p × ZMod p × ZMod p) : ℝ :=
  if progressionFormsGood r b p v then progressionSieveG p else -1

theorem progressionSieveSurvival_bounds {p : ℕ} (hp : 11 ≤ p) :
    1 - 4 / (p : ℝ) ≤ progressionSieveSurvival p ∧ progressionSieveSurvival p ≤ 1 := by
  have hp' : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < p := by linarith
  unfold progressionSieveSurvival
  constructor
  · apply (le_div_iff₀ (pow_pos hp_pos 3)).2
    have he : (1 - 4 / (p : ℝ)) * (p : ℝ)^3 = (p : ℝ)^3 - 4*(p : ℝ)^2 := by
      field_simp
    rw [he]
    nlinarith only [hp']
  · apply (div_le_iff₀ (pow_pos hp_pos 3)).2
    have hn := mul_nonneg (show (0 : ℝ) ≤ p - 1 by linarith) (show (0 : ℝ) ≤ 4*(p : ℝ) - 2 by linarith)
    nlinarith only [hn]

theorem progressionSieveSurvival_half {p : ℕ} (hp : 11 ≤ p) :
    (1 / 2 : ℝ) ≤ progressionSieveSurvival p := by
  have hp' : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < p := by linarith
  have hdiv : 4 / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp_pos).2 (by linarith)
  exact (by linarith : (1 / 2 : ℝ) ≤ 1 - 4 / p).trans (progressionSieveSurvival_bounds hp).1

theorem progressionSieveSurvival_factor {p : ℕ} (hp : 11 ≤ p) :
    progressionSieveSurvival p = (1 - 1 / (p : ℝ))^4 * (1 + 1 / ((p : ℝ) - 1)^3) := by
  have hp' : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < p := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  unfold progressionSieveSurvival
  field_simp
  ring

theorem progressionSieveG_bounds {p : ℕ} (hp : 11 ≤ p) :
    0 ≤ progressionSieveG p ∧ progressionSieveG p ≤ 1 := by
  have hs := progressionSieveSurvival_half hp
  have hs' := (progressionSieveSurvival_bounds hp).2
  have hsp : 0 < progressionSieveSurvival p := by linarith
  unfold progressionSieveG
  exact ⟨div_nonneg (by linarith) hsp.le, (div_le_iff₀ hsp).2 (by linarith)⟩

theorem progressionSieveG_ratio {p : ℕ} (hp : 11 ≤ p) :
    progressionSieveG p / (1 + progressionSieveG p) = 1 - progressionSieveSurvival p := by
  have hs : 0 < progressionSieveSurvival p := by linarith [progressionSieveSurvival_half hp]
  have hg : 0 < 1 + progressionSieveG p := by linarith [(progressionSieveG_bounds hp).1]
  apply (div_eq_iff hg.ne').2
  unfold progressionSieveG
  field_simp
  ring

theorem progressionSieveWeight_abs {r b p : ℕ} (hp : 11 ≤ p)
    (v : ZMod p × ZMod p × ZMod p) : |progressionSieveWeight r b p v| ≤ 1 := by
  unfold progressionSieveWeight
  split_ifs
  · obtain ⟨h₁, h₂⟩ := progressionSieveG_bounds hp
    rwa [abs_of_nonneg h₁]
  · norm_num

theorem progressionSieveWeight_moments {r b p : ℕ} [Fact p.Prime] (hp : 11 ≤ p)
    (hrp : (r : ZMod p) ≠ 0) :
    (∑ v : ZMod p × ZMod p × ZMod p, progressionSieveWeight r b p v) = 0 ∧
    (∑ v : ZMod p × ZMod p × ZMod p, (progressionSieveWeight r b p v)^2) =
      (p : ℝ)^3 * progressionSieveG p := by
  classical
  let F := ZMod p × ZMod p × ZMod p
  let P := progressionFormsGood r b p
  let A := (Finset.univ : Finset F).filter P
  let B := (Finset.univ : Finset F).filter (fun v => ¬P v)
  let s := progressionSieveSurvival p
  let g := progressionSieveG p
  have hcardN : ((Finset.univ : Finset F).card : ℝ) = (p : ℝ)^3 := by
    simp [F, ZMod.card, pow_succ, mul_assoc]
  have hp' : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hpr : (0 : ℝ) < p := by linarith
  have hA : (A.card : ℝ) = (p : ℝ)^3*s := by
    have hc := Fintype.card_subtype P
    change Fintype.card {v : F // P v} = A.card at hc
    rw [← hc, progressionFormsGood_card (b := b) hrp]
    dsimp [s, progressionSieveSurvival]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
      Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub (by omega : 2 ≤ p)]
    push_cast
    field_simp
  have hB : (B.card : ℝ) = (p : ℝ)^3*(1-s) := by
    have he : A.card + B.card = (Finset.univ : Finset F).card :=
      Finset.card_filter_add_card_filter_not _
    have he' : (A.card : ℝ) + (B.card : ℝ) = ((Finset.univ : Finset F).card : ℝ) := by exact_mod_cast he
    rw [hcardN, hA] at he'
    linarith only [he']
  have hs : 0 < s := by dsimp [s]; linarith [progressionSieveSurvival_half hp]
  have hg : g = (1-s)/s := rfl
  constructor
  · change (∑ v : F, if P v then g else -1) = _
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul]
    change (A.card : ℝ)*g+(B.card : ℝ)*(-1) = _
    rw [hA, hB, hg]
    field_simp
    ring
  · change (∑ v : F, (if P v then g else -1)^2) = _*g
    have hpw (v : F) : (if P v then g else -1)^2 = if P v then g^2 else (-1:ℝ)^2 := by
      split_ifs <;> rfl
    simp only [hpw]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul]
    change (A.card : ℝ)*g^2+(B.card : ℝ)*(-1)^2 = _*g
    rw [hA, hB, hg]
    field_simp
    ring

/-- A prime additive quadruple encoded by its first three indices. -/
noncomputable def progressionPrimeTriples (r b J : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (sieveCube J).filter (fun x : ℕ × ℕ × ℕ =>
    x.2.2 ≤ x.1 + x.2.1 ∧ x.1 + x.2.1 - x.2.2 < J ∧
    (r*x.1+b).Prime ∧ (r*x.2.1+b).Prime ∧ (r*x.2.2+b).Prime ∧
    (r*(x.1+x.2.1-x.2.2)+b).Prime)

/-- The smoothed weighted fourth moment is bounded by the unweighted prime quadruple count. -/
theorem fourthMoment_le_primeTriples (r b Y : ℕ) (hY : 1 ≤ Y) :
    (∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b Y α‖^4) ≤
      (progressionPrimeTriples r b (Y/r+1)).card * Real.log (2 * (Y : ℝ))^4 := by
  let J := Y/r+1
  let L := Real.log (2*(Y : ℝ))
  let f (j : ℕ) := quarticBump (((r * j + b : ℕ) : ℝ) / Y) * primeWeight (r*j+b)
  have hy : (0:ℝ) < Y := Nat.cast_pos.mpr (by omega)
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2*Y))
  have hf (j : ℕ) : 0 ≤ f j ∧ f j ≤ L := by
    let x := (((r*j+b : ℕ) : ℝ) / Y)
    have hn := quarticBump_nonneg x
    have hh := quarticBump_le_one x
    have hp := primeWeight_nonneg (r*j+b)
    refine ⟨mul_nonneg hn hp, ?_⟩
    by_cases hx : 0 < x ∧ x < 1
    · have hd : ((r*j+b : ℕ) : ℝ) < Y := (div_lt_one hy).mp hx.2
      have hj : r*j+b ≤ Y := by exact_mod_cast hd.le
      calc f j ≤ 1 * primeWeight (r*j+b) := mul_le_mul_of_nonneg_right hh hp
        _ = primeWeight (r*j+b) := one_mul _
        _ ≤ Real.log (Y : ℝ) := primeWeight_le_log hj
        _ ≤ L := Real.log_le_log hy (by linarith [hy.le])
    · change quarticBump x * _ ≤ L
      simp only [quarticBump, ite_eq_right hx, zero_mul]
      exact hL
  have hS (α : ℝ) : smoothedPrimeSum r b Y α =
      ∑ j ∈ Finset.range J, (f j : ℂ) * e (α*(j : ℝ)) := by
    unfold smoothedPrimeSum
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [f]
  simp_rw [hS]
  rw [integral_norm_fourth_trigPoly]
  let G (x : ℕ × ℕ × ℕ) : ℝ :=
    if x.2.2 ≤ x.1+x.2.1 ∧ x.1+x.2.1-x.2.2 < J then
      f x.1 * f x.2.1 * f x.2.2 * f (x.1+x.2.1-x.2.2) else 0
  let V (x : ℕ × ℕ × ℕ) : ℝ :=
    if x ∈ progressionPrimeTriples r b J then L^4 else 0
  have he : (∑ x ∈ sieveCube J, G x) =
      ∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, G (i,j,k) := by
    simp [sieveCube, Finset.sum_product]
  change (∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, G (i,j,k)) ≤ _
  rw [← he]
  calc (∑ x ∈ sieveCube J, G x) ≤ ∑ x ∈ sieveCube J, V x := by
        refine Finset.sum_le_sum fun x hx => ?_
        obtain ⟨i,j,k⟩ := x
        by_cases hJ : k ≤ i+j ∧ i+j-k < J
        · by_cases hp : (r*i+b).Prime ∧ (r*j+b).Prime ∧ (r*k+b).Prime ∧ (r*(i+j-k)+b).Prime
          · have hm : (i,j,k) ∈ progressionPrimeTriples r b J :=
              Finset.mem_filter.mpr ⟨hx, hJ.1, hJ.2, hp⟩
            change G (i,j,k) ≤ V (i,j,k)
            dsimp [G, V]
            rw [ite_eq_left hJ, ite_eq_left hm]
            calc f i * f j * f k * f (i+j-k) ≤ L*L*L*L :=
                mul_le_mul
                  (mul_le_mul (mul_le_mul (hf i).2 (hf j).2 (hf j).1 hL) (hf k).2 (hf k).1 (by positivity))
                  (hf (i+j-k)).2 (hf _).1 (by positivity)
              _ = _ := by ring
          · have hnp : ¬(r*i+b).Prime ∨ ¬(r*j+b).Prime ∨ ¬(r*k+b).Prime ∨ ¬(r*(i+j-k)+b).Prime := by
              tauto
            have hG : G (i,j,k) = 0 := by
              rcases hnp with hs | hs | hs | hs <;> simp [G, hJ, f, primeWeight, hs]
            rw [hG]
            dsimp [V]
            split_ifs <;> positivity
        · have hG : G (i,j,k) = 0 := ite_eq_right hJ
          rw [hG]
          dsimp [V]
          split_ifs <;> positivity
    _ = _ := by
        dsimp [V]
        rw [← Finset.sum_filter]
        have hsubset : progressionPrimeTriples r b J ⊆ sieveCube J := Finset.filter_subset ..
        rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsubset]
        simp [J, L, nsmul_eq_mul]

noncomputable def progressionSievedTriples (r b J : ℕ) (P : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (sieveCube J).filter fun x : ℕ × ℕ × ℕ => ∀ p ∈ P,
    progressionFormsGood r b p ((x.1 : ZMod p), (x.2.1 : ZMod p), (x.2.2 : ZMod p))

private lemma primeTriples_small_card {r b J z : ℕ} (hr : 0 < r) :
    let s := progressionPrimeTriples r b J
    let L₁ := s.filter (fun x => r*x.1+b ≤ z)
    let L₂ := s.filter (fun x => r*x.2.1+b ≤ z)
    let L₃ := s.filter (fun x => r*x.2.2+b ≤ z)
    let L₄ := s.filter (fun x => r*(x.1+x.2.1-x.2.2)+b ≤ z)
    (((L₁ ∪ L₂) ∪ L₃) ∪ L₄).card ≤ 4 * (z+1) * J^2 := by
  dsimp only
  set s := progressionPrimeTriples r b J
  set L₁ := s.filter (fun x => r*x.1+b ≤ z)
  set L₂ := s.filter (fun x => r*x.2.1+b ≤ z)
  set L₃ := s.filter (fun x => r*x.2.2+b ≤ z)
  set L₄ := s.filter (fun x => r*(x.1+x.2.1-x.2.2)+b ≤ z)
  let t : Finset (ℕ × ℕ × ℕ) := (Finset.range (z+1)).product ((Finset.range J).product (Finset.range J))
  have ht : t.card = (z+1)*J^2 := by simp [t, pow_two]
  have hphys {j : ℕ} (h : r*j+b ≤ z) : j < z+1 :=
    Nat.lt_succ_of_le (by simpa using (Nat.mul_le_mul_right j hr).trans (Nat.le_of_add_right_le h))
  have hmem {x : ℕ × ℕ × ℕ} (hx : x ∈ s) :
      x.1 < J ∧ x.2.1 < J ∧ x.2.2 < J ∧ x.2.2 ≤ x.1+x.2.1 := by
    have hc := (Finset.mem_filter.mp hx).1
    obtain ⟨a,d,e⟩ := (by simpa [sieveCube] using hc :
      x.1 < J ∧ x.2.1 < J ∧ x.2.2 < J)
    exact ⟨a,d,e,(Finset.mem_filter.mp hx).2.1⟩
  have h₁ : L₁.card ≤ t.card := by
    refine Finset.card_le_card_of_injOn id ?_ (fun _ _ _ _ h => h)
    intro x hx
    have h := Finset.mem_filter.mp hx
    have hm := hmem h.1
    simpa [t] using And.intro (hphys h.2) (And.intro hm.2.1 hm.2.2.1)
  have h₂ : L₂.card ≤ t.card := by
    refine Finset.card_le_card_of_injOn (fun x => (x.2.1,x.1,x.2.2)) ?_ ?_
    · intro x hx
      have h := Finset.mem_filter.mp hx
      have hm := hmem h.1
      simpa [t] using And.intro (hphys h.2) (And.intro hm.1 hm.2.2.1)
    · rintro ⟨x,y,z⟩ _ ⟨x',y',z'⟩ _ h
      simpa [Prod.mk.injEq, and_left_comm, and_assoc, and_comm] using h
  have h₃ : L₃.card ≤ t.card := by
    refine Finset.card_le_card_of_injOn (fun x => (x.2.2,x.1,x.2.1)) ?_ ?_
    · intro x hx
      have h := Finset.mem_filter.mp hx
      have hm := hmem h.1
      simpa [t] using And.intro (hphys h.2) (And.intro hm.1 hm.2.1)
    · rintro ⟨x,y,z⟩ _ ⟨x',y',z'⟩ _ h
      simpa [Prod.mk.injEq, and_left_comm, and_assoc, and_comm] using h
  have h₄ : L₄.card ≤ t.card := by
    refine Finset.card_le_card_of_injOn (fun x => (x.1+x.2.1-x.2.2,x.1,x.2.1)) ?_ ?_
    · intro x hx
      have h := Finset.mem_filter.mp hx
      have hm := hmem h.1
      simpa [t] using And.intro (hphys h.2) (And.intro hm.1 hm.2.1)
    · rintro ⟨x,y,z⟩ hx ⟨x',y',z'⟩ hy h
      obtain ⟨hn,ex,ey⟩ := (by simpa using h : x+y-z=x'+y'-z' ∧ x=x' ∧ y=y')
      subst x'
      subst y'
      have hzl := (hmem (Finset.mem_filter.mp hx).1).2.2.2
      have hzr := (hmem (Finset.mem_filter.mp hy).1).2.2.2
      change z ≤ x+y at hzl
      change z' ≤ x+y at hzr
      have he : z = z' := by omega
      subst z'
      rfl
  calc (((L₁ ∪ L₂) ∪ L₃) ∪ L₄).card ≤ (L₁ ∪ L₂ ∪ L₃).card + L₄.card := Finset.card_union_le _ _
    _ ≤ (L₁ ∪ L₂).card + L₃.card + L₄.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ L₁.card + L₂.card + L₃.card + L₄.card :=
      Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
    _ ≤ _ := by rw [mul_assoc, ← ht]; omega

theorem progressionPrimeTriples_card_le_sieved {r b J z : ℕ} (hr : 0 < r) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ z) :
    (progressionPrimeTriples r b J).card ≤
      (progressionSievedTriples r b J P).card + 4*(z+1)*J^2 := by
  let s := progressionPrimeTriples r b J
  let L₁ := s.filter (fun x => r*x.1+b ≤ z)
  let L₂ := s.filter (fun x => r*x.2.1+b ≤ z)
  let L₃ := s.filter (fun x => r*x.2.2+b ≤ z)
  let L₄ := s.filter (fun x => r*(x.1+x.2.1-x.2.2)+b ≤ z)
  let T := (((L₁ ∪ L₂) ∪ L₃) ∪ L₄)
  let S := progressionSievedTriples r b J P
  have hsubset : s ⊆ S ∪ T := by
    intro x hx
    by_cases ht : x ∈ T
    · exact Finset.mem_union_right S ht
    refine Finset.mem_union_left T (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, ?_⟩)
    intro p hp
    obtain ⟨hprime,hz⟩ := hP p hp
    obtain ⟨h0,_,h1,h2,h3,h4⟩ := (Finset.mem_filter.mp hx).2
    have hnot : ¬r*x.1+b ≤ z ∧ ¬r*x.2.1+b ≤ z ∧ ¬r*x.2.2+b ≤ z ∧
        ¬r*(x.1+x.2.1-x.2.2)+b ≤ z := by
      simp [T,L₁,L₂,L₃,L₄,hx] at ht
      simpa only [not_le] using ht
    have hval {n : ℕ} (hn : n.Prime) (hlt : ¬n ≤ z) : (n : ZMod p) ≠ 0 := by
      intro hf
      have hd := (ZMod.natCast_eq_zero_iff n p).mp hf
      rcases (Nat.dvd_prime hn).mp hd with h | h
      · exact hprime.ne_one h
      · exact hlt (h ▸ hz)
    have he : ((r*(x.1+x.2.1-x.2.2)+b : ℕ) : ZMod p) =
        (r : ZMod p)*((x.1 : ZMod p)+(x.2.1 : ZMod p)-(x.2.2 : ZMod p))+b := by
      push_cast [Nat.cast_sub h0]
      rfl
    exact ⟨by simpa using hval h1 hnot.1, by simpa using hval h2 hnot.2.1,
      by simpa using hval h3 hnot.2.2.1, he ▸ hval h4 hnot.2.2.2⟩
  exact (Finset.card_le_card hsubset).trans
    ((Finset.card_union_le S T).trans (Nat.add_le_add_left (primeTriples_small_card hr) _))

theorem progressionSieveMass_ge_half {P : Finset ℕ} {k : ℕ} (hk : 0 < k)
    (hP : ∀ p ∈ P, 11 ≤ p ∧ p ∈ Nat.primesLE (2^k)) :
    (∏ p ∈ P, (1 + progressionSieveG p)) / 2 ≤
      sieveMass P ((2^k)^32) progressionSieveG := by
  classical
  let z : ℕ := 2^k
  let D : ℕ := z^32
  let f (p : ℕ) := Real.log (p:ℝ)
  let g := progressionSieveG
  have hk' : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hD : 0 < D := by dsimp [D,z]; positivity
  have hD' : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hlog2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2:ℝ) (2:ℕ)
    norm_num at h
    exact h
  have hlogD : Real.log (D:ℝ) = 32*(k:ℝ)*Real.log 2 := by
    dsimp [D,z]
    push_cast
    rw [Real.log_pow, Real.log_pow]
    ring
  have hmean : ∑ p ∈ P, (g p/(1+g p))*f p ≤ Real.log (D:ℝ)/2 := by
    calc
      _ ≤ ∑ p ∈ P, 4 * (Real.log (p:ℝ)/(p:ℝ)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp11 := (hP p hp).1
        have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
        dsimp only [g,f]
        rw [progressionSieveG_ratio hp11]
        have hnu : 1 - progressionSieveSurvival p ≤ 4/(p:ℝ) := by
          linarith [(progressionSieveSurvival_bounds hp11).1]
        calc _ ≤ (4/(p:ℝ))*Real.log (p:ℝ) :=
                mul_le_mul_of_nonneg_right hnu (Real.log_nonneg hp1)
          _ = _ := by ring
      _ ≤ ∑ p ∈ Nat.primesLE z, 4 * (Real.log (p:ℝ)/(p:ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (hP p hp).2) fun p hp _ => ?_
        have hpp := Nat.prime_of_mem_primesLE hp
        have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hpp.one_le
        have := Real.log_nonneg hp1
        positivity
      _ ≤ 4 * (2 * Real.log 4 * (k:ℝ)) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_prime_log_div_dyadic k) (by norm_num)
      _ = Real.log (D:ℝ)/2 := by rw [hlogD,hlog4]; ring
  have htr := subset_product_truncation P g f (T := Real.log (D:ℝ))
    (fun p hp => (progressionSieveG_bounds (hP p hp).1).1)
    (fun p hp => Real.log_nonneg (by exact_mod_cast (by have := (hP p hp).1; omega : 1 ≤ p)))
    (by rw [hlogD]; positivity) hmean
  have hfilter :
      P.powerset.filter (fun s : Finset ℕ => (∑ p ∈ s, f p) ≤ Real.log (D:ℝ)) =
      sieveIndices P D := by
    ext s
    simp only [sieveIndices, Finset.mem_filter, Finset.mem_powerset, and_congr_right_iff]
    intro hs
    have hp' {p : ℕ} (hp : p ∈ s) : (0:ℝ) < p := by
      exact_mod_cast (by have := (hP p (hs hp)).1; omega : 0 < p)
    have hpos : 0 < ∏ p ∈ s, (p:ℝ) := Finset.prod_pos fun _ hp => hp' hp
    dsimp only [f,sieveModulus]
    rw [← Real.log_prod (fun _ hp => (hp' hp).ne'), Real.log_le_log_iff hpos hD']
    rw [← Nat.cast_prod]
    exact_mod_cast (Iff.rfl : (∏ p ∈ s, p) ≤ D ↔ (∏ p ∈ s, p) ≤ D)
  rw [hfilter] at htr
  exact htr

/-- Convert the retained sieve mass into the fourth power of the reciprocal Euler product. -/
theorem progressionSieveMass_controls_euler {P : Finset ℕ} {D : ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ 11 ≤ p)
    (hretain : (∏ p ∈ P, (1 + progressionSieveG p)) / 2 ≤
      sieveMass P D progressionSieveG) :
    (∏ p ∈ P, (1 - 1/(p:ℝ))⁻¹)^4 ≤
      (2 * Real.exp (1/2)) * sieveMass P D progressionSieveG := by
  let f (p : ℕ) : ℝ := 1 - 1/(p:ℝ)
  let c (p : ℕ) : ℝ := 1 + 1 / ((p:ℝ)-1)^3
  let w (p : ℕ) : ℝ := 1 + progressionSieveG p
  have hlocal : ∀ p ∈ P, (f p)⁻¹ ^ 4 = w p * c p := by
    intro p hp
    have hp11 := (hP p hp).2
    have hp' : (11:ℝ) ≤ p := by exact_mod_cast hp11
    have hpos : (0:ℝ)<p := by linarith
    have hf : 0 < f p := by
      dsimp [f]
      have : (1 : ℝ) / p < 1 := (div_lt_iff₀ hpos).2 (by linarith)
      linarith
    have hs : 0 < progressionSieveSurvival p := by linarith [progressionSieveSurvival_half hp11]
    have hc : 0 < c p := by
      dsimp [c]
      have : 0 < (p:ℝ)-1 := by linarith
      positivity
    have hw : w p = (progressionSieveSurvival p)⁻¹ := by
      dsimp [w,progressionSieveG]
      field_simp
      ring
    rw [hw, progressionSieveSurvival_factor hp11]
    change (f p)⁻¹ ^ 4 = ((f p)^4*c p)⁻¹ * c p
    field_simp
  have hc : (∏ p ∈ P, c p) ≤ Real.exp (1/2) := by
    refine (real_prod_le_prod P c (fun p => 1 + 1/((p:ℝ)-1)^2) ?_ ?_).trans
      (prod_odd_prime_one_add_inv_pred_sq_le P (fun p hp => ⟨(hP p hp).1, by have := (hP p hp).2; omega⟩))
    · intro p hp
      have hn : 0 ≤ (p:ℝ)-1 := by
        have h : (11:ℝ) ≤ p := by exact_mod_cast (hP p hp).2
        linarith
      dsimp [c]
      positivity
    · intro p hp
      have hp' : (11:ℝ) ≤ p := by exact_mod_cast (hP p hp).2
      have hn : 1 ≤ (p:ℝ)-1 := by linarith
      change (1 : ℝ)+1/((p:ℝ)-1)^3 ≤ 1 + 1/((p:ℝ)-1)^2
      have hpos : (0:ℝ) < ((p:ℝ)-1)^2 := by positivity
      have hpow : ((p:ℝ)-1)^2 ≤ ((p:ℝ)-1)^3 := pow_le_pow_right₀ hn (by decide)
      exact add_le_add (le_refl (1:ℝ)) (one_div_le_one_div_of_le hpos hpow)
  have hw : 0 ≤ ∏ p ∈ P, w p :=
    Finset.prod_nonneg fun p hp => by dsimp [w]; linarith [(progressionSieveG_bounds (hP p hp).2).1]
  calc
    (∏ p ∈ P, (f p)⁻¹)^4 = ∏ p ∈ P, (f p)⁻¹ ^ 4 := by rw [Finset.prod_pow]
    _ = (∏ p ∈ P, w p) * ∏ p ∈ P, c p := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl hlocal
    _ ≤ (∏ p ∈ P, w p) * Real.exp (1/2) := mul_le_mul_of_nonneg_left hc hw
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right hretain (Real.exp_nonneg (1/2))
      change ((∏ p ∈ P, w p)/2)*Real.exp (1/2) ≤ _ at h
      linarith only [h]

private theorem selberg_fourth_count_arithmetic {n s J z D G K L W : ℝ}
    (hs : 0 ≤ s) (hJ : 1 ≤ J) (hz : 0 ≤ z)
    (hG : 1 ≤ G) (hK : 0 ≤ K) (hL : 0 ≤ L) (hW : 1 ≤ W)
    (hcount : n ≤ s + 4 * (z + 1) * J^2)
    (hsieve : s * G^2 ≤ J^3*G + 6*J^2*D^4)
    (hD : D^4 ≤ J) (hzJ : z^2 ≤ J)
    (hlog : L^4 ≤ 240000 * Real.sqrt J)
    (hden : L^4 ≤ K*W*G) :
    n * L^4 ≤ (7*K + 1920000)*W*J^3 := by
  have hJ0 : 0 ≤ J := by linarith
  have hJ2 : 0 ≤ J^2 := sq_nonneg _
  have hJ3 : 0 ≤ J^3 := pow_nonneg hJ0 _
  have hGL : 0 < G := by linarith
  have hD' : 6*J^2*D^4 ≤ 6*J^3 := by
    have h := mul_le_mul_of_nonneg_left hD (show 0 ≤ 6*J^2 by positivity)
    nlinarith only [h]
  have hGa : 6*J^3 ≤ 6*J^3*G := by
    have h := mul_le_mul_of_nonneg_left hG (show 0 ≤ 6*J^3 by positivity)
    nlinarith only [h]
  have hsel : s * G ≤ 7*J^3 := by
    apply le_of_mul_le_mul_right _ hGL
    nlinarith only [hsieve,hD',hGa]
  have hsel' : s*L^4 ≤ 7*K*W*J^3 := by
    calc s*L^4 ≤ s*(K*W*G) := mul_le_mul_of_nonneg_left hden hs
      _ = K*W*(s*G) := by ring
      _ ≤ K*W*(7*J^3) := mul_le_mul_of_nonneg_left hsel (by positivity)
      _ = _ := by ring
  have hsqrt2 := Real.sq_sqrt hJ0
  have hzs : z ≤ Real.sqrt J := by
    apply (sq_le_sq₀ hz (Real.sqrt_nonneg _)).mp
    exact hzJ.trans_eq hsqrt2.symm
  have h1s : 1 ≤ Real.sqrt J := by simpa using Real.sqrt_le_sqrt hJ
  have hsmall : 4*(z+1)*J^2*L^4 ≤ 1920000*J^3 := by
    calc
      4*(z+1)*J^2*L^4 ≤ 4*(2*Real.sqrt J)*J^2*(240000*Real.sqrt J) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right ?_ hJ2) hlog (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith only [hzs,h1s]) (by norm_num)
      _ = _ := by nlinarith only [congrArg (fun x : ℝ => 1920000 * J^2 * x) hsqrt2]
  have hsmall' : 1920000*J^3 ≤ 1920000*W*J^3 := by
    have h := mul_le_mul_of_nonneg_right hW (show 0 ≤ 1920000*J^3 by positivity)
    nlinarith only [h]
  have hN := mul_le_mul_of_nonneg_right hcount (pow_nonneg hL 4)
  nlinarith only [hN,hsel',hsmall,hsmall']

private theorem progressionSieveMass_one_le {P : Finset ℕ} {D : ℕ} (hD : 1 ≤ D)
    (hP : ∀ p ∈ P, 11 ≤ p) : 1 ≤ sieveMass P D progressionSieveG := by
  have hempty : (∅ : Finset ℕ) ∈ sieveIndices P D :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simpa [sieveModulus] using hD⟩
  have h := Finset.single_le_sum
    (f := fun s : Finset ℕ => ∏ p ∈ s, progressionSieveG p)
    (fun s hs => Finset.prod_nonneg fun p hp =>
      (progressionSieveG_bounds (hP p (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1 hp))).1)
    hempty
  simpa [sieveMass,sieveIndices] using h

private theorem progression_sieve_cube_bound (r b J z D : ℕ) :
    let P := progressionSievePrimes r z
    let S := progressionSievedTriples r b J P
    (S.card : ℝ)*(sieveMass P D progressionSieveG)^2 ≤
      (J:ℝ)^3*sieveMass P D progressionSieveG+6*(J:ℝ)^2*(D:ℝ)^4 := by
  dsimp only
  let P := progressionSievePrimes r z
  let S := progressionSievedTriples r b J P
  have hmem {p : ℕ} (hp : p ∈ P) : p.Prime ∧ 11 ≤ p ∧ ¬p∣r := by
    have h := Finset.mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primesLE h.1,h.2⟩
  have hS : S ⊆ sieveCube J := Finset.filter_subset ..
  refine sieveCube_card_mul_mass_sq_le J D P S hS
    (fun p hp => (hmem hp).1) (progressionSieveWeight r b) progressionSieveG ?_ ?_ ?_ ?_
  · intro v hv p hp
    exact ite_eq_left ((Finset.mem_filter.mp hv).2 p hp)
  · exact fun p hp v => progressionSieveWeight_abs (hmem hp).2.1 v
  · intro p np hp
    let _ : Fact p.Prime := ⟨(hmem hp).1⟩
    exact (progressionSieveWeight_moments (r := r) (b := b) (hmem hp).2.1
      (fun hrp => (hmem hp).2.2 ((ZMod.natCast_eq_zero_iff r p).mp hrp))).1
  · intro p np hp
    let _ : Fact p.Prime := ⟨(hmem hp).1⟩
    exact (progressionSieveWeight_moments (r := r) (b := b) (hmem hp).2.1
      (fun hrp => (hmem hp).2.2 ((ZMod.natCast_eq_zero_iff r p).mp hrp))).2

set_option exponentiation.threshold 640 in
/-- Unconditional fourth moment for one reduced progression on the scales used
in the single-average argument. The genuine sieve input is a finite box count. -/
theorem smoothedPrimeSum_fourth_le_selberg :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {r b Y : ℕ}, 0 < r → b < r → Nat.Coprime b r → r ≤ Y →
      (r : ℝ) ≤ 4 * ((Y : ℝ) / r) →
      (∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b Y α‖^4) ≤
        K * ((r : ℝ) / r.totient)^4 * ((Y : ℝ) / r)^3 := by
  let U : ℝ := (3200 * (2:ℝ)^10)^4 * (2*Real.exp (1/2))
  let V : ℝ := (1600*Real.log 2)^4
  refine ⟨8*(7*U+1920000+V), by dsimp [U,V]; positivity, ?_⟩
  intro r b Y hr _ _ hrY hrH
  let J := Y/r+1
  let H : ℝ := (Y:ℝ)/r
  let κ : ℝ := (r:ℝ)/r.totient
  let L := Real.log (2*(Y:ℝ))
  have hY : 1 ≤ Y := hr.trans_le hrY
  obtain ⟨hJtwo,hJH,hYJ⟩ := sieve_class_scales hr hrY hrH
  have hJtwo' : 2 ≤ J := hJtwo
  have hJH' : (J:ℝ) ≤ 2*H := hJH
  have hYJ' : Y ≤ 4*J^2 := hYJ
  have hJ1 : (1:ℝ) ≤ J := by exact_mod_cast (show 1 ≤ J by omega)
  have hJ0 : (0:ℝ) ≤ J := by positivity
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2*Y))
  have hκ : 1 ≤ κ := by
    have ht : (0:ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
    exact (one_le_div ht).2 (by exact_mod_cast Nat.totient_le r)
  have hκ4 : 1 ≤ κ^4 := one_le_pow₀ hκ
  have hW : 0 ≤ κ^4 := by positivity
  have hJpower : (J:ℝ)^3 ≤ 8*H^3 := by
    have h := pow_le_pow_left₀ hJ0 hJH' 3
    nlinarith only [h]
  let N : ℝ := (progressionPrimeTriples r b J).card
  have hcount4 := fourthMoment_le_primeTriples r b Y hY
  change _ ≤ N*L^4 at hcount4
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hbound : N*L^4 ≤ (7*U+1920000+V)*κ^4*(J:ℝ)^3 := by
    by_cases hj : 2^320 ≤ J
    · let k := sieveScaleK J
      let z := sieveScaleZ J
      let D := sieveScaleD J
      let P := progressionSievePrimes r z
      let S := progressionSievedTriples r b J P
      let G := sieveMass P D progressionSieveG
      have h11 {p : ℕ} (hp : p ∈ P) : 11 ≤ p := (Finset.mem_filter.mp hp).2.1
      have hppr {p : ℕ} (hp : p ∈ P) : p.Prime ∧ p ≤ z := by
        have h := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
        exact ⟨h.2,h.1⟩
      have hk : 0 < k := (sieve_scale_bounds hj).1
      have hz : 0 < z := by dsimp [z,sieveScaleZ]; positivity
      have hD : 1 ≤ D := Nat.succ_le_iff.mpr (by dsimp [D,sieveScaleD,z,sieveScaleZ]; positivity)
      have hg : 1 ≤ G := progressionSieveMass_one_le hD (fun _ => h11)
      have hretain := progressionSieveMass_ge_half hk
        (P := P) (fun p hp => ⟨h11 hp,(Finset.mem_filter.mp hp).1⟩)
      have hprod := progressionSieveMass_controls_euler (fun p hp => ⟨(hppr hp).1,h11 hp⟩) hretain
      have heuler := prime_euler_log_le_progression (z := z) hr
      have hlocal : L ≤ 3200 * Real.log ((z:ℝ)+1) := by
        have hlog := sieve_log_two_mul_le hJtwo' hYJ'
        have hzlog := (sieve_scale_bounds hj).2.2.2
        have hzle : Real.log (z:ℝ) ≤ Real.log ((z:ℝ)+1) :=
          Real.log_le_log (Nat.cast_pos.mpr hz) (by linarith)
        change L ≤ 5*Real.log (J:ℝ) at hlog
        change Real.log (J:ℝ) ≤ 640*Real.log (z:ℝ) at hzlog
        linarith only [hlog,hzlog,hzle]
      have hden : L^4 ≤ U*κ^4*G := by
        have hstep := mul_le_mul_of_nonneg_left heuler (show (0:ℝ) ≤ 3200 by norm_num)
        let e := ∏ p ∈ P, (1 - 1/(p:ℝ))⁻¹
        change 3200*Real.log ((z:ℝ)+1) ≤ 3200*((2:ℝ)^10*κ*e) at hstep
        calc L^4 ≤ (3200*((2:ℝ)^10*κ*e))^4 :=
              pow_le_pow_left₀ hL (hlocal.trans hstep) 4
          _ = ((3200*(2:ℝ)^10)^4*κ^4)*e^4 := by ring
          _ ≤ ((3200*(2:ℝ)^10)^4*κ^4)*((2*Real.exp (1/2))*G) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
          _ = _ := by dsimp [U]; ring
      have hcard : N ≤ (S.card:ℝ)+4*((z:ℝ)+1)*(J:ℝ)^2 := by
        dsimp [N,S]
        exact_mod_cast (progressionPrimeTriples_card_le_sieved (J := J) (b := b) (z := z) hr
          (P := P) (fun _ hp => hppr hp))
      have hsel := selberg_fourth_count_arithmetic (Nat.cast_nonneg S.card) hJ1
        (Nat.cast_nonneg z) hg hU hL hκ4 hcard (progression_sieve_cube_bound r b J z D)
        (by exact_mod_cast sieve_scale_pow_four_le hj)
        (by exact_mod_cast (sieve_scale_bounds hj).2.2.1)
        (sieve_log_two_mul_pow_four_le hJtwo' hYJ') hden
      exact hsel.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : 7*U+1920000 ≤ 7*U+1920000+V) hW)
        (by positivity))
    · have hs : L ≤ 1600*Real.log 2 := sieve_log_small_scale hJtwo' hYJ' (lt_of_not_ge hj)
      have hc : N ≤ (J:ℝ)^3 := by
        have hn := Finset.card_le_card
          (show progressionPrimeTriples r b J ⊆ sieveCube J from Finset.filter_subset ..)
        rw [card_sieveCube] at hn
        dsimp [N]
        exact_mod_cast hn
      have hV' : L^4 ≤ V := pow_le_pow_left₀ hL hs 4
      calc N*L^4 ≤ (J:ℝ)^3*V := mul_le_mul hc hV' (by positivity) (by positivity)
        _ = V*1*(J:ℝ)^3 := by ring
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul (by linarith : V ≤ 7*U+1920000+V) hκ4 (by norm_num) (by positivity))
            (by positivity)
  calc _ ≤ N*L^4 := hcount4
    _ ≤ (7*U+1920000+V)*κ^4*(J:ℝ)^3 := hbound
    _ ≤ (7*U+1920000+V)*κ^4*(8*H^3) :=
      mul_le_mul_of_nonneg_left hJpower (by positivity)
    _ = _ := by ring

/-- Single-average log-edge bound with the fourth moment discharged by the
unconditional Selberg sieve. -/
theorem single_average_log_edge_of_smoothedTwist (h : SmoothedTwistEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r : ℕ) (hr : 0 < r) (b₁ : ReducedClass r), 2 ≤ X → r ≤ X →
      singleAvgExceptions X r hr b₁ ≤ C * singleAvgLogEdgeBudget X r :=
  single_average_log_edge_of_fourth h smoothedPrimeSum_fourth_le_selberg

theorem single_average_log_edge_of_dirichletGRH (h : DirichletGRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r : ℕ) (hr : 0 < r) (b₁ : ReducedClass r), 2 ≤ X → r ≤ X →
      singleAvgExceptions X r hr b₁ ≤ C * singleAvgLogEdgeBudget X r :=
  single_average_log_edge_of_smoothedTwist (smoothedTwistEstimate_of_dirichletGRH h)

/-- Density one whenever `X / (φ(r)² log(2X)²)` tends to infinity. -/
theorem single_average_density_one_of_dirichletGRH (h : DirichletGRH)
    (X r : ℕ → ℕ) (hr : ∀ n, 0 < r n) (b₁ : ∀ n, ReducedClass (r n))
    (hX : ∀ n, 2 ≤ X n) (hrX : ∀ n, r n ≤ X n)
    (hK : Tendsto (fun n => singleAvgLogEdgeParameter (X n) (r n)) atTop atTop) :
    Tendsto (fun n => singleAvgExceptions (X n) (r n) (hr n) (b₁ n) / ((X n:ℝ)/r n)) atTop (𝓝 0) :=
  singleAvgDensity_of_logEdgeDyadic
    (single_average_log_edge_dyadic_of_fourth
      (smoothedTwistEstimate_of_dirichletGRH h) smoothedPrimeSum_fourth_le_selberg)
    X r hr b₁ hX hrX hK

/-- The stronger of the log-edge and sharp single-average budgets, with one
uniform constant. -/
theorem single_average_combined_of_dirichletGRH (h : DirichletGRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r : ℕ) (hr : 0 < r) (b₁ : ReducedClass r), 2 ≤ X → r ≤ X →
      singleAvgExceptions X r hr b₁ ≤ C * min (singleAvgLogEdgeBudget X r) (singleAvgSharpBudget X r) := by
  obtain ⟨C₁, hC₁, h₁⟩ := single_average_log_edge_of_dirichletGRH h
  obtain ⟨C₂, hC₂, h₂⟩ := single_average_sharp_of_dirichletGRH h
  refine ⟨max C₁ C₂, hC₁.trans_le (le_max_left _ _), fun X r hr b₁ hX hrX => ?_⟩
  have h₁' := h₁ X r hr b₁ hX hrX
  have h₂' := h₂ X r hr b₁ hX hrX
  have he : 0 ≤ singleAvgExceptions X r hr b₁ := by unfold singleAvgExceptions; positivity
  have hlog := nonneg_of_mul_nonneg_right (he.trans h₁') hC₁
  have hsharp := nonneg_of_mul_nonneg_right (he.trans h₂') hC₂
  rw [mul_min_of_nonneg _ _ (hC₁.trans_le (le_max_left C₁ C₂)).le]
  exact le_min (h₁'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog))
    (h₂'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hsharp))

end FareyGoldbach
