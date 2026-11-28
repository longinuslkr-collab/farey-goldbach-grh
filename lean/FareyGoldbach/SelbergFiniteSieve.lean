import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.CastCard
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A finite square upper sieve on three-dimensional boxes

The finite square estimate and the box discrepancy apply to arbitrary real weights.
-/

open scoped BigOperators
open Finset

namespace FareyGoldbach

/-- The square of a sum of local weights majorizes a constant on the sifted set. -/
theorem finite_square_sieve {α ι : Type*} [DecidableEq ι]
    (Ω S : Finset α) (I : Finset ι) (u : ι → α → ℝ) (g : ι → ℝ) (M E : ℝ)
    (hS : S ⊆ Ω) (hsift : ∀ x ∈ S, ∀ d ∈ I, u d x = g d)
    (hgram : ∀ d ∈ I, ∀ e ∈ I, ∑ x ∈ Ω, u d x * u e x ≤
      (if d = e then M * g d else 0) + E) :
    (S.card : ℝ) * (∑ d ∈ I, g d) ^ 2 ≤
      M * (∑ d ∈ I, g d) + (I.card : ℝ) ^ 2 * E := by
  classical
  calc
    _ = ∑ _ ∈ S, (∑ d ∈ I, g d) ^ 2 := by simp
    _ = ∑ x ∈ S, (∑ d ∈ I, u d x) ^ 2 := by
      exact Finset.sum_congr rfl fun x hx ↦ by
        rw [Finset.sum_congr rfl (hsift x hx)]
    _ ≤ ∑ x ∈ Ω, (∑ d ∈ I, u d x) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hS fun x _ _ ↦ sq_nonneg _
    _ = ∑ d ∈ I, ∑ e ∈ I, ∑ x ∈ Ω, u d x * u e x := by
      simp_rw [sq, sum_mul, mul_sum]
      rw [sum_comm]
      exact Finset.sum_congr rfl fun d _ ↦ sum_comm
    _ ≤ ∑ d ∈ I, ∑ e ∈ I, ((if d = e then M * g d else 0) + E) :=
      Finset.sum_le_sum fun d hd ↦ Finset.sum_le_sum fun e he ↦ hgram d hd e he
    _ = _ := by
      simp [Finset.sum_add_distrib, ← Finset.mul_sum, sq, mul_assoc]

/-- Triples of integers in the half-open cube of side length `J`. -/
def sieveCube (J : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range J) ×ˢ ((range J) ×ˢ (range J))

@[simp] theorem card_sieveCube (J : ℕ) : (sieveCube J).card = J ^ 3 := by
  simp [sieveCube, pow_succ, Nat.mul_assoc]

theorem sieveCube_mono {J K : ℕ} (h : J ≤ K) : sieveCube J ⊆ sieveCube K := by
  intro x hx
  simpa [sieveCube] using (show x.1 < K ∧ x.2.1 < K ∧ x.2.2 < K from by
    simp [sieveCube] at hx
    omega)

/-- Coordinatewise reduction modulo `l`. -/
def sieveCubeMod (l : ℕ) (x : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (x.1 % l, x.2.1 % l, x.2.2 % l)

private theorem sum_range_blocks_mod (k l : ℕ) (f : ℕ → ℝ) :
    (∑ x ∈ range (k * l), f (x % l)) = k * ∑ x ∈ range l, f x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, sum_range_add, ih, Nat.cast_succ, add_mul, one_mul]
    congr 1
    exact sum_congr rfl fun x hx ↦ by simp [Nat.add_mod, Nat.mod_eq_of_lt (mem_range.mp hx)]

private theorem sum_sieveCube_blocks (k l : ℕ) (f : ℕ × ℕ × ℕ → ℝ) :
    (∑ x ∈ sieveCube (k * l), f (sieveCubeMod l x)) = (k : ℝ) ^ 3 *
      ∑ x ∈ sieveCube l, f x := by
  unfold sieveCube
  simp only [sum_product, sieveCubeMod]
  have hz (x y : ℕ) : (∑ z ∈ range (k * l), f (x, y, z % l)) =
      k * ∑ z ∈ range l, f (x, y, z) := sum_range_blocks_mod k l (fun z ↦ f (x, y, z))
  have hy (x : ℕ) : (∑ y ∈ range (k * l), ∑ z ∈ range l, f (x, y % l, z)) =
      k * ∑ y ∈ range l, ∑ z ∈ range l, f (x, y, z) :=
    sum_range_blocks_mod k l (fun y ↦ ∑ z ∈ range l, f (x, y, z))
  have hx : (∑ x ∈ range (k * l), ∑ y ∈ range l, ∑ z ∈ range l, f (x % l, y, z)) =
      k * ∑ x ∈ range l, ∑ y ∈ range l, ∑ z ∈ range l, f (x, y, z) :=
    sum_range_blocks_mod k l (fun x ↦ ∑ y ∈ range l, ∑ z ∈ range l, f (x, y, z))
  simp_rw [hz, ← mul_sum, hy, ← mul_sum, hx]
  ring

/-- A bounded function periodic modulo `l` has cube sum within the boundary error
`6 J² l` of its complete-residue mean multiplied by the volume. -/
theorem sum_sieveCube_le_periodic_mean (J l : ℕ) (hl : 0 < l)
    (F : ℕ × ℕ × ℕ → ℝ) (hbound : ∀ x, |F x| ≤ 1)
    (hper : ∀ x, F x = F (sieveCubeMod l x)) :
    (∑ x ∈ sieveCube J, F x) ≤ (J : ℝ)^3 * ((∑ x ∈ sieveCube l, F x) / (l : ℝ)^3)
      + 6 * (J : ℝ)^2 * l := by
  let k := J / l
  let T := k * l
  have hTJ : T ≤ J := Nat.div_mul_le_self _ _
  have hrem : J - T < l := by
    have hm := Nat.mod_add_div J l
    have hr := Nat.mod_lt J hl
    dsimp [T, k]
    rw [Nat.mul_comm l] at hm
    omega
  have hsub := sieveCube_mono hTJ
  have htail : (∑ x ∈ sieveCube J \ sieveCube T, F x) ≤ (J : ℝ)^3 - (T : ℝ)^3 := by
    calc
      _ ≤ ∑ _ ∈ sieveCube J \ sieveCube T, (1 : ℝ) :=
        sum_le_sum fun x _ ↦ (abs_le.mp (hbound x)).2
      _ = _ := by simp [Finset.cast_card_sdiff hsub]
  have hcomplete : (∑ x ∈ sieveCube T, F x) = (k : ℝ)^3 * ∑ x ∈ sieveCube l, F x := by
    calc
      _ = ∑ x ∈ sieveCube T, F (sieveCubeMod l x) := sum_congr rfl fun x _ ↦ hper x
      _ = _ := sum_sieveCube_blocks k l F
  let m := (∑ x ∈ sieveCube l, F x) / (l : ℝ)^3
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hm : -1 ≤ m := by
    apply (le_div_iff₀ (pow_pos hlr 3)).mpr
    calc
      _ = ∑ _ ∈ sieveCube l, (-1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum fun x _ ↦ (abs_le.mp (hbound x)).1
  have hTc : (T : ℝ) = (k : ℝ) * (l : ℝ) := by simp [T]
  have hmain : (k : ℝ)^3 * (∑ x ∈ sieveCube l, F x) = (T : ℝ)^3 * m := by
    rw [hTc]; dsimp [m]; field_simp
  have hTJr : (T : ℝ) ≤ J := by exact_mod_cast hTJ
  have hsmall : (J : ℝ) - T ≤ l := by
    have h : (J : ℝ) ≤ (T : ℝ) + l := by exact_mod_cast (show J ≤ T + l by omega)
    linarith
  have hgap : 0 ≤ (J : ℝ)^3 - T^3 := sub_nonneg.mpr (by gcongr)
  have hvol : (J : ℝ)^3 - T^3 ≤ 3 * (J : ℝ)^2 * l := by
    calc
      _ = ((J : ℝ) - T) * (J^2 + J * T + T^2) := by ring
      _ ≤ (l : ℝ) * ((J : ℝ)^2 + J * J + J^2) := by gcongr
      _ = _ := by ring
  have hs := sum_sdiff hsub (f := F)
  change _ ≤ (J : ℝ)^3 * m + _
  rw [hcomplete, hmain] at hs
  nlinarith [mul_nonneg hgap (show 0 ≤ m + 1 by linarith)]

private theorem sieve_sum_range_natCast (l : ℕ) [NeZero l] (f : ZMod l → ℝ) :
    (∑ n ∈ range l, f (n : ZMod l)) = ∑ a, f a := by
  apply sum_bij (s := range l) (t := univ) (fun (n : ℕ) _ ↦ (n : ZMod l))
  · simp
  · intro a ha b hb hab
    simpa [ZMod.val_natCast_of_lt (mem_range.mp ha),
      ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
  · intro b _
    exact ⟨b.val, mem_range.mpr b.val_lt, ZMod.natCast_zmod_val b⟩
  · simp

private theorem sieve_crt_range_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] (hc : Pairwise (fun i j ↦ (m i).Coprime (m j)))
    (f : ∀ i, ZMod (m i) → ℝ) :
    (∑ n ∈ range (∏ i, m i), ∏ i, f i (n : ZMod (m i))) = ∏ i, ∑ a, f i a := by
  classical
  let l := ∏ i, m i
  let : NeZero l := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ ↦ NeZero.ne (m i))⟩
  let e := (ZMod.prodEquivPi m hc).toEquiv
  let f' := fun x : ∀ i, ZMod (m i) ↦ ∏ i, f i (x i)
  calc
    _ = ∑ n ∈ range l, f' (e (n : ZMod l)) := by
      apply sum_congr rfl; intro n _
      simp [f', e]
    _ = ∑ a : ZMod l, f' (e a) := sieve_sum_range_natCast l (fun a ↦ f' (e a))
    _ = ∑ x, f' x := e.sum_comp _
    _ = _ := (Fintype.prod_sum f).symm

/-- Three nested applications of CRT give the complete (unnormalized) cube moment. -/
theorem sieve_crt_cube_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] (hc : Pairwise (fun i j ↦ (m i).Coprime (m j)))
    (f : ∀ i, ZMod (m i) × ZMod (m i) × ZMod (m i) → ℝ) :
    (∑ v ∈ sieveCube (∏ i, m i),
      ∏ i, f i ((v.1 : ZMod (m i)), (v.2.1 : ZMod (m i)), (v.2.2 : ZMod (m i)))) =
      ∏ i, ∑ a, ∑ b, ∑ c, f i (a, b, c) := by
  simp only [sieveCube, sum_product]
  let J := ∏ i, m i
  calc
    _ = ∑ x ∈ range J, ∑ y ∈ range J, ∏ i, ∑ z, f i (x, y, z) := by
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intro y _
      exact sieve_crt_range_sum m hc (fun i z ↦ f i (x, y, z))
    _ = ∑ x ∈ range J, ∏ i, ∑ y, ∑ z, f i (x, y, z) := by
      apply sum_congr rfl; intro x _
      exact sieve_crt_range_sum m hc (fun i y ↦ ∑ z, f i (x, y, z))
    _ = _ := sieve_crt_range_sum m hc (fun i x ↦ ∑ y, ∑ z, f i (x, y, z))

/-- The squarefree period indexed by a finite set of primes. -/
def sieveModulus (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

/-- A tensor product of local weights evaluated at an integral triple. -/
noncomputable def sieveProductWeight
    (u : ∀ p, ZMod p × ZMod p × ZMod p → ℝ) (s : Finset ℕ) (v : ℕ × ℕ × ℕ) : ℝ :=
  ∏ p ∈ s, u p (v.1, v.2.1, v.2.2)

/-- The two products have complete Gram matrix zero off the diagonal. The period is
the product over the union, which avoids introducing prime factorizations of `d,e`. -/
theorem sieve_complete_gram (s t : Finset ℕ) (hpr : ∀ p ∈ s ∪ t, p.Prime)
    (u : ∀ p, ZMod p × ZMod p × ZMod p → ℝ) (g : ℕ → ℝ)
    (hz : ∀ p [NeZero p], p ∈ s ∪ t → ∑ v, u p v = 0)
    (hsq : ∀ p [NeZero p], p ∈ s ∪ t → ∑ v, (u p v)^2 = (p : ℝ)^3 * g p) :
    (∑ v ∈ sieveCube (sieveModulus (s ∪ t)), sieveProductWeight u s v * sieveProductWeight u t v) =
      if s = t then (sieveModulus (s ∪ t) : ℝ)^3 * ∏ p ∈ s, g p else 0 := by
  classical
  let U := s ∪ t
  let m : U → ℕ := fun p ↦ p.val
  let _ (p : U) : NeZero (m p) := ⟨(hpr p p.property).ne_zero⟩
  have hcop : Pairwise (fun i j : U ↦ (m i).Coprime (m j)) := by
    intro i j hij
    exact (Nat.coprime_primes (hpr i i.property) (hpr j j.property)).mpr
      (fun h ↦ hij (Subtype.ext h))
  let f (p : U) (v : ZMod (m p) × ZMod (m p) × ZMod (m p)) :=
    (if p.val ∈ s then u p.val v else 1) * (if p.val ∈ t then u p.val v else 1)
  have hmod : (∏ p : U, m p) = sieveModulus (s ∪ t) := prod_coe_sort U id
  have hrestrict (a : Finset ℕ) (ha : a ⊆ U) (F : ℕ → ℝ) :
      (∏ p : U, if p.val ∈ a then F p else 1) = ∏ p ∈ a, F p := by
    rw [prod_coe_sort U (fun p ↦ if p ∈ a then F p else 1), prod_ite_mem,
      inter_eq_right.mpr ha]
  have hfactor : (∑ v ∈ sieveCube (sieveModulus (s ∪ t)),
      sieveProductWeight u s v * sieveProductWeight u t v) =
      ∏ p : U, ∑ v, f p v := by
    rw [← hmod]
    calc
      _ = ∑ v ∈ sieveCube (∏ p : U, m p), ∏ p : U, f p (v.1, v.2.1, v.2.2) := by
        apply sum_congr rfl; intro v _
        simp only [f, prod_mul_distrib]
        exact congrArg₂ (· * ·) (hrestrict s subset_union_left
          (fun p ↦ u p (v.1, v.2.1, v.2.2))).symm (hrestrict t subset_union_right
          (fun p ↦ u p (v.1, v.2.1, v.2.2))).symm
      _ = _ := by simpa [Fintype.sum_prod_type] using sieve_crt_cube_sum m hcop f
  rw [hfactor]
  by_cases hst : s = t
  · subst t
    rw [ite_eq_left rfl]
    calc
      _ = ∏ p : U, (p.val : ℝ)^3 * g p := by
        apply prod_congr rfl
        intro p _
        have hp : p.val ∈ s := by simpa [U] using p.property
        simpa [f, hp, sq] using hsq p.val p.property
      _ = _ := by
        rw [prod_mul_distrib, prod_coe_sort U (fun p : ℕ ↦ (p : ℝ)^3), prod_coe_sort U g]
        simp [U, sieveModulus, ← prod_pow]
  · rw [ite_eq_right hst]
    obtain ⟨p, hp⟩ : ∃ p, (p ∈ s ∧ p ∉ t) ∨ (p ∈ t ∧ p ∉ s) := by
      by_contra hn
      apply hst
      ext p
      constructor
      · intro h
        by_contra h'
        exact hn ⟨p, Or.inl ⟨h, h'⟩⟩
      · intro h
        by_contra h'
        exact hn ⟨p, Or.inr ⟨h, h'⟩⟩
    have hpU : p ∈ U := hp.elim (fun h ↦ mem_union_left _ h.1) (fun h ↦ mem_union_right _ h.1)
    let i : U := ⟨p, hpU⟩
    apply prod_eq_zero (mem_univ i)
    have hi : ∑ v, u (m i) v = 0 := hz (m i) i.property
    rcases hp with hp | hp
    · simpa [f, i, m, hp.1, hp.2] using hi
    · simpa [f, i, m, hp.1, hp.2] using hi

/-- The allowed finite subsets are indexed injectively by their squarefree product. -/
def sieveIndices (P : Finset ℕ) (D : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter fun s ↦ sieveModulus s ≤ D

@[simp] theorem mem_sieveIndices {P s : Finset ℕ} {D : ℕ} :
    s ∈ sieveIndices P D ↔ s ⊆ P ∧ sieveModulus s ≤ D := by simp [sieveIndices]

theorem card_sieveIndices_le (P : Finset ℕ) (D : ℕ) (hpr : ∀ p ∈ P, p.Prime) :
    (sieveIndices P D).card ≤ D := by
  have hprime {s} (hs : s ∈ sieveIndices P D) (p) (hp : p ∈ s) :=
    hpr p ((mem_sieveIndices.mp hs).1 hp)
  calc
    _ ≤ (Icc 1 D).card := by
      apply card_le_card_of_injOn sieveModulus
      · intro s hs
        exact mem_Icc.mpr ⟨Finset.prod_pos (fun p hp ↦ (hprime hs p hp).pos),
          (mem_sieveIndices.mp hs).2⟩
      · intro s hs t ht hst
        simpa only [sieveModulus, Nat.primeFactors_prod (hprime hs),
          Nat.primeFactors_prod (hprime ht)] using congrArg Nat.primeFactors hst
    _ = _ := by simp

private theorem sieveProductWeight_abs_le (u : ∀ p, ZMod p × ZMod p × ZMod p → ℝ)
    (s : Finset ℕ) (hu : ∀ p ∈ s, ∀ x, |u p x| ≤ 1) (v : ℕ × ℕ × ℕ) :
    |sieveProductWeight u s v| ≤ 1 := by
  rw [sieveProductWeight, Finset.abs_prod]
  exact prod_le_one₀ (fun _ _ ↦ abs_nonneg _) (fun p hp ↦ hu p hp _)

private theorem sieveProductWeight_periodic (u : ∀ p, ZMod p × ZMod p × ZMod p → ℝ)
    {s : Finset ℕ} {l : ℕ} (hdvd : ∀ p ∈ s, p ∣ l) (v : ℕ × ℕ × ℕ) :
    sieveProductWeight u s v = sieveProductWeight u s (sieveCubeMod l v) := by
  apply prod_congr rfl; intro p hp
  have h (x : ℕ) : ((x % l : ℕ) : ZMod p) = x := by
    rw [← ZMod.natCast_mod (x % l) p, Nat.mod_mod_of_dvd x (hdvd p hp), ZMod.natCast_mod]
  simp [sieveCubeMod, h]

/-- The Gram bound for two truncated products on an incomplete cube. -/
theorem sieveCube_gram_le (J D : ℕ) (P s t : Finset ℕ)
    (hpr : ∀ p ∈ P, p.Prime) (hs : s ∈ sieveIndices P D) (ht : t ∈ sieveIndices P D)
    (u : ∀ p, ZMod p × ZMod p × ZMod p → ℝ) (g : ℕ → ℝ)
    (hu : ∀ p ∈ P, ∀ x, |u p x| ≤ 1)
    (hz : ∀ p [NeZero p], p ∈ P → ∑ v, u p v = 0)
    (hsq : ∀ p [NeZero p], p ∈ P → ∑ v, (u p v)^2 = (p : ℝ)^3 * g p) :
    (∑ v ∈ sieveCube J, sieveProductWeight u s v * sieveProductWeight u t v) ≤
      (if s = t then (J : ℝ)^3 * ∏ p ∈ s, g p else 0) + 6 * (J : ℝ)^2 * D^2 := by
  have hsP := (mem_sieveIndices.mp hs).1
  have htP := (mem_sieveIndices.mp ht).1
  have hUP : s ∪ t ⊆ P := union_subset hsP htP
  let l := sieveModulus (s ∪ t)
  have hl : 0 < l := prod_pos fun p hp ↦ (hpr p (hUP hp)).pos
  have hI : 0 < sieveModulus (s ∩ t) :=
    prod_pos fun p hp ↦ (hpr p (hsP (mem_inter.mp hp).1)).pos
  have hlD : l ≤ D^2 := calc
    _ ≤ l * sieveModulus (s ∩ t) := Nat.le_mul_of_pos_right _ hI
    _ = sieveModulus s * sieveModulus t := prod_union_inter
    _ ≤ _ := by simpa [sq] using Nat.mul_le_mul (mem_sieveIndices.mp hs).2 (mem_sieveIndices.mp ht).2
  have hdvd (p) (hp : p ∈ s ∪ t) : p ∣ l := dvd_prod_of_mem id hp
  have hgram := sieve_complete_gram s t (fun p hp ↦ hpr p (hUP hp)) u g
    (fun p _ hp ↦ hz p (hUP hp)) (fun p _ hp ↦ hsq p (hUP hp))
  let F := fun v ↦ sieveProductWeight u s v * sieveProductWeight u t v
  have hb := sum_sieveCube_le_periodic_mean J l hl F (fun v ↦ by
    dsimp [F]; rw [abs_mul]
    calc
      _ ≤ 1 * |sieveProductWeight u t v| := mul_le_mul_of_nonneg_right
        (sieveProductWeight_abs_le _ _ (fun p hp ↦ hu p (hsP hp)) v) (abs_nonneg _)
      _ ≤ 1 := by simpa using sieveProductWeight_abs_le u t (fun p hp ↦ hu p (htP hp)) v)
    (fun v ↦ congrArg₂ (· * ·) (sieveProductWeight_periodic u
      (fun p hp ↦ hdvd p (mem_union_left _ hp)) v) (sieveProductWeight_periodic u
      (fun p hp ↦ hdvd p (mem_union_right _ hp)) v))
  have he : 6 * (J : ℝ)^2 * l ≤ 6 * (J : ℝ)^2 * D^2 := by gcongr; exact_mod_cast hlD
  change (∑ v ∈ sieveCube l, F v) = _ at hgram
  rw [hgram] at hb
  have hlr : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  split_ifs at hb ⊢ with h
  · change _ ≤ (J : ℝ)^3 * (((l : ℝ)^3 * _) / (l : ℝ)^3) + _ at hb
    field_simp [hlr] at hb
    linarith
  · simp only [zero_div, mul_zero, zero_add] at hb ⊢
    exact hb.trans he

/-- Truncated mass of the finite sieve. -/
noncomputable def sieveMass (P : Finset ℕ) (D : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ s ∈ sieveIndices P D, ∏ p ∈ s, g p

/-- Finite upper sieve for a sifted subset of a cube. -/
theorem sieveCube_card_mul_mass_sq_le (J D : ℕ) (P : Finset ℕ)
    (S : Finset (ℕ × ℕ × ℕ)) (hS : S ⊆ sieveCube J) (hpr : ∀ p ∈ P, p.Prime)
    (u : ∀ p, ZMod p × ZMod p × ZMod p → ℝ) (g : ℕ → ℝ)
    (hsift : ∀ v ∈ S, ∀ p ∈ P, u p (v.1, v.2.1, v.2.2) = g p)
    (hu : ∀ p ∈ P, ∀ x, |u p x| ≤ 1)
    (hz : ∀ p [NeZero p], p ∈ P → ∑ v, u p v = 0)
    (hsq : ∀ p [NeZero p], p ∈ P → ∑ v, (u p v)^2 = (p : ℝ)^3 * g p) :
    (S.card : ℝ) * (sieveMass P D g)^2 ≤
      (J : ℝ)^3 * sieveMass P D g + 6 * (J : ℝ)^2 * D^4 := by
  apply (finite_square_sieve (sieveCube J) S (sieveIndices P D) (sieveProductWeight u)
    (fun s ↦ ∏ p ∈ s, g p) ((J : ℝ)^3) (6 * (J : ℝ)^2 * D^2) hS
    (fun v hv s hs ↦ prod_congr rfl fun p hp ↦ hsift v hv p ((mem_sieveIndices.mp hs).1 hp))
    (fun s hs t ht ↦ sieveCube_gram_le J D P s t hpr hs ht u g hu hz hsq)).trans
  apply add_le_add (le_refl _)
  have hcard : ((sieveIndices P D).card : ℝ) ≤ D := by exact_mod_cast card_sieveIndices_le P D hpr
  calc
    _ ≤ (D : ℝ)^2 * (6 * (J : ℝ)^2 * D^2) := by gcongr
    _ = _ := by ring

end FareyGoldbach
