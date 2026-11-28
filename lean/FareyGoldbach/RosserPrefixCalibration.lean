import FareyGoldbach.LinearSieveWeights

/-! # Comparing descending prime lists with the inclusive prefix test

For p in a finite set s of distinct factors, the prefix ending at p is
precisely the set of q in s with p ≤ q.  Its cardinality is the position
of p in the descending enumeration, counted from one.
-/

open scoped Classical

namespace FareyGoldbach

/-- The cubic Rosser tests written on finite prefixes ordered by their last prime. -/
def rosserPrefixAdmits (upper : Bool) (D m : ℕ) (s : Finset ℕ) : Prop :=
  ∀ p ∈ s, (if upper then ¬ Even ((s.filter (p ≤ ·)).card)
            else Even ((s.filter (p ≤ ·)).card)) →
    m * (s.filter (p ≤ ·)).prod id * p^2 < D

private theorem prefix_admits_insert {p : ℕ} {s : Finset ℕ} (hp : ∀ q ∈ s, q < p)
    (upper : Bool) (D m : ℕ) :
    rosserPrefixAdmits upper D m (insert p s) ↔
      (upper = true → m*p^3 < D) ∧ rosserPrefixAdmits (!upper) D (m*p) s := by
  have hpout : p ∉ s := fun h => (lt_irrefl p) (hp p h)
  have hfirst : (insert p s).filter (p ≤ ·) = {p} := by
    ext q
    simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | hq, hle⟩
      · rfl
      · exact False.elim (not_lt_of_ge hle (hp q hq))
    · rintro rfl
      exact ⟨Or.inl rfl,le_rfl⟩
  have hhead : m*p*p^2 = m*p^3 := by ring
  have htail (q : ℕ) (hq : q ∈ s) :
      (insert p s).filter (q ≤ ·) = insert p (s.filter (q ≤ ·)) := by
    rw [Finset.filter_insert, ite_eq_left (hp q hq).le]
  have hpar (k : ℕ) : (if upper then ¬Even (k+1) else Even (k+1)) ↔
      (if !upper then ¬Even k else Even k) := by
    cases upper <;> simp [Nat.even_add]
  have hcond (q : ℕ) (hq : q ∈ s) :
      (if upper then ¬Even (((insert p s).filter (q ≤ ·)).card)
                else Even (((insert p s).filter (q ≤ ·)).card)) ↔
      (if !upper then ¬Even ((s.filter (q ≤ ·)).card) else Even ((s.filter (q ≤ ·)).card)) := by
    have hnot : p ∉ s.filter (q ≤ ·) := fun h => hpout (Finset.mem_filter.mp h).1
    rw [htail q hq,Finset.card_insert_of_notMem hnot]
    exact hpar _
  have hprod (q : ℕ) (hq : q ∈ s) :
      m * (((insert p s).filter (q ≤ ·)).prod id) * q^2 =
        (m*p) * ((s.filter (q ≤ ·)).prod id) * q^2 := by
    have hnot : p ∉ s.filter (q ≤ ·) := fun h => hpout (Finset.mem_filter.mp h).1
    rw [htail q hq, Finset.prod_insert hnot]
    simp only [id_eq,mul_assoc]
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · rintro rfl
      have h := h p (Finset.mem_insert_self ..)
      simpa [hfirst,hhead] using h
    · intro q hq he
      rw [←hprod q hq]
      exact h q (Finset.mem_insert_of_mem hq) ((hcond q hq).mpr he)
  · rintro ⟨h₁,h₂⟩ q hq hparity
    rcases Finset.mem_insert.mp hq with rfl | hq
    · cases upper <;> simp_all
    · rw [hprod q hq]
      exact h₂ q hq ((hcond q hq).mp hparity)

/-- Evaluation of the recursion using non-strict prime prefixes and a strict level.
This form also applies when the incoming prefix is nontrivial. -/
theorem rosserSubset_eq_prefix_weight (upper : Bool) (D m : ℕ) (s : Finset ℕ) :
    rosserSubset upper D m s =
      (if rosserPrefixAdmits upper D m s then (if Even s.card then (1:ℤ) else -1) else 0) := by
  induction s using Finset.induction_on_max generalizing m upper with
  | empty => simp [rosserSubset,rosserChain,rosserPrefixAdmits]
  | insert p s hp ih =>
    have hnot : p ∉ s := fun h => (lt_irrefl p) (hp p h)
    have hs : rosserSubset upper D m (insert p s) =
      (if upper=true ∧ D≤m*p^3 then 0 else -rosserSubset (!upper) D (m*p) s) := by
      rw [rosserSubset, Finset.sort_insert _ (fun q hq => (hp q hq).le) hnot,rosserChain]
      rfl
    rw [hs,ih, prefix_admits_insert hp, Finset.card_insert_of_notMem hnot]
    by_cases stop : upper=true ∧ D≤m*p^3
    · have hfail : ¬ (upper=true → m*p^3<D) := fun h => (not_lt_of_ge stop.2) (h stop.1)
      simp [stop]
    · have hok : upper=true → m*p^3<D := fun hu => lt_of_not_ge fun h => stop ⟨hu,h⟩
      by_cases had : rosserPrefixAdmits (!upper) D (m*p) s <;>
        by_cases he : Even s.card <;> simp [stop,had,Nat.even_add,he]

end FareyGoldbach