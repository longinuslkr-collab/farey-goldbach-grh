import FareyGoldbach.ChenSwitching

/-! # Rosser weights for the linear sieve

Primes are read in descending order. At a checked stage the prefix product `m`
times the cube of the next prime must be strictly below `D`. The upper sieve
checks odd stages and the lower sieve checks even stages.
-/

namespace FareyGoldbach

open scoped Classical

/-- The signed prefix recursion. The Boolean is true when the next stage is checked. -/
def rosserChain (upper : Bool) (D m : ℕ) : List ℕ → ℤ
  | [] => 1
  | p :: ps => if upper=true ∧ D≤m*p^3 then 0 else -rosserChain (!upper) D (m*p) ps

def rosserSubset (upper : Bool) (D m : ℕ) (s : Finset ℕ) : ℤ :=
  rosserChain upper D m (s.sort (·≥·))

/-- Integer-indexed weights at level `D`, supported on squarefree `d<D`. -/
noncomputable def rosserWeight (upper : Bool) (D d : ℕ) : ℤ :=
  if d<D ∧ Squarefree d then rosserSubset upper D 1 d.primeFactors else 0

theorem rosserWeight_zero_of_level {D d : ℕ} (hd : D≤d) (upper : Bool) :
    rosserWeight upper D d=0 := by simp [rosserWeight,not_lt.mpr hd]

theorem rosserWeight_zero_of_not_squarefree {D d : ℕ} (hd : ¬Squarefree d) (upper : Bool) :
    rosserWeight upper D d=0 := by simp [rosserWeight,hd]

theorem rosserWeight_one {D : ℕ} (hD : 1<D) (upper : Bool) : rosserWeight upper D 1=1 := by
  simp [rosserWeight,hD,rosserSubset,rosserChain]

private theorem chain_sign (L : List ℕ) (D m : ℕ) (upper : Bool) :
    rosserChain upper D m L=0 ∨ rosserChain upper D m L=(-1:ℤ)^L.length := by
  induction L generalizing upper m with
  | nil => simp [rosserChain]
  | cons p l ih =>
    rw [rosserChain]
    split
    · exact Or.inl rfl
    · rcases ih (m*p) (!upper) with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simp [h,pow_succ])

theorem abs_rosserWeight_le_one (upper : Bool) (D d : ℕ) : |rosserWeight upper D d|≤1 := by
  unfold rosserWeight rosserSubset
  split
  · rcases chain_sign (d.primeFactors.sort (·≥·)) D 1 upper with h | h <;> simp [h,abs_pow]
  · norm_num

/-- Every retained divisor has exactly its Möbius sign. -/
theorem rosserWeight_eq_zero_or_moebius (upper : Bool) (D d : ℕ) :
    rosserWeight upper D d=0 ∨ rosserWeight upper D d=ArithmeticFunction.moebius d := by
  unfold rosserWeight
  split
  next h =>
    obtain hs | hs := chain_sign (d.primeFactors.sort (·≥·)) D 1 upper
    · exact Or.inl hs
    · right
      rw [rosserSubset,hs,Finset.length_sort,ArithmeticFunction.moebius_apply_of_squarefree h.2]
      congr 1
      exact (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree h.2.ne_zero).mpr h.2
  next => exact Or.inl rfl

private theorem chain_level (l : List ℕ) (D m : ℕ) (upper : Bool)
    (hs : l.Pairwise (·≥·)) (hp : ∀ p ∈ l, 1≤p) (hm : m<D)
    (hfree : upper=false → ∀ p∈l, m*p<D) (hne : rosserChain upper D m l ≠ 0) :
    m*l.prod<D := by
  induction l generalizing m upper with
  | nil => simpa using hm
  | cons p l ih =>
    obtain ⟨hmax,hst⟩ := List.pairwise_cons.mp hs
    have hpt : 1≤p := hp p (by simp)
    have hpos : ∀ q∈l, 1≤q := fun q hq ↦ hp q (List.mem_cons_of_mem p hq)
    have hchecked : ¬(upper=true ∧ D≤m*p^3) := by
      intro hh
      exact hne (by simp [rosserChain,hh])
    have hchild : rosserChain (!upper) D (m*p) l ≠ 0 := by
      intro hh
      exact hne (by simp [rosserChain,hchecked,hh])
    have hp2 : p*p≤p^3 := by
      calc p*p ≤ (p*p)*p := Nat.le_mul_of_pos_right _ hpt
           _ = _ := by ring
    have hpp : p≤p^3 := (Nat.le_mul_of_pos_right _ hpt).trans hp2
    have hmp : m*p<D := by
      cases upper with
      | false => exact hfree rfl p (by simp)
      | true =>
        exact (Nat.mul_le_mul_left m hpp).trans_lt (lt_of_not_ge (fun h ↦ hchecked ⟨rfl,h⟩))
    have hnext : (!upper)=false → ∀ q∈l, (m*p)*q<D := by
      intro hu q hq
      have htrue : upper=true := by cases upper <;> simp_all
      have hb : m*p^3<D := lt_of_not_ge (fun h ↦ hchecked ⟨htrue,h⟩)
      calc (m*p)*q = m*(p*q) := Nat.mul_assoc .. 
           _ ≤ m*(p*p) := Nat.mul_le_mul_left m (Nat.mul_le_mul_left p (hmax q hq))
           _ ≤ m*p^3 := Nat.mul_le_mul_left m hp2
           _ < D := hb
    simpa only [List.prod_cons,Nat.mul_assoc] using ih (m*p) (!upper) hst hpos hmp hnext hchild

private theorem subset_level {D : ℕ} (upper : Bool) (s : Finset ℕ) (hD : 1<D)
    (hp : ∀p∈s, p.Prime) (hbound : ∀p∈s, p<D) (hne : rosserSubset upper D 1 s≠0) :
    (∏ p ∈ s,p)<D := by
  let l := s.sort (·≥·)
  have hs : l.Pairwise (·≥·) := s.pairwise_sort _
  have hl (p : ℕ) : p∈l ↔ p∈s := Finset.mem_sort _
  have h := chain_level l D 1 upper hs (fun p h ↦ (hp p ((hl p).mp h)).pos) hD
    (fun _ p h ↦ by simpa using hbound p ((hl p).mp h)) hne
  have hprod : l.prod=∏ p∈s,p := by
    change (s.sort (·≥·)).prod=_
    rw [← Multiset.prod_coe,Finset.sort_eq]
    exact Finset.prod_val s
  simpa only [hprod,one_mul] using h

/-- The subset-indexed Rosser density sum, with the incoming prefix product `m`. -/
noncomputable def rosserPacket (upper : Bool) (D m : ℕ) (P : Finset ℕ) (g : ℕ→ℝ) : ℝ :=
  ∑ s ∈ P.powerset, (rosserSubset upper D m s:ℝ)*(∏ p∈s, g p)

theorem rosserPacket_insert (upper : Bool) (D m p : ℕ) (P : Finset ℕ) (g : ℕ→ℝ)
    (hp : ∀ q∈P, q<p) :
    rosserPacket upper D m (insert p P) g =
      rosserPacket upper D m P g -
      (if upper=true ∧ D≤m*p^3 then 0 else g p * rosserPacket (!upper) D (m*p) P g) := by
  classical
  have hpP : p∉P := fun h ↦ (lt_irrefl p) (hp p h)
  unfold rosserPacket
  rw [Finset.sum_powerset_insert hpP]
  by_cases hb : upper=true ∧ D≤m*p^3
  · rw [ite_eq_left hb,sub_zero]
    apply add_eq_left.mpr
    apply Finset.sum_eq_zero
    intro s hs
    have hsub := Finset.mem_powerset.mp hs
    have hps : p∉s := fun h ↦ hpP (hsub h)
    rw [rosserSubset,Finset.sort_insert _ (fun q hq ↦ (hp q (hsub hq)).le) hps]
    simp [rosserChain,hb]
  · rw [ite_eq_right hb,Finset.mul_sum,sub_eq_add_neg,← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    have hsub := Finset.mem_powerset.mp hs
    have hps : p∉s := fun h ↦ hpP (hsub h)
    rw [rosserSubset,Finset.sort_insert _ (fun q hq ↦ (hp q (hsub hq)).le) hps,
      rosserChain,ite_eq_right hb,Finset.prod_insert hps, Int.cast_neg]
    unfold rosserSubset
    ring

/-- The fundamental pointwise sandwich, valid for any local factors in `[0,1]`. -/
theorem rosser_packet_bounds (D m : ℕ) (P : Finset ℕ) (g : ℕ→ℝ)
    (hg : ∀p∈P, 0≤g p ∧ g p≤1) :
    rosserPacket false D m P g ≤ ∏ p∈P,(1-g p) ∧
      (∏ p∈P,(1-g p)) ≤ rosserPacket true D m P g := by
  classical
  induction P using Finset.induction_on_max generalizing m with
  | empty => simp [rosserPacket,rosserSubset,rosserChain]
  | insert p P hp ih =>
    have htail : ∀q∈P,0≤g q ∧ g q≤1 := fun q hq ↦ hg q (Finset.mem_insert_of_mem hq)
    have hgp := hg p (Finset.mem_insert_self ..)
    have hn : p∉P := fun h ↦ (lt_irrefl p) (hp p h)
    have hV : 0≤∏ q∈P,(1-g q) := Finset.prod_nonneg fun q hq ↦ sub_nonneg.mpr (htail q hq).2
    obtain ⟨hL,hU⟩ := ih m htail
    obtain ⟨hLC,hUC⟩ := ih (m*p) htail
    rw [rosserPacket_insert false D m p P g hp,rosserPacket_insert true D m p P g hp,Finset.prod_insert hn]
    simp only [Bool.false_eq_true,false_and,ite_false,Bool.not_false,Bool.not_true,true_and]
    constructor
    · nlinarith only [hL,mul_le_mul_of_nonneg_left hUC hgp.1]
    · split
      · nlinarith only [hU,mul_nonneg hgp.1 hV]
      · nlinarith only [hU,mul_le_mul_of_nonneg_left hLC hgp.1]

theorem rosserPacket_eq_divisor_sum (upper : Bool) {D P : ℕ} (hD : 1<D) (hP : Squarefree P)
    (hbound : ∀p∈P.primeFactors, p<D) (g : ℕ→ℝ) :
    rosserPacket upper D 1 P.primeFactors g =
      ∑ d ∈ P.divisors, (rosserWeight upper D d:ℝ)*(∏ p∈d.primeFactors,g p) := by
  classical
  let J (s : Finset ℕ) := ∏ p∈s,p
  have hfac (s : Finset ℕ) (hs : s∈P.primeFactors.powerset) : (J s).primeFactors=s :=
    Nat.primeFactors_prod (fun p hp ↦ Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hs hp))
  have hdiv (s : Finset ℕ) (hs : s∈P.primeFactors.powerset) : J s∣P := by
    have hh := Finset.prod_dvd_prod_of_subset s P.primeFactors id (Finset.mem_powerset.mp hs)
    exact hh.trans (Nat.prod_primeFactors_dvd P)
  unfold rosserPacket
  apply Finset.sum_bij' (fun s _ ↦ J s) (fun d _ ↦ d.primeFactors)
  · intro s hs
    exact Nat.mem_divisors.mpr ⟨hdiv s hs,hP.ne_zero⟩
  · intro d hd
    exact Finset.mem_powerset.mpr (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hP.ne_zero)
  · exact hfac
  · intro d hd
    exact Nat.prod_primeFactors_of_squarefree (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))
  · intro s hs
    rw [rosserWeight,hfac s hs]
    have hsq := hP.squarefree_of_dvd (hdiv s hs)
    by_cases hh : J s<D
    · simp [hh,hsq]
    · have hz : rosserSubset upper D 1 s=0 := by
        by_contra hne
        exact hh (subset_level upper s hD
          (fun p hp ↦ Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hs hp))
          (fun p hp ↦ hbound p (Finset.mem_powerset.mp hs hp)) hne)
      simp [hh,hz]

/-- The unconditional finite Euler-product comparison for the divisor-indexed weights. -/
theorem rosser_weighted_bounds {D P : ℕ} (hD : 1<D) (hP : Squarefree P)
    (hbound : ∀p∈P.primeFactors, p<D) (g : ℕ→ℝ) (hg : ∀p∈P.primeFactors,0≤g p ∧ g p≤1) :
    (∑ d ∈ P.divisors,(rosserWeight false D d:ℝ)*(∏ p∈d.primeFactors,g p)) ≤
      ∏ p∈P.primeFactors,(1-g p) ∧
    (∏ p∈P.primeFactors,(1-g p)) ≤
      ∑ d ∈ P.divisors,(rosserWeight true D d:ℝ)*(∏ p∈d.primeFactors,g p) := by
  simpa only [rosserPacket_eq_divisor_sum false hD hP hbound,rosserPacket_eq_divisor_sum true hD hP hbound]
    using rosser_packet_bounds D 1 P.primeFactors g hg

/-- At an integer, the two divisor sums bound the coprimality indicator. -/
theorem rosser_divisor_bounds {P D n : ℕ} (hP : Squarefree P) (hD : 1<D)
    (hprime : ∀p∈P.primeFactors,p<D) :
    (∑ d ∈ P.divisors.filter (·∣n),rosserWeight false D d) ≤ (if n.Coprime P then (1:ℤ) else 0) ∧
      (if n.Coprime P then (1:ℤ) else 0) ≤ ∑ d ∈ P.divisors.filter (·∣n),rosserWeight true D d := by
  classical
  let M := n.gcd P
  have hMP : M∣P := Nat.gcd_dvd_right .. 
  have hM := hP.squarefree_of_dvd hMP
  have hset : M.divisors=P.divisors.filter (·∣n) := by
    ext d
    simp only [Nat.mem_divisors,Finset.mem_filter]
    change (d∣n.gcd P ∧ M≠0) ↔ (d∣P ∧ P≠0) ∧ d∣n
    rw [Nat.dvd_gcd_iff]
    exact ⟨fun h ↦ ⟨⟨h.1.2,hP.ne_zero⟩,h.1.1⟩,fun h ↦ ⟨⟨h.2,h.1.1⟩,hM.ne_zero⟩⟩
  have h := rosser_weighted_bounds hD hM (fun p hp ↦ hprime p (Nat.primeFactors_mono hMP hP.ne_zero hp))
    (fun _ ↦ (1:ℝ)) (fun _ _ ↦ ⟨zero_le_one,le_rfl⟩)
  rw [hset] at h
  simp only [Finset.prod_const_one,mul_one,sub_self,Finset.prod_const] at h
  by_cases hcop : n.Coprime P
  · have hh : M=1 := hcop
    simp only [hh,Nat.primeFactors_one,Finset.card_empty,pow_zero] at h
    simp only [ite_eq_left hcop]
    exact_mod_cast h
  · have hn : M.primeFactors.Nonempty := Finset.nonempty_iff_ne_empty.mpr
        (fun he ↦ (Nat.primeFactors_eq_empty.mp he).elim hM.ne_zero (fun h₁ ↦ hcop h₁))
    simp only [zero_pow hn.card_pos.ne',ite_eq_right hcop] at h ⊢
    exact_mod_cast h

end FareyGoldbach
