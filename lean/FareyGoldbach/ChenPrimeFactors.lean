import FareyGoldbach.SharpRankin

/-! # Prime factors in the finite Chen inequality -/

namespace FareyGoldbach

/-- Positive integers with at most two prime factors, counted with multiplicity. -/
def IsAlmostPrimeTwo (m : ℕ) : Prop :=
  m = 1 ∨ m.Prime ∨ ∃ u v : ℕ, u.Prime ∧ v.Prime ∧ m = u*v

theorem isAlmostPrimeTwo_iff_primeFactorsList_length_le_two {m : ℕ} (hm : 0<m) :
    IsAlmostPrimeTwo m ↔ m.primeFactorsList.length≤2 := by
  constructor
  · rintro (rfl|hp|⟨u,v,hu,hv,rfl⟩)
    · simp
    · simp [Nat.primeFactorsList_prime hp]
    · rw [(Nat.perm_primeFactorsList_mul hu.ne_zero hv.ne_zero).length_eq,
        Nat.primeFactorsList_prime hu,Nat.primeFactorsList_prime hv]
      simp
  · intro h
    have hp := Nat.prod_primeFactorsList hm.ne'
    rcases hL : m.primeFactorsList with _ | ⟨u,_ | ⟨v, _ | ⟨w,ws⟩⟩⟩
    · exact Or.inl (by simpa [hL] using hp.symm)
    · rw [hL,List.prod_singleton] at hp
      exact Or.inr (Or.inl (hp ▸ Nat.prime_of_mem_primeFactorsList (n:=m) (by simp [hL])))
    · rw [hL] at hp
      exact Or.inr (Or.inr ⟨u,v,Nat.prime_of_mem_primeFactorsList (n:=m) (by simp [hL]),
        Nat.prime_of_mem_primeFactorsList (n:=m) (by simp [hL]),by simpa using hp.symm⟩)
    · simp [hL] at h

private theorem odd_prime_triple_exceeds_floor {N y u v w : ℕ} (hy : N<(y+1)^3)
    (hy3 : 3≤y) (hu : u.Prime) (hv : v.Prime) (hw : w.Prime)
    (hyu : y≤u) (huv : u<v) (hvw : v<w) : N<u*v*w := by
  have ho₁ := hu.odd_iff.mpr (by omega)
  have ho₂ := hv.odd_iff.mpr (by omega)
  have ho₃ := hw.odd_iff.mpr (by omega)
  obtain ⟨a,ha⟩ := ho₁
  obtain ⟨b,hb⟩ := ho₂
  obtain ⟨c,hc⟩ := ho₃
  have hv' : y+2≤v := by omega
  have hw' : y+4≤w := by omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul hyu hv') hw'
  have hp : (y+1)^3≤y*(y+2)*(y+4) := by
    exact_mod_cast (show ((y:ℤ)+1)^3≤(y:ℤ)*((y:ℤ)+2)*((y:ℤ)+4) by
      have H : (3:ℤ)≤y := by exact_mod_cast hy3
      nlinarith only [H,sq_nonneg (y:ℤ)])
  exact hy.trans_le (hp.trans hmul)

/-- A rough squarefree integer is almost prime, has two medium prime factors, or
belongs to the switched three-prime range. The spacing of distinct odd primes
allows the exact floor of the cube root. -/
theorem chen_squarefree_dichotomy {N z y a : ℕ} (hy : N < (y+1)^3) (hy3 : 3≤y)
    (ha1 : 2≤a) (haN : a≤N) (hsq : Squarefree a)
    (hrough : ∀ p∈a.primeFactors, z≤p) :
    a.primeFactorsList.length≤2 ∨
      (∃ q₁∈a.primeFactors, ∃ q₂∈a.primeFactors, q₁≠q₂ ∧ q₁<y ∧ q₂<y) ∨
      ∃ u v w : ℕ, u.Prime ∧ v.Prime ∧ w.Prime ∧ z≤u ∧ u<y ∧ y≤v ∧ v≤w ∧ a=u*v*w := by
  have ha0 : a≠0 := by omega
  have hp := Nat.prod_primeFactorsList ha0
  have hs := (Nat.primeFactorsList_sorted a).pairwise
  have hd := hsq.nodup_primeFactorsList
  rcases hL : a.primeFactorsList with _ | ⟨u,_ | ⟨v, _ | ⟨w,ws⟩⟩⟩
  · simp
  · simp
  · simp
  right
  have hu : u∈a.primeFactorsList := by simp [hL]
  have hv : v∈a.primeFactorsList := by simp [hL]
  have hw : w∈a.primeFactorsList := by simp [hL]
  have huP := Nat.prime_of_mem_primeFactorsList hu
  have hvP := Nat.prime_of_mem_primeFactorsList hv
  have hwP := Nat.prime_of_mem_primeFactorsList hw
  rw [hL] at hs hd hp
  obtain ⟨hsu,ht⟩ := List.pairwise_cons.mp hs
  obtain ⟨hsv,ht'⟩ := List.pairwise_cons.mp ht
  have hsw := (List.pairwise_cons.mp ht').1
  have hne := List.nodup_cons.mp hd
  have hnuv : u≠v := fun he => hne.1 (by simp [he])
  have hnvw : v≠w := fun he => (List.nodup_cons.mp hne.2).1 (by simp [he])
  have huv : u<v := lt_of_le_of_ne (hsu v (by simp)) hnuv
  have hvw : v<w := lt_of_le_of_ne (hsv w (by simp)) hnvw
  by_cases hvl : v<y
  · exact Or.inl ⟨u,Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hu,v,
      Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hv,hnuv,huv.trans hvl,hvl⟩
  · right
    have hyv : y≤v := le_of_not_gt hvl
    have hul : u<y := by
      by_contra hh
      have hlarge := odd_prime_triple_exceeds_floor hy hy3 huP hvP hwP (le_of_not_gt hh) huv hvw
      have hdvd : u*v*w ∣ a := ⟨ws.prod,by
        rw [←hp]; simp only [List.prod_cons]; ac_rfl⟩
      exact hlarge.not_ge ((Nat.le_of_dvd (by omega : 0<a) hdvd).trans haN)
    have hws : ws=[] := by
      cases ws with
      | nil => rfl
      | cons k ks =>
        exfalso
        have hk : k∈a.primeFactorsList := by simp [hL]
        have hwk : w<k := lt_of_le_of_ne (hsw k (by simp))
          (fun he => (List.nodup_cons.mp (List.nodup_cons.mp hne.2).2).1 (by simp [he]))
        have hlarge := odd_prime_triple_exceeds_floor hy hy3 hvP hwP
          (Nat.prime_of_mem_primeFactorsList hk) hyv hvw hwk
        have hdvd : v*w*k ∣ a := ⟨u*ks.prod,by
          rw [←hp]; simp only [List.prod_cons]; ac_rfl⟩
        exact hlarge.not_ge ((Nat.le_of_dvd (by omega : 0<a) hdvd).trans haN)
    exact ⟨u,v,w,huP,hvP,hwP,hrough u (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hu),
      hul,hyv,hvw.le,by simpa [hws,mul_assoc] using hp.symm⟩

end FareyGoldbach
