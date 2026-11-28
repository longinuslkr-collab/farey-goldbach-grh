import FareyGoldbach.ShortIntervalExceptions
import FareyGoldbach.SingleAverageAssembly
import FareyGoldbach.TernaryDefinitions

/-! # Removing one prime from a ternary Goldbach target -/

open scoped Classical

namespace FareyGoldbach

private theorem ternary_drop_prime {X r n p : ℕ} (hr : 0<r) (b₁ b₂ b₃ : ReducedClass r)
    (hn : n ∈ Finset.Ioc (X/2) X) (hadm : ternaryAdmissible r b₁.1 b₂.1 b₃.1 n)
    (hbad : ¬ (ternaryRepresentations r b₁.1 b₂.1 b₃.1 n).Nonempty)
    (hp : p ∈ ternaryCandidatePrimes X r b₁.1) :
    X/4 < n-p ∧ n-p ∈ exceptions (shortProgressions hr b₂ b₃) X := by
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hn
  obtain ⟨hpr,hpprime,hpb⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpn,hpx⟩ := Finset.mem_Icc.mp hpr
  have hplen : p ≤ n := by omega
  have hs : X/4 < n-p := by omega
  have hpodd := (hpprime.odd_iff).mpr hpn
  have hm : Even (n-p) := by
    obtain ⟨a,ha⟩ := hadm.1
    obtain ⟨b,hb⟩ := hpodd
    exact ⟨a-b,by omega⟩
  have hpg : p ≡ b₁.1 [MOD r] := by
    change p%r=b₁.1%r
    rwa [Nat.mod_eq_of_lt (mem_coprimeClasses.mp b₁.2).1]
  have hgn : n-p ≡ b₂.1+b₃.1 [MOD r] := by
    apply Nat.ModEq.add_right_cancel' p
    rw [Nat.sub_add_cancel hplen]
    have hg : n ≡ (b₂.1+b₃.1)+b₁.1 [MOD r] := by
      simpa only [Nat.ModEq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hadm.2
    exact hg.trans (hpg.symm.add_left (b₂.1+b₃.1))
  have hzero : (primeRepresentations (shortProgressions hr b₂ b₃) (n-p)).card=0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨⟨q,s⟩,hqs⟩
    obtain ⟨hpair,hqprime,hsprime,he,hqmod,hsmod⟩ := Finset.mem_filter.mp hqs
    obtain ⟨hq,hs'⟩ := Finset.mem_product.mp hpair
    obtain ⟨hql,hqu⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hsl,hsu⟩ := Finset.mem_Icc.mp hs'
    have hqn : q≤n := hqu.trans (Nat.sub_le _ _)
    have hsn : s≤n := hsu.trans (Nat.sub_le _ _)
    apply hbad
    refine ⟨(p,q,s),Finset.mem_filter.mpr ⟨?_,hpprime,hqprime,hsprime,?_,hpb,hqmod,hsmod⟩⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hplen⟩,
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hql,hqn⟩,Finset.mem_Icc.mpr ⟨hsl,hsn⟩⟩⟩
    · change q+s=n-p at he
      change p+q+s=n
      omega
  refine ⟨hs,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,hm,?_,hzero⟩⟩
  exact hgn

private theorem ternary_drop_injective {X r n : ℕ} {b : ℕ}
    (hn : n ∈ Finset.Ioc (X/2) X) :
    Set.InjOn (fun p : ℕ => n-p) (ternaryCandidatePrimes X r b) := by
  intro p hp q hq he
  have hp' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
  have hq' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
  have hn' := (Finset.mem_Ioc.mp hn).1
  change n-p=n-q at he
  omega

/-- Every candidate yields a distinct binary exception at a failed admissible target. -/
theorem ternaryCandidate_card_le_exceptions {X r n : ℕ} (hr : 0<r) (b₁ b₂ b₃ : ReducedClass r)
    (hn : n ∈ Finset.Ioc (X/2) X) (hadm : ternaryAdmissible r b₁.1 b₂.1 b₃.1 n)
    (hbad : ¬ (ternaryRepresentations r b₁.1 b₂.1 b₃.1 n).Nonempty) :
    (ternaryCandidatePrimes X r b₁.1).card ≤ (exceptions (shortProgressions hr b₂ b₃) X).card := by
  rw [← Finset.card_image_of_injOn (ternary_drop_injective (r:=r) (b:=b₁.1) hn)]
  apply Finset.card_le_card
  intro m hm
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm
  exact (ternary_drop_prime hr b₁ b₂ b₃ hn hadm hbad hp).2

theorem ternaryCandidate_card_le_exceptions_of_badBlock {X r : ℕ} (hr : 0<r)
    (b₁ b₂ b₃ : ReducedClass r) (hbad : ¬ ternaryGoodBlock X r b₁.1 b₂.1 b₃.1) :
    (ternaryCandidatePrimes X r b₁.1).card ≤ (exceptions (shortProgressions hr b₂ b₃) X).card := by
  by_contra h
  apply hbad
  intro n hn hadm
  by_contra nc
  exact h (ternaryCandidate_card_le_exceptions hr b₁ b₂ b₃ hn hadm nc)

/-- Three dyadic windows cover the displaced targets. Their starting points
remain comparable to `X`, allowing a single logarithm in the single-average estimate. -/
theorem ternaryCandidate_card_le_block_exceptions {X r : ℕ} (hX : 4≤X) (hr : 0<r)
    (b₁ b₂ b₃ : ReducedClass r) (hbad : ¬ ternaryGoodBlock X r b₁.1 b₂.1 b₃.1) :
    let s := X/4
    let P := shortProgressions hr b₂ b₃
    (ternaryCandidatePrimes X r b₁.1).card ≤
      (shortIntervalExceptions P s s).card + (shortIntervalExceptions P (2*s) (2*s)).card +
        (shortIntervalExceptions P (4*s) (4*s)).card := by
  intro s P
  by_contra hcard
  apply hbad
  intro n hn hadm
  by_contra nc
  let A := shortIntervalExceptions P s s
  let B := shortIntervalExceptions P (2*s) (2*s)
  let C := shortIntervalExceptions P (4*s) (4*s)
  have hsub : (ternaryCandidatePrimes X r b₁.1).image (fun p => n-p) ⊆ A∪B∪C := by
    intro m hm
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hlo,hm⟩ := ternary_drop_prime hr b₁ b₂ b₃ hn hadm nc hp
    obtain ⟨hmrange,he,hcon,hbad'⟩ := Finset.mem_filter.mp hm
    obtain ⟨h1,hmax⟩ := Finset.mem_Icc.mp hmrange
    have hnz (a d : ℕ) (hl : a<n-p) (hh : n-p≤a+d) : n-p ∈ shortIntervalExceptions P a d :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1,hh⟩,he,hcon,hbad'⟩,hl⟩
    by_cases h₂ : n-p≤2*s
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (hnz s s hlo (by omega)))))
    by_cases h₄ : n-p≤4*s
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (hnz (2*s) (2*s) (by omega) (by omega)))))
    · have h₈ : X≤8*s := by dsimp [s]; omega
      exact Finset.mem_union.mpr (Or.inr (hnz (4*s) (4*s) (by omega) (by omega)))
  have h := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn (ternary_drop_injective (r:=r) (b:=b₁.1) hn)] at h
  apply hcard
  exact h.trans ((Finset.card_union_le _ _).trans (by
    have := Finset.card_union_le A B
    change (A∪B).card+C.card≤A.card+B.card+C.card
    omega))

end FareyGoldbach
