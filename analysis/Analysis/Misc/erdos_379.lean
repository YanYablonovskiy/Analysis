import Mathlib

/-! Formalizing a proof of Erdos problem \#379, arising from conversations between Stijn Cambie, Vjeko Kovac, and Terry Tao.  See the discussion at https://www.erdosproblems.com/forum/thread/379 -/

open Nat

theorem binom_eq {n k:ℕ} (hk: 1 ≤ k) (hn: k ≤ n) : (n.choose k) * k = ((n-1).choose (k-1)) * n := by
  symm; rw [←choose_symm]; nth_rewrite 2 [←choose_symm]
  convert choose_mul_succ_eq (n-1) ((n-1)-(k-1)) using 3
  all_goals omega

theorem binom_eq_2 {n k:ℕ} (hk: 2 ≤ k) (hn: k ≤ n) : (n.choose k) * k * (k-1) = ((n-2).choose (k-2)) * (n-1) * n := calc
  _ = ((n-1).choose (k-1)) * n * (k-1) := by rw [binom_eq] <;> omega
  _ = ((n-1).choose (k-1)) * (k-1) * n := by ring
  _ = _ := by
    rw [binom_eq]; congr 2
    all_goals omega

theorem lemma_1 {n k p a b:ℕ} (hk: 1 ≤ k) (hn: k ≤ n)
 (hp: p.Prime) (h1: p^(a+b+1) ∣ n) : p^(a+1) ∣ n.choose k ∨ p^(b+1) ∣ k := by
  replace h1 := h1.trans (n.dvd_mul_left ((n-1).choose (k-1)))
  rw [←binom_eq hk hn] at h1; contrapose! h1
  apply Prime.prime at hp; apply finiteMultiplicity_mul_aux <;> tauto

theorem lemma_2 {n k p r:ℕ} (hk: 2 ≤ k) (hn: k ≤ n)
 (hp: p.Prime) (h1: p^r ∣ n-1) (hr: 0 < r) (h2: ¬p∣k) (h3: ¬ p∣n-k) : p^r ∣ n.choose k := by
  have h1' : p ∣ n-1 := dvd_trans (dvd_pow_self _ (by omega)) h1
  replace h1 := h1.trans ((n-1).dvd_mul_left ((n-2).choose (k-2)))
  replace h1 := h1.trans (Nat.dvd_mul_right _ n)
  rw [←binom_eq_2 hk hn] at h1
  apply Prime.prime at hp
  replace h3 : ¬p∣k-1 := by contrapose! h3; convert Nat.dvd_sub h1' h3 using 1; omega
  apply hp.pow_dvd_of_dvd_mul_right _ h3 at h1
  exact hp.pow_dvd_of_dvd_mul_right _ h2 h1

theorem key_prop {k n p r R:ℕ} (hn: n = 2^((p^R).totient))
  (hk: 1 ≤ k) (hkn: k < n) (hp: p.Prime) (hpr: p > 2^(r-1))
  (hr: 1 < r) (hr' : r ≤ (p^R).totient):
  2^r ∣ n.choose k ∨ p^R ∣ n.choose k := by
  set m := (p^R).totient
  have : 2 ^ (r - 1 + 1) ∣ n.choose k ∨ 2 ^ (m - r + 1) ∣ k := by
    apply lemma_1 hk (le_of_lt hkn) (by decide) _
    convert dvd_rfl; rw [hn]; congr; omega
  rcases this with this | this
  . left; convert this; omega
  have hcoprime : Coprime 2 p := by simp; apply hp.odd_of_ne_two; grind [Nat.le_self_pow]
  have hrm : 2^(r-1) * 2^(m-r+1) = n := by rw [hn,←pow_add]; congr; omega
  have hrp : 2^(r-1) * 2^(m-r+1) < p * 2^(m-r+1) := by gcongr
  right; apply lemma_2 _ (le_of_lt hkn) hp
  . rw [←modEq_iff_dvd']; symm
    . rw [hn]; apply_rules [ModEq.pow_totient, Coprime.pow_right]
    omega
  . by_contra!; simp at this; subst this; simp [m] at hr'; omega
  . by_contra! h
    replace := Coprime.mul_dvd_of_dvd_of_dvd ?_ h this
    . apply Nat.le_of_dvd (by positivity) at this; linarith
    apply hcoprime.symm.pow_right _
  . by_contra! h
    replace : 2^(m-r+1) ∣ n-k := by apply dvd_sub _ this; rw [←hrm]; apply dvd_mul_left
    replace := Coprime.mul_dvd_of_dvd_of_dvd ?_ h this
    . apply le_of_dvd (by omega) at this; omega
    apply hcoprime.symm.pow_right _
  apply le_of_dvd (by omega) at this
  apply (Nat.le_self_pow _ _).trans this; omega

noncomputable abbrev S (n:ℕ) : ℕ := sSup { r | ∀ k ∈ Finset.Ico 1 n, ∃ p, p.Prime ∧ p^r ∣ (n.choose k) }

theorem S_ge {n r:ℕ} (hn: 1 < n) (h: ∀ k ∈ Finset.Ico 1 n, ∃ p, p.Prime ∧ p^r ∣ n.choose k) : r ≤ S n := by
  apply le_csSup
  . rw [bddAbove_def]; use n; simp; intro r h
    specialize h 1 (by simp) hn
    obtain ⟨ p, hp, hp' ⟩ := h
    simp at hp'; apply le_of_dvd (by positivity) at hp'
    have : r < p^r := Nat.lt_pow_self hp.one_lt
    order
  aesop

theorem key_cor {p r:ℕ} (hp: p.Prime) (hpr: p > 2^(r-1)) (hr: 1 < r) :
  r ≤ S (2^((p^r).totient)) := by
  apply S_ge
  . simp; grind
  intro k hk; simp at hk
  have := key_prop rfl hk.1 hk.2 hp hpr hr ?_; swap
  . have : r-1 < p^(r-1) := Nat.lt_pow_self hp.one_lt
    have : p^(r-1) ≤ (p^r).totient := by
      rw [totient_prime_pow hp (by omega)]
      apply Nat.le_mul_of_pos_right; have := hp.one_lt; omega
    omega
  rcases this with this | this
  . use 2; simp [this, prime_two]
  use p

theorem erdos_379 : Filter.atTop.limsup (fun n ↦ (S n:ENat)) = ⊤ := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  simp; intro N; rw [iSup₂_eq_top]; intro r hr
  lift r to ℕ using (by order)
  obtain ⟨ p, hp, hp' ⟩ := exists_infinite_primes (max N (2^(r+1)+1))
  use 2^((p^(r+2)).totient), ?_
  . have := key_cor hp' ?_ (show 1 < r+2 by omega)
    all_goals simp at *; linarith
  suffices : p ≤ 2 ^ (p ^ (r + 2)).totient
  . order
  have : p-1 < 2^(p-1) := Nat.lt_two_pow_self
  have : 2^(p-1) ≤ 2 ^ (p ^ (r + 2)).totient := by
    rw [totient_prime_pow hp' (by omega)]
    gcongr; norm_num; apply Nat.le_mul_of_pos_left; have := hp'.one_lt; positivity
  omega
