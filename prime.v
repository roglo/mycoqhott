Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Fixpoint prime_test n d :=
  match d with
  | 0 | 1 => true
  | S d' =>
      match n mod d with
      | 0 => false
      | _ => prime_test n d'
      end
  end.

Definition is_prime n :=
  match n with
  | 0 | 1 => false
  | S n' => prime_test n n'
  end.

Theorem fold_mod_succ : ∀ n d, d - snd (Nat.divmod n d 0 d) = n mod (S d).
Proof. easy. Qed.

Theorem not_prime_div : ∀ n d, 2 ≤ n → d < n →
  prime_test n d = false
  → ∃ m, 1 < m ∧ Nat.divide m n.
Proof.
intros * Hn Hd Hp.
revert n Hn Hd Hp.
induction d; intros; [ easy | ].
cbn in Hp.
rewrite fold_mod_succ in Hp.
...

Theorem not_prime : ∀ n, 2 ≤ n →
  is_prime n = false → ∃ d, 1 < d ∧ Nat.divide d n.
Proof.
intros * Hn Hp.
destruct n; [ flia Hn | ].
destruct n; [ flia Hn | ].
clear Hn.
unfold is_prime in Hp.
apply (not_prime_div _ (S n)); [ flia | flia | easy ].
...

Theorem infinite_primes : ∀ n, ∃ m, m > n ∧ is_prime m = true.
Proof.
intros.
set (fn := fact n + 1).
remember (is_prime fn) as pfn eqn:Hpfn.
symmetry in Hpfn.
destruct pfn.
-exists fn.
 split; [ | easy ].
 subst fn; clear Hpfn.
 induction n; [ flia | cbn ].
 rewrite <- (Nat.add_1_r n).
 apply Nat.add_lt_mono_r.
 destruct n; [ cbn; flia | ].
 apply (lt_le_trans _ (fact (S n) + 1)). {
   cbn.
   rewrite <- Nat.add_1_r.
   apply Nat.add_lt_mono_r.
   cbn in IHn; flia IHn.
 }
 apply Nat.add_le_mono_l; cbn.
 specialize (fact_neq_0 n) as H.
 remember (fact n) as m eqn:Hm.
 destruct m; [ easy | flia ].
-idtac.
