From iris.algebra Require Import auth excl gset numbers.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation.

(* ################################################################# *)
(** * Case Study: Ticket Lock *)

(* ================================================================= *)
(** ** Implementation *)

(**
  Let us look at another implementation of a lock, namely a ticket lock.
  Instead of having every thread fight to acquire the lock, the ticket
  lock makes them wait in line. It functions similarly to a ticketing
  system that one often finds in bakeries and pharmacies. Upon entering
  the shop, you pick a ticket with some number and wait until the number
  on the screen has reached your number. Once this happens, it becomes
  your turn to speak to the shop assistant. In our scenario, talking to
  the shop assistant corresponds to accessing the protected resources.

  To implement this, we will maintain two counters: [o] and [n]. The
  first counter, [o], represents the number on the screen – the customer
  currently being served. The second counter, [n], represents the next
  number to be dispensed by the ticketing machine.

  To acquire the lock, a thread must increment the second counter, [n],
  and keep its previous value as a ticket for a position in the queue.
  Once the ticket has been obtained, the thread must wait until the
  first counter, [o], reaches its ticket value. Once this happens, the
  thread gets access to the protected resources. The thread can then
  release the lock by incrementing the first counter.
*)

Definition mk_lock : val :=
  λ: <>, (ref #0, ref #0).

Definition wait : val :=
  rec: "wait" "n" "l" :=
  let: "o" := !(Fst "l") in
  if: "o" = "n" then #() else "wait" "n" "l".

Definition acquire : val :=
  rec: "acquire" "l" :=
  let: "n" := !(Snd "l") in
  if: CAS (Snd "l") "n" ("n" + #1) then
    wait "n" "l"
  else
    "acquire" "l".

Definition release : val :=
  λ: "l", Fst "l" <- ! (Fst "l") + #1.

(* ================================================================= *)
(** ** Representation Predicates *)

(**
  As a ticket lock is a lock, we expect it to satisfy the same
  specification as the spin-lock. This time, you have to come up with
  the necessary resource algebra and lock invariant by yourself. It
  might be instructive to first look through all required predicates and
  specifications to figure out exactly what needs to be proven.
*)

Definition RA : cmra :=
  authR (prodUR (optionUR (exclR natO)) (gset_disjR nat)).

Section proofs.
Context `{!heapGS Σ, !inG Σ RA}.
Let N := nroot .@ "ticket_lock".

(**
  This time around, we know that the thread is locked by a thread with a
  specific ticket. As such, we first define a predicate [locked_by]
  which states that the lock is locked by ticket [o].
*)
Definition locked_by (γ : gname) (o : nat) : iProp Σ :=
  own γ (◯ (Excl' o, GSet ∅)).

(** The lock is locked when it has been locked by some ticket. *)
Definition locked (γ : gname) : iProp Σ :=
  ∃ o, locked_by γ o.

Lemma locked_excl γ : locked γ -∗ locked γ -∗ False.
Proof.
  iIntros "[%o1 Hγ1] [%o2 Hγ2]".
  iCombine "Hγ1 Hγ2" gives "%H".
  rewrite auth_frag_valid /= pair_valid /= in H.
  by destruct H.
Qed.

(**
  We will also have a predicate signifying that ticket [x] has been
  _issued_. A thread will need to have been issued ticket [x] in order
  to wait for the first counter to become [x].
*)
Definition issued (γ : gname) (x : nat) : iProp Σ :=
  own γ (◯ (ε, GSet {[x]})).

Definition lock_inv (γ : gname) (lo ln : loc) (P : iProp Σ) : iProp Σ :=
  ∃ o n : nat, lo ↦ #o ∗ ln ↦ #n ∗ 
  own γ (● (Excl' o, GSet (set_seq 0 n))) ∗
  ((locked_by γ o ∗ P) ∨ issued γ o).

Definition is_lock (γ : gname) (l : val) (P : iProp Σ) : iProp Σ :=
  ∃ lo ln : loc, ⌜l = (#lo, #ln)%V⌝ ∗ inv N (lock_inv γ lo ln P).

(* ================================================================= *)
(** ** Specifications *)

Lemma mk_lock_spec P :
  {{{ P }}} mk_lock #() {{{ γ l, RET l; is_lock γ l P }}}.
Proof.
  iIntros "%Φ P HΦ".
  rewrite /mk_lock; wp_pures.
  wp_alloc ln as "Hln".
  wp_alloc lo as "Hlo".
  wp_pures.
  iMod (own_alloc (● (Excl' 0, GSet ∅) ⋅ ◯ (Excl' 0, GSet ∅))) as "(%γ & Hγ & Ho)";
    first by apply auth_both_valid_discrete.
  iApply ("HΦ" $! γ).
  iExists lo, ln.
  iSplitR; first done.
  iMod (inv_alloc with "[P Hln Hlo Hγ Ho]") as "#I"; last by iFrame "#".
  iExists 0, 0.
  iFrame.
  iLeft.
  iFrame.
Qed.

Lemma wait_spec γ l P x :
  {{{ is_lock γ l P ∗ issued γ x }}}
    wait #x l
  {{{ RET #(); locked γ ∗ P }}}.
Proof.
  iIntros "%Φ [(%lo & %ln & -> & #I) Hx] HΦ".
  iLöb as "IH".
  wp_rec.
  wp_pures.
  wp_bind (! _)%E.
  iInv "I" as "(%o & %n & Hlo & Hln & Hγ)".
  wp_load.
  destruct (decide (#o = #x)).
  - injection e as e.
    apply (inj Z.of_nat) in e; subst x.
    iDestruct "Hγ" as "[Hγ [[Hexcl P]|Ho]]".
    + iSplitL "Hlo Hln Hγ Hx"; first by iFrame.
      iModIntro; wp_pures.
      rewrite bool_decide_eq_true_2; last done.
      wp_pures.
      iApply "HΦ".
      by iFrame.
    + iCombine "Hx Ho" gives "%H".
      rewrite auth_frag_valid /= pair_valid /= in H.
      destruct H as [_ H].
      apply gset_disj_valid_op in H.
      by rewrite disjoint_singleton_l not_elem_of_singleton in H.
  - iSplitL "Hlo Hln Hγ"; first by iFrame.
    iModIntro; wp_pures.
    rewrite bool_decide_eq_false_2; last done.
    wp_pures.
    by iApply ("IH" with "Hx").
Qed.

Lemma acquire_spec γ l P :
  {{{ is_lock γ l P }}} acquire l {{{ RET #(); locked γ ∗ P }}}.
Proof.
  iIntros "%Φ (%lo & %ln & -> & #I) HΦ".
  iLöb as "IH".
  wp_rec; wp_pures.
  wp_bind (! _)%E.
  iInv "I" as "(%o & %n & Hlo & Hln & Hγ)".
  wp_load.
  iSplitL "Hlo Hln Hγ"; first by iFrame.
  clear o.
  iModIntro; wp_pures.
  wp_bind (CmpXchg _ _ _).
  iInv "I" as "(%o & %n' & Hlo & Hln & Hγ)".
  destruct (decide (#n = #n')).
  - injection e as e.
    apply (inj Z.of_nat) in e; subst n'.
    wp_cmpxchg_suc.
    assert (#(n + 1) = #(S n)) as ->.
    { rewrite -(Nat2Z.inj_add _ 1). 
      by (replace (S n) with (n + 1) by lia). }
    iDestruct "Hγ" as "[Hγ Hγ']".
    iMod (own_update _ _ (● (Excl' o, GSet (set_seq 0 (S n))) ⋅ ◯ (ε, GSet {[n]})) with "Hγ") as "[Hγ Hn]".
    { apply auth_update_alloc, prod_local_update_2.
      assert (GSet {[n]} ≡ GSet {[n]} ⋅ ε) as -> by rewrite right_id //.
      assert (GSet (set_seq 0 (S n)) ≡ GSet {[n]} ⋅ GSet (set_seq 0 n)) as ->.
      { rewrite set_seq_S_end_union_L gset_disj_union.
        - done.
        - replace n with (0 + n) at 1 by lia. 
          apply set_seq_S_end_disjoint. }
      apply gset_disj_alloc_op_local_update.
      replace n with (0 + n) at 1 by lia. 
      apply set_seq_S_end_disjoint. }
    rewrite {2}/lock_inv.
    iSplitL "Hlo Hln Hγ Hγ'"; first by iFrame.
    iModIntro; wp_pures.
    wp_apply (wait_spec with "[$Hn] HΦ").
    by iFrame "#".
  - wp_cmpxchg_fail.
    iFrame; iModIntro; wp_pures.
    by iApply "IH".
Qed.

Lemma release_spec γ l P :
  {{{ is_lock γ l P ∗ locked γ ∗ P }}} release l {{{ RET #(); True }}}.
Proof.
  iIntros "%Φ ((%lo & %ln & -> & #I) & [%o Hγ] & P) HΦ".
  wp_lam; wp_pures.
  wp_bind (! _)%E.
  iInv "I" as "(%o' & %n & Hlo & Hln & Hγ' & [[>Ho' _] | Ho])".
  { iCombine "Hγ Ho'" gives "%H".
    rewrite auth_frag_valid pair_valid /= in H.
    by destruct H. }
  wp_load.
  iCombine "Hγ Hγ'" gives "%H".
  rewrite cmra_comm auth_both_valid_discrete pair_included Excl_included in H.
  assert (o ≡ o') as [] by intuition.
  iModIntro.
  iFrame "Hlo Hln Hγ' Ho".
  wp_pures; clear.
  rewrite Z.add_comm -(Nat2Z.inj_add 1) /=.
  iInv "I" as "(%o' & %n & Hlo & Hln & Hγ' & [[>Ho' _]|Ho])".
  { iCombine "Hγ Ho'" gives "%H".
    rewrite auth_frag_valid pair_valid /= in H.
    by destruct H. }
  wp_store.
  iAssert (True)%I as "⊤"; first done.
  iPoseProof ("HΦ" with "⊤") as "HΦ"; iClear "⊤".
  iCombine "Hγ Hγ'" gives "%H".
  rewrite cmra_comm auth_both_valid_discrete pair_included Excl_included in H.
  assert (o ≡ o') as [] by intuition.
  iFrame "Hlo ∗"; clear.
  iCombine "Hγ Hγ'" as "Hγ".
  iMod (own_update _ _ (● (Excl' (S o), GSet (set_seq 0 n)) ⋅ ◯ (Excl' (S o), GSet ∅)) with "Hγ") as "[Hγ Ho']".
  { rewrite cmra_comm.
    by apply auth_update, prod_local_update_1, 
             option_local_update, exclusive_local_update. }
  iCombine "Ho' P" as "HP".
  by iFrame. 
Qed.

End proofs.
