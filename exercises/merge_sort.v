From stdpp Require Export sorting.
From iris.heap_lang Require Import array lang proofmode notation par.

(* ################################################################# *)
(** * Case Study: Merge Sort *)

(* ================================================================= *)
(** ** Implementation *)

(**
  Let us implement a simple multithreaded merge sort on arrays. Merge
  sort consists of splitting the array in half until we are left with
  pieces of size [0] or [1]. Then, each pair of pieces is merged into a
  new sorted array.
*)

(**
  We begin by implementing a function which merges two arrays [a1] and
  [a2] of lengths [n1] and [n2] into an array [b] of length [n1 + n2].
*)
Definition merge : val :=
  rec: "merge" "a1" "n1" "a2" "n2" "b" :=
  (** If [a1] is empty, we simply copy the second [a2] into [b]. *)
  if: "n1" = #0 then
    array_copy_to "b" "a2" "n2"
  (** Likewise if [a2] is empty instead. *)
  else if: "n2" = #0 then
    array_copy_to "b" "a1" "n1"
  else
  (**
    Otherwise, we compare the first elements of [a1] and [a2]. The
    smallest is removed and written to [b]. Rinse and repeat.
  *)
    let: "x1" := !"a1" in
    let: "x2" := !"a2" in
    if: "x1" ≤ "x2" then
      "b" <- "x1";;
      "merge" ("a1" +ₗ #1) ("n1" - #1) "a2" "n2" ("b" +ₗ #1)
    else
      "b" <- "x2";;
      "merge" "a1" "n1" ("a2" +ₗ #1) ("n2" - #1) ("b" +ₗ #1).

(**
  To sort an array [a], we split the array in half, sort each sub-array
  recursively on separate threads, and merge the sorted sub-arrays using
  [merge], writing the elements back into the array.
*)
Definition merge_sort_inner : val :=
  rec: "merge_sort_inner" "a" "b" "n" :=
  if: "n" ≤ #1 then #()
  else
    let: "n1" := "n" `quot` #2 in
    let: "n2" := "n" - "n1" in
    ("merge_sort_inner" "b" "a" "n1" ||| "merge_sort_inner" ("b" +ₗ "n1") ("a" +ₗ "n1") "n2");;
    merge "b" "n1" ("b" +ₗ "n1") "n2" "a".

(**
  HeapLang requires array allocations to contain at least one element.
  As such, we need to treat this case separately.
*)
Definition merge_sort : val :=
  λ: "a" "n",
  if: "n" = #0 then #()
  else
    let: "b" := AllocN "n" #() in
    array_copy_to "b" "a" "n";;
    merge_sort_inner "a" "b" "n".

(**
  Our desired specification will be that [merge_sort] produces a new
  sorted array which, importantly, is a permutation of the input.
*)

(* ================================================================= *)
(** ** Specifications *)

Section proofs.
Context `{!heapGS Σ, !spawnG Σ}.

(**
  We begin by giving a specification for the [merge] function. To merge
  two arrays [a1] and [a2], we require that they are both already
  sorted. Furthermore, we need the result array [b] to have enough
  space, though we don't care what it contains.
*)
Lemma merge_spec (a1 a2 b : loc) (l1 l2 : list Z) (l : list val) :
  {{{
    a1 ↦∗ ((λ x : Z, #x) <$> l1) ∗
    a2 ↦∗ ((λ x : Z, #x) <$> l2) ∗ b ↦∗ l ∗
    ⌜StronglySorted Z.le l1⌝ ∗
    ⌜StronglySorted Z.le l2⌝ ∗
    ⌜length l = (length l1 + length l2)%nat⌝
  }}}
    merge #a1 #(length l1) #a2 #(length l2) #b
  {{{(l : list Z), RET #();
    a1 ↦∗ ((λ x : Z, #x) <$> l1) ∗
    a2 ↦∗ ((λ x : Z, #x) <$> l2) ∗
    b ↦∗ ((λ x : Z, #x) <$> l) ∗
    ⌜StronglySorted Z.le l⌝ ∗
    ⌜l1 ++ l2 ≡ₚ l⌝
  }}}.
Proof.
  iLöb as "IH" forall (a1 a2 b l1 l2 l).
  iIntros "%Φ (Ha1 & Ha2 & Hb & %Hl1 & %Hl2 & %Hlen) HΦ".
  wp_rec; wp_pures.
  destruct l1 as [|x1 l1']; wp_pures.
  { (* l1 = [] *)
    wp_apply (wp_array_copy_to _ _ b a2 l ((λ x : Z, #x) <$> l2) with "[Hb Ha2]");
    first (simpl in Hlen; lia);
    first (by rewrite fmap_length); iFrame.
    iIntros "[Hb Ha2]".
    iApply "HΦ"; by iFrame. }
  destruct l2 as [|x2 l2']; wp_pures.
  { (* l2 = [] *)
    wp_apply (wp_array_copy_to _ _ b a1 l ((λ x : Z, #x) <$> x1 :: l1') with "[Hb Ha1]");
    first (simpl in Hlen; lia);
    first (by rewrite fmap_length); iFrame.
    iIntros "[Hb Ha1]".
    iApply "HΦ"; iFrame.
    by rewrite app_nil_r. }
  destruct l as [|x l']; try done; simpl.
  iDestruct (array_cons with "Ha1") as "[Hx1 Ha1]".
  iDestruct (array_cons with "Ha2") as "[Hx2 Ha2]".
  iDestruct (array_cons with "Hb") as "[Hx Hb]".
  do 2 wp_load; wp_pures.
  destruct (bool_decide_reflect (x1 ≤ x2)%Z) as [Hx|Hx]; wp_store; wp_pures.
  - assert (S (length l1') - 1 = length l1')%Z as -> by lia.
    assert (S (length l2') = length (x2 :: l2'))%Z as -> by done.
    iApply ("IH" with "[$Ha1 Hx2 Ha2 $Hb]").
    { iFrame; iPureIntro.
      inversion Hl1; auto. }
    iIntros "%l !> (Ha1 & Ha2 & Hb & %Hl & %Hperm)".
    iDestruct (array_cons with "[$Hx $Hb]") as "Hb".
    rewrite -(fmap_cons _ _ l).
    iApply "HΦ"; iFrame; iPureIntro.
    intuition.
    constructor; try done.
    inversion Hl1; inversion Hl2; subst.
    apply (Permutation_Forall Hperm).
    rewrite Forall_app; intuition.
    apply Forall_cons; intuition.
    apply (Forall_impl _ _ _ H6); lia.
  - assert (S (length l2') -1 = length l2')%Z as -> by lia.
    assert (S (length l1') = length (x1 :: l1')) as -> by done.
    iApply ("IH" with "[Hx1 Ha1 Ha2 $Hb]").
    { iFrame; iPureIntro.
      inversion Hl2; simpl in *; intuition; lia. }
    iIntros "%l !> (Ha1 & Ha2 & Hb & %Hl & %Hperm)".
    iApply "HΦ".
    iDestruct (array_cons with "[$Hx $Hb]") as "Hb".
    rewrite -(fmap_cons _ _ l); iFrame; iPureIntro; intuition.
    + constructor; try done.
      inversion Hl1; inversion Hl2; subst.
      apply (Permutation_Forall Hperm).
      apply Forall_app; intuition.
      assert (x2 ≤ x1)%Z by lia.
      apply Forall_cons; intuition.
      apply (Forall_impl _ _ _ H2); lia.
    + assert (x1 :: l1' ++ x2 :: l2' = [x1] ++ l1' ++ x2 :: l2') as -> by auto.
      do 2 (eapply Permutation_trans; first apply Permutation_app_rot).
      simpl; apply Permutation_cons; auto.
      assert (l2' ++ x1 :: l1' = l2' ++ [x1] ++ l1') as -> by auto.
      eapply Permutation_trans; first apply Permutation_app_rot.
      assert ([x1] ++ l1' ++ l2' = (x1 :: l1') ++ l2') as ->; auto.
Qed.

(**
  With this, we can prove that sort actually sorts the output.
*)
Lemma merge_sort_inner_spec (a b : loc) (l : list Z) :
  {{{
    a ↦∗ ((λ x : Z, #x) <$> l) ∗
    b ↦∗ ((λ x : Z, #x) <$> l)
  }}}
    merge_sort_inner #a #b #(length l)
  {{{(l' : list Z) vs, RET #();
    a ↦∗ ((λ x : Z, #x) <$> l') ∗
    b ↦∗ vs ∗ ⌜StronglySorted Z.le l'⌝ ∗
    ⌜l ≡ₚ l'⌝ ∗
    ⌜length vs = length l'⌝
  }}}.
Proof.
  iLöb as "IH" forall (a b l).
  do 2 (destruct l; try solve [ iIntros "%Φ [Ha Hb] HΦ"; wp_rec; wp_pures; 
    iApply "HΦ"; iFrame; iPureIntro; intuition; repeat constructor ]).
  iIntros "%Φ [Ha Hb] HΦ"; wp_rec; wp_pures.
  rewrite bool_decide_eq_false_2; last lia.
  wp_pures.
  remember (S (S (length l)) `quot` 2)%Z as len1.
  remember (S (S (length l)) - len1)%Z as len2.
  assert (0 ≤ len1 ≤ S (S (length l)) ∧ (len1 + len2 = S (S (length l))))%Z as [H H0].
  { split; last lia; split; subst.
    - by apply Z.quot_pos.
    - apply Z.quot_le_upper_bound; try done.
      by apply (Z.mul_le_mono_pos_r 1 2 (S (S (length l)))). }
  assert (∃ l1 l2, Z.of_nat (length l1) = len1 ∧ 
                   Z.of_nat (length l2) = len2 ∧ 
                   l1 ++ l2 = z :: z0 :: l) as [l1 [l2 [Hlen1 [Hlen2 H1]]]].
  { assert (S (S (length l)) = length (z :: z0 :: l))%Z by done.
    rewrite H1 in H0, H; rename l into l'.
    remember (z :: z0 :: l') as l.
    clear Heql H1 Heqlen1 Heqlen2.
    exists (take (Z.to_nat len1) l), (drop (Z.to_nat len1) l).
    intuition; first [ rewrite firstn_length_le; lia
                     | rewrite drop_length; lia
                     | apply take_drop ]. }
  rewrite -H1 fmap_app.
  iDestruct (array_app with "Ha") as "[Ha1 Ha2]".
  iDestruct (array_app with "Hb") as "[Hb1 Hb2]".
  iCombine "Hb1 Ha1" as "H1".
  iCombine "Hb2 Ha2" as "H2".
  rewrite fmap_length.
  remember (λ _ : val, ∃ l1' vs1, b ↦∗ ((λ x : Z, #x) <$> l1') ∗
            a ↦∗ vs1 ∗ ⌜StronglySorted Z.le l1'⌝ ∗
            ⌜l1 ≡ₚ l1'⌝ ∗ ⌜length vs1 = length l1'⌝)%I as Ψ1.
  remember (λ _ : val, ∃ l2' vs2, (b +ₗ len1) ↦∗ ((λ x : Z, #x) <$> l2') ∗
            (a +ₗ len1) ↦∗ vs2 ∗ ⌜StronglySorted Z.le l2'⌝ ∗
            ⌜l2 ≡ₚ l2'⌝ ∗ ⌜length vs2 = length l2'⌝)%I as Ψ2.
  wp_apply (wp_par Ψ1 Ψ2 with "[H1] [H2]").
  - rewrite -Hlen1.
    iApply ("IH" with "H1").
    iIntros "!> * H".
    subst; iFrame.
  - rewrite Hlen1 -Hlen2; wp_pures.
    iApply ("IH" with "H2").
    iIntros "!> * H"; subst.
    subst; iFrame.
  - rewrite HeqΨ1 HeqΨ2.
    iIntros "* [(%l1' & %vs1 & Hb1 & Ha1 & %Hl1' & %Hperm1 & %Hlen1')
                (%l2' & %vs2 & Hb2 & Ha2 & %Hl2' & %Hperm2 & %Hlen2')] !>"; wp_seq.
    assert (len1 = length l1') as -> by by rewrite -Hlen1 (Permutation_length Hperm1).
    assert (len2 = length l2') as -> by by rewrite -Hlen2 (Permutation_length Hperm2).
    wp_pures; remember (vs1 ++ vs2) as vs.
    rewrite -{2}Hlen1'.
    iDestruct (array_app with "[$Ha1 $Ha2]") as "Ha".
    wp_apply (merge_spec with "[$Hb1 $Hb2 $Ha]").
    { iPureIntro; intuition; by rewrite -Hlen1' -Hlen2' app_length. }
    iIntros "%l' (Hb1 & Hb2 & Ha & %Hl' & %Hperm)".
    rewrite -(fmap_length (λ x : Z, #x)).
    iDestruct (array_app with "[$Hb1 $Hb2]") as "Hb".
    rewrite -fmap_app.
    iApply ("HΦ" with "[$Ha $Hb]"); iPureIntro.
    rewrite fmap_length (Permutation_length Hperm); intuition.
    eapply Permutation_trans; first apply Permutation_app; eassumption.
Qed.

(**
  Finally, we lift this result to the outer [merge_sort] function.
*)
Lemma merge_sort_spec (a : loc) (l : list Z) :
  {{{a ↦∗ ((λ x : Z, #x) <$> l)}}}
    merge_sort #a #(length l)
  {{{(l' : list Z), RET #();
    a ↦∗ ((λ x : Z, #x) <$> l') ∗
    ⌜StronglySorted Z.le l'⌝ ∗
    ⌜l ≡ₚ l'⌝
  }}}.
Proof.
  iIntros "%Φ Ha HΦ".
  wp_lam; wp_pures.
  destruct l; simpl; wp_pures.
  - iApply "HΦ".
    rewrite -(fmap_nil (λ x : Z, #x)).
    iFrame; iPureIntro.
    repeat constructor.
  - wp_apply (wp_allocN); try done.
    iIntros "%l' [Hl' HL]".
    wp_pures.
    wp_apply (wp_array_copy_to with "[$Hl' $Ha]");
    first (rewrite replicate_length; lia);
    first (simpl; by rewrite fmap_length).
    iIntros "[Hl' Ha]"; wp_pures. rewrite -fmap_cons.
    assert (S (length l) = length ((λ x : Z, #x) <$> z :: l)) as ->
      by by rewrite fmap_length.
    rewrite fmap_length.
    wp_apply (merge_sort_inner_spec with "[$Ha $Hl']").
    iIntros "* (Ha & Hl' & %Hperm & %Hlen)".
    iApply ("HΦ" $! l'0); iFrame.
    iPureIntro; intuition.
Qed.

End proofs.
