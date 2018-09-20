Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import String.
Require Import List.
Require Import Program.Tactics.
Require Import Relation_Operators.
Require Import Ascii.
Require Import Program.
Require Import Bool.
Require Import Sorting.Permutation.

(* --------- Ascii Lemmas --------- *)

Section CharacterFacts.
  Definition ascii_eq (a b:ascii) : bool :=
    match (a, b) with
    | (Ascii a1 a2 a3 a4 a5 a6 a7 a8,
       Ascii b1 b2 b3 b4 b5 b6 b7 b8) =>
      eqb a1 b1 && eqb a2 b2 && eqb a3 b3 && eqb a4 b4 &&
          eqb a5 b5 && eqb a6 b6 && eqb a7 b7 && eqb a8 b8
    end.

  Lemma ascii_eq_refl (a:ascii):
    ascii_eq a a = true.
  Proof.
    destruct a; unfold ascii_eq; repeat rewrite eqb_reflx; simpl; auto.
  Qed.

  (* `ascii_eq` is equivalent to character equality. *)
  Lemma ascii_eq_iff a b:
    ascii_eq a b = true <-> a = b.
  Proof.
    split; intros.
    - unfold ascii_eq in H; destruct a; destruct b;
        repeat rewrite andb_true_iff in *; destruct_pairs;
          rewrite eqb_true_iff in *; congruence.
    - rewrite H; apply ascii_eq_refl.
  Qed.
End CharacterFacts.

(* --------- String Lemmas --------- *)

Section StringFacts.

  Lemma append_nil_l s:
    ("" ++ s)%string = s.
  Proof.
    simpl; auto.
  Qed.

  Lemma append_nil_r s:
    (s ++ "")%string = s.
  Proof.
    induction s; simpl; try rewrite IHs; auto.
  Qed.

  Lemma append_assoc s1 s2 s3:
    (s1 ++ s2 ++ s3)%string = ((s1 ++ s2) ++ s3)%string.
  Proof.
    induction s1; simpl; try rewrite IHs1; auto.
  Qed.

  Lemma append_comm_cons a s1 s2:
    (String a s1 ++ s2)%string = String a (s1 ++ s2)%string.
  Proof.
    induction s1; simpl; auto.
  Qed.

End StringFacts.

(* --------- regex --------- *)

Inductive regex : Set :=
| Empty : regex
| Any : regex
| Char : ascii -> regex
| Append : regex -> regex -> regex
| Or : regex -> regex -> regex
| Star : regex -> regex.

(* --------- Match --------- *)

Inductive Match : regex -> string -> Prop :=

| match_empty   : Match Empty EmptyString

| match_any     : forall (c : ascii),
                    Match Any (String c EmptyString)

| match_char    : forall (c : ascii), 
                    Match (Char c) (String c EmptyString)

| match_append  : forall (r1 r2 : regex) (s1 s2 : string),
                    Match r1 s1 -> Match r2 s2 -> Match (Append r1 r2) (s1 ++ s2)

| match_or_l    : forall (r1 r2 : regex) (s : string),
                    Match r1 s -> Match (Or r1 r2) s

| match_or_r    : forall (r1 r2 : regex) (s : string),
                    Match r2 s -> Match (Or r1 r2) s

| match_star_0  : forall (r : regex),
                    Match (Star r) EmptyString

| match_star_2  : forall (r : regex) (s1 s2 : string),
                    Match r s1 -> Match (Star r) s2 -> Match (Star r) (s1 ++ s2).

Hint Constructors Match.

(* --------- Examples --------- *)

Example example_empty : Match Empty ""%string.
Proof.
  apply match_empty.
Qed.

Example example_any : Match Any (String zero ""%string).
Proof.
  apply match_any.
Qed.

Example example_char : Match (Char "I") "I".
Proof.
  apply match_char.
Qed.

Example example_char_false : ~Match (Char "I") "J".
Proof.
  unfold not. intros.
  inversion H.
Qed.

Example example_append : Match (Append (Char "C") (Append (Or (Char "l") (Char "o")) (Char "q"))) "Coq".
Proof.
  apply match_append with (r1 := (Char "C")) (r2 := (Append (Or (Char "l") (Char "o")) (Char "q"))) (s1 := "C"%string) (s2 := "oq"%string).
  - apply match_char.
  - apply match_append with (r1 := (Or (Char "l") (Char "o"))) (r2 := (Char "q")) (s1 := "o"%string) (s2 := "q"%string).
    + apply match_or_r. apply match_char.
    + apply match_char.
Qed.

Example example_star_empty : Match (Star (Append (Char "h") (Char "i"))) ""%string.
Proof.
  apply match_star_0.
Qed.

Example example_dholland : Match (Star (Char "a")) "aaa".
Proof.
  apply match_star_2 with (s1 := "a"%string).
  2: apply match_star_2 with (s1 := "a"%string).
  3: apply match_star_2 with (s1 := "a"%string).
  all: auto.
Qed.

Example example_eric : Match (Star (Or (Char "a") (Char "b"))) "ababaabbba".
Proof.
  repeat (try apply match_star_2 with (s1 := "a"%string); auto; 
          try apply match_star_2 with (s1 := "b"%string); auto).
Qed.

(* --------- Match Lemmas --------- *)

Lemma Match_Empty (s : string) :
  Match Empty s -> s = ""%string.
Proof.
  intros. inversion H. auto.
Qed.

Function Repeat_N (r : regex) (n : nat) : regex :=
  match n with
  | O => Empty
  | S O => r
  | S (n') => Append r (Repeat_N r n')
  end.

Lemma Star_impl_Append (r : regex) (s : string) :
  Match (Star r) s -> exists n : nat, Match (Repeat_N r n) s.
Proof.
  intros. remember (Star r) as sr. induction H; try discriminate.
  - exists 0; auto.
  - injection Heqsr; intros; subst. specialize (IHMatch2 Heqsr). 
    destruct IHMatch2. exists (S x). destruct x.
    + inversion H1. rewrite append_nil_r. auto.
    + rewrite Repeat_N_equation. auto.
Qed.

Lemma Append_impl_Star (r : regex) (s : string) :
  (exists n : nat, Match (Repeat_N r n) s) -> Match (Star r) s.
Proof.
  intros. destruct H. remember (Repeat_N r x) as rep.
  revert Heqrep. revert r x. induction H; intros; subst; auto.
  1-2, 4-6: destruct x; try destruct x; try discriminate; 
            cbn in *; subst; rewrite <- append_nil_r; auto.
  functional induction (Repeat_N r x).
  - subst. discriminate.
  - rewrite <- append_nil_r. auto.
  - destruct n'; try contradiction.
    injection Heqrep; intros; cbn in *.
    specialize (IHMatch2 r (S n') H1); subst; auto.
Qed.

Lemma Star_iff_Append (r : regex) (s : string) :
  Match (Star r) s <-> exists n : nat, Match (Repeat_N r n) s.
Proof.
  unfold iff; split; intros.
  - apply Star_impl_Append; auto.
  - apply Append_impl_Star; auto.
Qed.

Lemma Repeat_dec_substring (r : regex) (x : nat) (c : ascii) (s : string) :
  Match (Append r (Repeat_N r (S x))) (String c s) -> 
  (exists (s2 s3 : string), Match r (String c s2) /\ (s = append s2 s3) /\ Match (Repeat_N r (S x)) s3) \/ Match (Repeat_N r (S x)) (String c s).
Proof.
  intros. rewrite Repeat_N_equation in H.
  inversion H. destruct x.
  - destruct s1; left; cbn in *; subst.
    + exists s; exists EmptyString; rewrite append_nil_r; auto.
    + injection H2; intros; subst. exists s1; exists s2; auto.
  - destruct s1, s2; try discriminate; injection H2; intros; cbn in *; subst; auto.
    + left. exists s1; exists EmptyString; auto.
    + left. exists s1; exists (String a0 s2); auto.
Qed.

Lemma Repeat_nonempty_substring (r : regex) (x : nat) (c : ascii) (s1 : string) :
  Match (Repeat_N r (S x)) (String c s1) -> (exists (s2 s3 : string), Match r (String c s2) /\ (s1 = append s2 s3) /\ Match (Repeat_N r x) s3).
Proof.
  intros. inversion H; subst.
  1-2: exists EmptyString; exists EmptyString; destruct x; cbn in *; auto; discriminate.
  1-4: destruct x; try discriminate; cbn in *.
  1,3-5: exists s1; exists EmptyString; rewrite append_nil_r; auto.
  rewrite <- H0 in *. revert H H0 H2 H3. revert r1 r2. induction x; intros.
  - destruct s0, s2; try discriminate; injection H0; injection H1; intros; subst; cbn in *.
    + exists s1; exists EmptyString; rewrite append_nil_r; auto.
    + exists s0; exists EmptyString; rewrite append_nil_r; auto.
    + exists s0; exists (String a0 s2); auto.
  - destruct s0, s2; try discriminate; cbn in *; injection H0; injection H1; intros; subst.
    + specialize (IHx r (match x with 0 => r | S _ => Append r (Repeat_N r x) end)).
      specialize (eq_refl (Append r match x with 0 => r | S _ => Append r (Repeat_N r x) end)); intros.
      specialize (IHx H3 H4 H2). clear H0 H1 H4. destruct x.
      1: assert (r = Repeat_N r 1) by (cbn; auto).
      2: assert ((Append r (Repeat_N r (S x))) = Repeat_N r (S (S x))) by (cbn; auto).
      all: rewrite H0 in H3; apply Repeat_dec_substring in H3; destruct H3.
      1, 3: destruct H1 as [s2 [s3 [E [F G]]]].
      3, 4: specialize (IHx H1); auto; destruct IHx as [s2 [s3 [E [F G]]]].
      1-4: exists s2; exists s3; split; try split; rewrite <- append_nil_l; auto.
    + exists s0; exists EmptyString; auto.
    + exists s0; exists (String a0 s2); auto.
Qed.

Lemma Star_nonempty_substring (r : regex) (c : ascii) (s : string) :
  Match (Star r) (String c s) -> (exists (s2 s3 : string), Match r (String c s2) /\ (s = append s2 s3) /\ Match (Star r) s3).
Proof.
  intros. apply Star_impl_Append in H. destruct H.
  destruct x; cbn in *.
  + inversion H.
  + apply Repeat_nonempty_substring in H. destruct H as [s2 [s3 [F [G H]]]].
    assert (exists n : nat, Match (Repeat_N r n) s3) by (exists x; auto).
    specialize (Append_impl_Star r s3 H0); intros.
    exists s2. exists s3. auto.
Qed.

(* --------- Implementation --------- *)

Fixpoint nu (r : regex) : bool :=
  match r with
  | Empty => true
  | Any => false
  | Char c => false
  | Append a b => andb (nu a) (nu b)
  | Or a b => orb (nu a) (nu b)
  | Star r' => true
  end.

Definition orpair (a b : bool * regex) : bool * regex :=
  match a with
  | (false, _) => b
  | (true, ra) => match b with
                  | (false, _) => a
                  | (true, rb) => (true, Or ra rb)
                  end
  end.

Definition appendpair (a b : bool * regex) : bool * regex :=
  match a with
  | (false, _) => (false, Empty)
  | (true, ra) => match b with
                  | (false, _) => (false, Empty)
                  | (true, rb) => (true, Append ra rb)
                  end
  end.

Definition condpair (q : bool) (a : bool * regex) : bool * regex :=
  match q with
  | false => (false, Empty)
  | true => a
  end.

Fixpoint deriv_char (r : regex) (c : ascii) : bool * regex :=
  match r with
  | Empty => (false, Empty)
  | Any => (true, Empty)
  | Char c' => match (ascii_eq c c') with
              | true => (true, Empty)
              | false => (false, Empty)
              end
  | Append a b => orpair (appendpair (deriv_char a c) (true, b)) (condpair (nu a) (deriv_char b c))
  | Or a b => orpair (deriv_char a c) (deriv_char b c)
  | Star r' => appendpair (deriv_char r' c) (true, r)
  end.

Fixpoint deriv_string (qr : bool * regex) (s : string) : bool * regex :=
  match qr with
  | (false, _) => (false, Empty)
  | (true, r) => match s with
                 | EmptyString => (true, r)
                 | String c s' => deriv_string (deriv_char r c) s'
                 end
  end.

Definition match_regex (r : regex) (s : string) : bool :=
  match (deriv_string (true, r) s) with
  | (false, _) => false
  | (true, r') => nu r'
  end.

(* --------- Simplification Lemmas --------- *)

Lemma simpl_fst_orpair_l (a b : bool * regex) : 
  (fst a) = true -> fst (orpair a b) = true.
Proof.
  intros. destruct a, b; cbn in *. subst; destruct b; auto.
Qed.

Lemma simpl_fst_orpair_r (a b : bool * regex) : 
  (fst b) = true -> fst (orpair a b) = true.
Proof.
  intros. destruct a, b; cbn in *. subst; destruct b0; auto.
Qed.

Lemma simpl_appendpair_l (a b : bool * regex) :
  (fst a) = true -> (appendpair a b) = match b with
                                       | (false, _) => (false, Empty)
                                       | (true, rb) => (true, Append (snd a) (snd b))
                                       end.
Proof.
  intros. destruct a, b; cbn in *; subst; auto.
Qed.

Lemma simpl_appendpair (a b : bool * regex) :
  (fst a) = true -> (fst b) = true -> (appendpair a b) = (true, Append (snd a) (snd b)).
Proof.
  intros. destruct a, b; cbn in *; subst; auto.
Qed.

Lemma simpl_condpair (q : bool) (a : bool * regex) : 
  q = true -> (condpair q a) = a.
Proof.
  intros. destruct q; auto; discriminate.
Qed.

Lemma simpl_fst_condpair_f (q : bool) (a : bool * regex) : 
  (fst a) = false -> fst (condpair q a) = false.
Proof.
  intros. destruct q; auto; discriminate.
Qed.

Lemma simpl_deriv_string (qr : bool * regex) (s : string) :
  (fst qr) = true -> (deriv_string qr s) = match s with
                                           | EmptyString => (true, (snd qr))
                                           | String c s' => deriv_string (deriv_char (snd qr) c) s'
                                           end.
Proof.
  intros. destruct qr, s; cbn in *; subst; auto.
Qed.

Lemma simpl_deriv_string_f (qr : bool * regex) (s : string) :
  (fst qr) = false -> (deriv_string qr s) = (false, Empty).
Proof.
  intros. destruct qr, s; cbn in *; subst; auto.
Qed.

Lemma true_impl_fst (a b : bool) : 
  Is_true (if a then b else false) -> a = true.
Proof.
  destruct a; auto.
Qed.

Lemma true_impl_snd (a b : bool) : 
  Is_true (if a then b else false) -> b = true.
Proof.
  destruct a, b; auto.
Qed.

Lemma true_impl_let_fst (a : bool) (r : regex) (s : string) :
  Is_true (let (b, r') := deriv_string (a, r) s in if b then nu r' else false) 
  -> (fst (deriv_string (a, r) s)) = true.
Proof.
  intros. destruct (deriv_string (a, r) s). apply true_impl_fst in H. auto.
Qed.

Lemma true_impl_let_snd (a : bool) (r : regex) (s : string) :
  Is_true (let (b, r') := deriv_string (a, r) s in if b then nu r' else false) 
  -> nu (snd (deriv_string (a, r) s)) = true.
Proof.
  intros. destruct (deriv_string (a, r) s). apply true_impl_snd in H. auto.
Qed.

Lemma true_impl_fstpair_fst (a b : bool) : 
  forall (r1 r2 : regex), Is_true (fst (if a then (b, r1) else (false, r2))) -> a = true.
Proof.
  destruct a; auto.
Qed.

Lemma Match_orpair_l (qr1 qr2 : bool * regex) (s : string) :
  fst qr1 = true -> Match (snd qr1) s -> Match (snd (orpair qr1 qr2)) s.
Proof.
  intros. destruct qr1, qr2. cbn in *. subst. destruct b0; cbn; auto.
Qed.

Lemma Match_orpair_r (qr1 qr2 : bool * regex) (s : string) :
  fst qr2 = true -> Match (snd qr2) s -> Match (snd (orpair qr1 qr2)) s.
Proof.
  intros. destruct qr1, qr2. cbn in *. subst. destruct b; cbn; auto.
Qed.

(* --------- Match -> match_regex Lemmas --------- *)

Lemma nu_equiv_Match_EmptyString (r : regex) :
  Is_true (nu r) <-> Match r EmptyString.
Proof.
  unfold iff; split; intros.
  - induction r; auto; try contradiction.
    + cbn in H. apply andb_prop_elim in H. destruct_conjs.
      rewrite <- append_nil_r; auto.
    + cbn in H. apply orb_prop_elim in H. destruct H; auto.
  - induction r; cbn; auto.
    + inversion H.
    + inversion H.
    + apply andb_prop_intro. inversion H; subst. split.
      * destruct s1; auto. discriminate.
      * destruct s2; auto. destruct s1; simpl in H2; discriminate.
    + apply orb_prop_intro. inversion H; auto.
Qed.

Lemma deriv_char_cons (r : regex) (c : ascii) (s : string) :
  Match r (String c s) -> fst (deriv_char r c) = true.
Proof.
  revert c s. induction r; auto; intros; inversion H; subst; simpl in *.
  - specialize (ascii_eq_refl c); intros. rewrite H0. cbn; auto.
  - destruct s1; cbn in *; subst.
    + apply nu_equiv_Match_EmptyString in H3. apply Is_true_eq_true in H3. rewrite simpl_condpair; auto.
      apply simpl_fst_orpair_r. specialize (IHr2 c s H4); auto.
    + injection H2; intros; subst. specialize (IHr1 c s1 H3).
      rewrite simpl_appendpair; auto. rewrite simpl_fst_orpair_l; auto.
  - specialize (IHr1 c s H3). rewrite simpl_fst_orpair_l; auto.
  - specialize (IHr2 c s H3). rewrite simpl_fst_orpair_r; auto.
  - apply Star_nonempty_substring in H. destruct H as [s3 [s4 [E [F G]]]].
    specialize (IHr c s3 E). rewrite simpl_appendpair; auto.
Qed.

Lemma deriv_char_correct (r : regex) (c : ascii) (s : string) :
  Match r (String c s) -> Match (snd (deriv_char r c)) s.
Proof.
  revert c s. induction r; intros.
  - inversion H.
  - inversion H. cbn. auto.
  - inversion H. unfold deriv_char. specialize (ascii_eq_refl c); intros. 
    rewrite H0; auto.
  - cbn. inversion H; subst.
    destruct s1.
    + cbn in H2. subst. apply nu_equiv_Match_EmptyString in H3.
      rewrite simpl_condpair; try apply Is_true_eq_true; auto.
      specialize (IHr2 c s H4). apply Match_orpair_r; auto.
      apply deriv_char_cons in H4; auto.
    + cbn in H2. assert (a = c) by congruence; subst.
      specialize (IHr1 c s1 H3). apply deriv_char_cons in H3. 
      rewrite simpl_appendpair; auto. apply Match_orpair_l; auto.
      cbn. assert (append s1 s2 = s) by congruence. subst. apply match_append; auto.
  - cbn. inversion H; subst.
    + specialize (IHr1 c s H3). destruct (deriv_char r2 c); destruct b.
      * cbn. apply deriv_char_cons in H3. apply Match_orpair_l; auto.
      * apply deriv_char_cons in H3. apply Match_orpair_l; auto.
    + specialize (IHr2 c s H3). destruct (deriv_char r1 c); destruct b.
      * apply deriv_char_cons in H3. apply Match_orpair_r; auto.
      * cbn. auto.
  - cbn. apply Star_nonempty_substring in H. destruct H as [s2 [s3 [F [G H]]]].
    specialize (IHr c s2 F). apply deriv_char_cons in F; rewrite simpl_appendpair; cbn; subst; auto.
Qed.

(* --------- match_regex -> Match Lemmas --------- *)

Lemma deriv_string_fst (r : regex) (s : string) :
  Match r s -> fst (deriv_string (true, r) s) = true.
Proof.
  revert r. induction s; intros.
  - cbn; auto.
  - specialize (deriv_char_correct _ _ _ H); intros.
    apply deriv_char_cons in H.
    specialize (IHs (snd (deriv_char r a)) H0). cbn in *.
    destruct (deriv_char r a); cbn in *. rewrite H. auto.
Qed.

Lemma deriv_string_snd (r : regex) (s : string) :
  Match r s -> Is_true (nu (snd (deriv_string (true, r) s))).
Proof.
  revert r. induction s; intros.
  - cbn. apply nu_equiv_Match_EmptyString; auto.
  - specialize (deriv_char_correct _ _ _ H); intros.
    apply deriv_char_cons in H.
    specialize (IHs (snd (deriv_char r a)) H0). cbn.
    destruct (deriv_char r a); cbn in *. rewrite H. auto.
Qed.

Lemma deriv_char_impl (r : regex) (c : ascii) (s : string) :
  fst (deriv_char r c) = true
  -> Match (snd (deriv_char r c)) s
  -> Match r (String c s).
Proof.
  revert s. induction r; intros.
  - cbn in *. discriminate.
  - cbn in *. inversion H0. auto.
  - simpl in H. apply Is_true_eq_left in H. apply true_impl_fstpair_fst in H.
    simpl in H0. rewrite H in H0. apply ascii_eq_iff in H. subst. cbn in H0. inversion H0. auto.
  - cbn in *. destruct (deriv_char r1 c) eqn:dc1, (deriv_char r2 c) eqn:dc2.
    destruct b, b0; auto; cbn in *.
    + destruct (condpair (nu r1) (false, r0)) eqn:cnd; destruct (nu r1) eqn:nu; destruct b; try discriminate; cbn in *.
      * inversion H0; subst. inversion H4; subst.
        -- specialize (IHr1 s1 H H3). rewrite <- append_comm_cons; auto.
        -- apply Is_true_eq_left in nu. apply nu_equiv_Match_EmptyString in nu. 
           specialize (IHr2 s H H4). rewrite <- append_nil_l; auto.
      * inversion H0; subst. specialize (IHr1 s1 H H3). rewrite <- append_comm_cons; auto.
    + destruct (condpair (nu r1) (false, r0)) eqn:cnd; destruct (nu r1); 
      destruct b; try discriminate; cbn in *; injection cnd; intros; subst; inversion H0; subst;
      specialize (IHr1 s1 H H3); rewrite <- append_comm_cons; auto.
    + destruct (nu r1) eqn:nu; cbn in *; try discriminate. specialize (IHr2 s H H0).
      apply Is_true_eq_left in nu. apply nu_equiv_Match_EmptyString in nu.
      rewrite <- append_nil_l; auto.
    + rewrite simpl_fst_condpair_f in H; auto; discriminate.
  - cbn in *. destruct (deriv_char r1 c), (deriv_char r2 c).
    destruct b, b0; auto; cbn in *. inversion H0; subst.
    + specialize (IHr1 s H H4); auto.
    + specialize (IHr2 s H H4); auto.
  - cbn in *. destruct (deriv_char r c). destruct b; cbn in *; try discriminate.
    inversion H0; subst. specialize (IHr s1 H H3); rewrite <- append_comm_cons; auto.
Qed.

Lemma deriv_string_impl (r : regex) (s : string) :
  fst (deriv_string (true, r) s) = true 
  -> Match (snd (deriv_string (true, r) s)) ""
  -> Match r s.
Proof.
  revert r. induction s; intros.
  - rewrite simpl_deriv_string in H0; auto.
  - rewrite simpl_deriv_string in *; cbn in *; auto.
    specialize (IHs (snd (deriv_char r a))).
    destruct (deriv_char r a) eqn:dc. destruct b.
    + cbn in IHs. rewrite <- dc in *.
      specialize (IHs H H0). apply deriv_char_impl; rewrite dc; auto.
    + rewrite simpl_deriv_string_f in H; cbn in H; auto; discriminate.
Qed.

(* --------- Correctness Theorem --------- *)

Theorem match_equivalent (r : regex) (s : string) :
  Match r s <-> Is_true (match_regex r s).
Proof.
  unfold iff; split; intros.
  - unfold match_regex.
    specialize (deriv_string_snd _ _ H); intros.
    apply deriv_string_fst in H.
    destruct (deriv_string (true, r) s); cbn in *; rewrite H; auto.
  - unfold match_regex in H.
    specialize (true_impl_let_snd _ _ _ H); intros.
    apply true_impl_let_fst in H.
    apply Is_true_eq_left in H0. apply nu_equiv_Match_EmptyString in H0.
    apply deriv_string_impl; auto.
Qed.