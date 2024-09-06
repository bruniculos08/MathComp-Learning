From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(** *** Exercise 1:
    - use no lemma to prove the following statement
*)
Lemma orbC p q : p || q = q || p.
Proof.
    by case p; case q.
Qed.

(** *** Exercise 2:
   - look up what [==>] is check if there are relevant views
   - prove that as you like
*)
Lemma Peirce p q : ((p ==> q) ==> p) ==> p.
Proof.
    by case p; case q.
Qed.

(** *** Exercise 3:
    - look for lemmas supporting contrapositive reasoning
*)
Lemma bool_gimmics1 a : a != a.-1 -> a != 0.
Proof.
    Search ((_ -> _) -> (_ -> ~~ _)).
    apply: contra_neq.
    move=> H.
    by rewrite H.
Qed.
(* Admitted. *)

(** *** Exercise 4:
    - what is [(+)] ?
    - find the right view to prove this statement
    - now find another proof without the view
*)
Lemma find_me p q :  ~~ p = q -> p (+) q.
Proof.
    Print "(+)".
    move=> /eqP.
    rewrite /addb.
    case p.
        case q.
        {
            move=> H.
            apply H.
        }
        {
            move=> {}.
            by [].
        }
        move=> /eqP H.
        by simpl in H; rewrite -H.
Qed.
(* Admitted. *)

(** *** Exercise 5:
   - it helps to find out what is behind [./2] and [.*2] in order to [Search]
   - any proof would do, but there is one not using [implyP]
*)
Lemma view_gimmics1 p a b : p -> (p ==> (a == b.*2)) -> a./2 = b.
Proof.
    Print "./2". Print ".*2".
    Check implyP.
    move=> Hp.
    rewrite Hp; simpl.
    move=> /eqP H.
    rewrite H.
    apply doubleK.
Qed.
(* Admitted. *)


(** *** Exercise 6:
    - prove that using [case:]
    - then prove that without using [case:]
*)
Lemma bool_gimmics2 p q r : ~~ p && (r == q) -> q ==> (p || r).
Proof.
    case p.
    {
        move=> Hand. simpl.
        by case q.
    }
    simpl. move=> /eqP Hrq.
    rewrite Hrq. by case q.
Qed.
(* Admitted. *)

(** *** Exercise 7:
   - the only tactics allowed are [rewrite] and [by]
   - use [Search] to find the relevant lemmas (all are good but for
     [ltn_neqAle]) or browse the #<a href="https://math-comp.github.io/htmldoc_2_0_alpha1/mathcomp.ssreflect.ssrnat.html">online doc</a>#
   - proof sketch:
<<
        m < n = ~~ (n <= m)
              = ~~ (n == m || n < m)
              = n != m && ~~ (n < m)
              = ...
>> *)
Lemma ltn_neqAle m n : (m < n) = (m != n) && (m <= n).
Proof.
    Search (_ < _ = _).
    rewrite Order.NatOrder.ltn_def.
    Search (_ != _ = _).
    rewrite neq_ltn.
    rewrite neq_ltn.
    rewrite orbC.
    rewrite orbC.
    by [].
Qed.

(** Exercise 8:
    - induction on lists
*)
Lemma mem_cat (T : eqType) (x : T) s1 s2 :
  (x \in s1 ++ s2) = (x \in s1) || (x \in s2).
Proof.
    elim s1.
    {
        by [].   
    }
    move=> Ht l Hi.
    simpl. unfold "\in" in *. simpl.
    simpl in Hi. rewrite Hi.
    rewrite orbA. by [].
Qed.
(* Admitted. *)