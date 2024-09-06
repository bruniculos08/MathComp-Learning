From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Elements *)

Definition elements {A} (f : _ -> A) n :=
  let l := iota 0 n.+1 in zip l (map f l).

(** Triangular number *)
Definition delta n := (n.+1 * n)./2.

Lemma deltaE n : delta n =  (n.+1 * n)./2.
Proof. by []. Qed.

Lemma delta1 : delta 1 = 1.
Proof. by []. Qed.

Compute elements delta 10.

(** Hints : halfD half_bit_double *)
Lemma deltaS n : delta n.+1 = delta n + n.+1.
Proof.
  rewrite /delta.
  have: forall x y, x./2 + y = (x + y.*2)./2.
    {
      move=> x. elim: x.
      {
        move=> y.
        rewrite add0n. Search (_./2).
        rewrite -divn2. Search (0 %/ _).
        rewrite div0n. rewrite add0n.
        Search (_.*2). elim: y => //.
        {
          move=> m Hi. rewrite doubleS.
          simpl. rewrite -Hi. by [].   
        }
      }
      move=> x Hi y. 
      destruct (odd x) eqn:Case.
      {
        Search (odd). pose proof (oddS x).
        rewrite Case in H. Search (~~ _ = _).
        apply negbLR in H. Search (odd).
        apply even_halfK in H.
        rewrite <-H at 2. Search (odd).
        rewrite halfD.
        rewrite odd_double.
        rewrite odd_double.
        simpl (false && false).
        rewrite H. simpl. rewrite add0n.
        pose proof (odd_double y).
        Search (double). rewrite half_double.
        reflexivity.
      }
      pose proof (oddS x). rewrite Case in H.
      simpl (~~ false) in H. Search (_./2).
      rewrite halfD.
      rewrite H. rewrite odd_double.
      rewrite half_double. simpl. rewrite add0n.
      reflexivity.
    }
  move=> H. rewrite (H (n.+1 * n) (n.+1)).
  Search (_ * _). rewrite mulnS.
  rewrite mulnC. Print Notation "n .+2".
  rewrite -add2n.
  rewrite mulSn. rewrite -mul2n.
  rewrite mulnS. rewrite mulnDr.
  rewrite (addnC (n * 2)).
  rewrite (addnC 2).
  rewrite -addnA.
  rewrite (addnC _ (n * n + n * 2)).
  rewrite -addnA.
  rewrite (addnC (n * 2)).
  rewrite (mulnC).
  rewrite -addnA.
  by [].
Qed.
(* Admitted.  *)

(* Hints half_leq *)
Lemma leq_delta m n : m <= n -> delta m <= delta n.
Proof.
  rewrite /delta.
  move: m. elim n => [|k Ik].
  {
    move=> m mL0. simpl. Search (_ <= 0).
    rewrite leqn0 in mL0. move: mL0. move=> /eqP H.
    rewrite H. simpl. by [].
  }
  move=> m HLSk. have: forall x, x.+2 = ((x + 1).+1).
  {
    by move=> x; rewrite addn1. 
  }
  move=> Hx.  
  rewrite Hx. rewrite -(addn1 k). 
  rewrite -(deltaE (k + 1)). rewrite addnC add1n.
  rewrite deltaS. Search (_ <= _ + _).
  rewrite -!deltaE.
  rewrite -(addn0 (delta m)).
  Search (_ || _).
  rewrite leq_eqVlt in HLSk. Search (_ || _).
  apply Bool.orb_true_iff in HLSk. 
  case: HLSk => HLSk.
  {
    rewrite addn0. move: HLSk. move=> /eqP mEQSk.
    rewrite -mEQSk addnC mEQSk addnC deltaS.
    Search (_ <= _). rewrite leqnn. by [].
  }
  Search (_ < _). apply ltnSE in HLSk.
  Search (_ <= _ + _).
  apply (@leq_add (delta m) 0 (delta k) (k.+1)).
  {
    apply Ik. assumption. 
  }
  {
    apply leq0n.
  }
Qed.
(* Admitted. *)

(** Hints sqrnD *)
Lemma delta_square n : (8 * delta n).+1 = n.*2.+1 ^ 2.
Proof.
  symmetry. rewrite -addn1 sqrnD.
  rewrite -!mulnn. rewrite !muln1.
  symmetry.
  rewrite -addn1. rewrite deltaE.
  rewrite (mulnC _ n).
  have: (8 = 4 * 2) by [].
  move=> H8. rewrite H8 -mulnA. rewrite mul2n.
  have: forall n, odd (n * n.+1) = false.
  {
    move=> m. elim m => [|k Ik] //.
    rewrite -addn2. Search (_ * _). 
    rewrite mulnC mulnS. rewrite -addnA.
    rewrite addnC -addnA addnC addn2.
    simpl. have: (k + 2) = (k + 1).+1.
    { rewrite -addn1 -addn1 -addn1. 
      rewrite !add0n. rewrite addnA. symmetry.
      rewrite !addn1. by [].  
    }
    move=> H. rewrite H. rewrite mulSn.
    rewrite -addnA addnC -addnA addnn.
    Search (odd). rewrite oddD.
    rewrite addn1 mulnC Ik. simpl.
    rewrite odd_double. by simpl.   
  }
  move=> oddnSn. Search (odd).
  rewrite halfK. rewrite oddnSn.
  simpl. rewrite subn0.
  rewrite mulnS. clear H8.
  rewrite -mul2n. rewrite (mulnA 2 2 n).
  have: 4 = 2 * 2. { by []. }
  move=> H4.
  rewrite -H4.
  rewrite -mulnA (mulnC n) -mulnA mulnA.
  rewrite -H4.
  rewrite addnC.
  symmetry.
  rewrite addnC. rewrite addnA. symmetry.
  rewrite addnC. rewrite !addn1.
  f_equal. Search (_ + _).
  rewrite H4. rewrite mulnC mulnA.
  rewrite !muln2. rewrite !doubleD.
  symmetry.
  rewrite mulnC -!mul2n.
  rewrite -H4. symmetry. rewrite mulnA -H4.
  rewrite mulnA -H4. by rewrite mulnC. 
Qed.
(* Admitted. *)

(**  Triangular root *)
Definition troot n := 
 let l := iota 0 n.+2 in
 (find (fun x => n < delta x) l).-1.

Compute (iota 0 5).
Compute (troot 3).

Lemma trootE n :
  troot n = (find (fun x => n < delta x) (iota 0 n.+2)).-1.
Proof. by []. Qed.

Compute elements troot 10.
(* Find retorna a posição!!!!!!! *)
About find.
Print find.

Lemma troot_gt0 n : 0 < n -> 0 < troot n.
Proof.
  elim n => [|k Ik].
  { move=> //= H. }
  { move=> // H.
    (* move: Ik. case: k => k.
    { by []. }
    { move=> H Ik. have: 0 < k.+1.
        by [].
      move=> H0. apply H in H0.
      unfold "<". unfold "<" in H0.
      rewrite /troot in H0.  
      rewrite /troot. simpl.  
    } *)
  }
Qed.  
(* Admitted. *)

(* unfold não é necessário, pois para qualquer definição *)

(** Hints before_find find_size size_iota nth_iota *)
Lemma leq_delta_root m : delta (troot m) <= m.
Proof.
  case: m => //.
  move=> n.
  elim: n => [ //= |k Hk].
  rewrite /troot. 
  rewrite /troot in Hk.
  have: (find (fun x : nat => k.+2 < delta x) (iota 0 k.+4)).-1 < (find (fun x : nat => k.+2 < delta x) (iota 0 k.+4)).
    rewrite //=.
  move=> H. apply (before_find 0) in H.
  remember (fun x : nat => k.+1 < delta x) as f1.
  remember (fun x : nat => k.+2 < delta x) as f2.
  pose proof (find_size f2 (iota 0 k.+4)).
  rewrite size_iota in H0.
  (* Aqui tem como resolver *)
  have: (find f2 (iota 0 k.+4)).-1 < k.+4.
    Search (_ <= _ = _).
    rewrite leq_eqVlt in H0.
    Search (_ || _).
    move: H0.
    move=> /orP H0.
    destruct H0.
      {
        move: H0.
        move=> /eqP H0. 
        rewrite H0 //=. 
      }
      { 
        apply (@ltn_trans (find f2 (iota 0 k.+4)) (find f2 (iota 0 k.+4)).-1 (k.+4)).
        { subst f2. rewrite //=. }
        (* Igual ao assumption: *)
        move=> //. 
      }
    move=> H1.
    apply (nth_iota 0 0) in H1.
    rewrite add0n in H1.
    rewrite H1 in H.
    (* Agora é só usar a hipótese H: *)
    Search (_ < _).
    rewrite ltnNge in H.
    Search (~~ _ = false).
    apply negbFE in H.
    move=> //.
Qed.
(* Admitted *)

(** Hints hasP mem_iota half_bit_double half_leq nth_find nth_iota *)
Lemma ltn_delta_root m : m < delta (troot m).+1.
Proof.
  (* 
    Bruno's notes: 
    - The exists2 is equal to an exist but it uses
    is ture to then build a prop. 
  *)
  rewrite /troot.
  remember (fun x : nat => m < delta x) as f.
  destruct (has f (iota 0 m.+2)) eqn:Case.
  {
    apply (nth_find 0) in Case as H.
    move: Case. move=> /hasP Case.
    case: Case. move=> x Hx1.
    rewrite mem_iota in Hx1.
    move=> Hx2. rewrite add0n in Hx1.
    have: (x < m.+2).
      move=> //.
    move=> xLm2. apply (nth_iota 0 0) in xLm2.
    rewrite // add0n in xLm2.
    rewrite nth_iota in H.
    {
      rewrite add0n in H.
      rewrite Heqf in H.
      rewrite -Heqf in H.
      Search (_.-1.+1).
      rewrite prednK.
        move=> //.
      destruct ((find f (iota 0 m.+2))).
      {
        rewrite // in H.
      }
      rewrite //=.
    }
    pose proof (find_size f (iota 0 m.+2)).
    have: (find f (iota 0 m.+2) <= x).
      {
        (* Search (find). *)
        Search (_ <= _).
        rewrite leqNgt.
        destruct (x < find f (iota 0 m.+2)) eqn:Case.
        {
          apply (before_find 0) in Case.
          rewrite xLm2 in Case.
          rewrite Hx2 in Case.
          rewrite Case //=.
        }
        rewrite //=.
      }
    move=> findLx.
    have: x < m.+2.
      move=> //.
    move=> {}xLm2.
    Search (_ -> _ -> _ < _).
    apply (leq_ltn_trans findLx xLm2).
  }
  Search (_ = false).
  apply negbT in Case.
  Search (has).
  apply hasNfind in Case.
  rewrite size_iota in Case.
  rewrite Case.
  rewrite deltaS //=.
  have: m < m.+2.
    rewrite //=.
  move=> mLm2.
  rewrite addnC.
  Search (_ < _ + _).
  apply ltn_addr.
  move=> //.
  (* rewrite pred_Sn. *)
Qed.
(* Admitted. *)

Lemma leq_root_delta m n : (n <= troot m) = (delta n <= m).
Proof.
  case H : (n <= troot m).
  (* destruct (n <= troot m) eqn:Case. *)
    {
      symmetry. rewrite /troot in H.
      have: 
        (find (fun x : nat => m < delta x) (iota 0 m.+2)).-1
        <
        (find (fun x : nat => m < delta x) (iota 0 m.+2)).
        rewrite //=.
      move=> trLf. apply (before_find 0) in trLf.
      rewrite nth_iota in trLf.
        {
          rewrite add0n in trLf.
          apply negbT in trLf.
          rewrite -leqNgt in trLf.
          have: n < (find (fun x : nat => m < delta x) (iota 0 m.+2)).
            move=> //.
          move=> nLf. apply (before_find 0) in nLf.
          rewrite nth_iota in nLf.
          rewrite add0n in nLf.
          apply negbT in nLf.
          rewrite -leqNgt in nLf.
          move=> //.

          rewrite -trootE in H.
          rewrite -trootE in trLf.
          have: n <= delta n.
            move: H trLf.
            elim: n => [//= |k Hk].
            move=> kLtm dtmLm.
            rewrite deltaS ltn_addl //=.
          move=> nLdn.
          have: n <= m.
            apply leq_delta in H.
            pose proof (leq_trans nLdn H).
            apply (leq_trans H0 trLf).
          move=> nLm.
          have mLm2: m < m.+2.
            by rewrite //=.
          apply (leq_ltn_trans nLm mLm2).
        }
        pose proof (find_size (fun x : nat => m < delta x) (iota 0 m.+2)).
        rewrite size_iota in H0.
        rewrite //=.
    }
    symmetry.
    rewrite -Bool.negb_true_iff.
    rewrite -Bool.negb_true_iff in H.
    Search (~~ (_ <= _)).
    rewrite -ltnNge.
    rewrite -ltnNge in H.
    apply leq_delta in H.
    pose proof (ltn_delta_root m).
    Search (_ <= _ = _).
    rewrite leq_eqVlt in H.
    move: H. move=> /orP H.
    case : H.
      {
        move=> /eqP H.
        by [rewrite -H; move=>//]. 
      }
      {
        move=> H. apply (ltn_trans H0 H).
      }  
Qed.
(* Admitted. *)

Lemma leq_troot m n : m <= n -> troot m <= troot n.
Proof.
  move=> mLn. 
  (* pose proof (ltn_delta_root m) as mLd. *)
  rewrite leq_root_delta /troot.
  have: (find (fun x : nat => m < delta x) (iota 0 m.+2)).-1 < (find (fun x : nat => m < delta x) (iota 0 m.+2)).
    rewrite //=.
  move=> fLf.
  apply (before_find 0) in fLf as nF.
  apply negbT in nF.
  rewrite -leqNgt in nF.
  remember (fun x : nat => m < delta x) as f.
  remember (iota 0 m.+2) as s.
  pose proof (find_size f s).
  subst s. rewrite size_iota in H.
  rewrite nth_iota in nF. 
  rewrite add0n in nF.
  apply (leq_trans nF mLn).
    Search (_ < _).
    rewrite leq_eqVlt in H.
    move: H.
    move=> /orP [H|H].
      {
        move: H. move=> /eqP H.
        rewrite H //=. 
      }
      {
        apply (ltn_trans fLf H).
      }
Qed.
(* Admitted. *)

Lemma troot_delta m n : (troot m == n) = (delta n <= m < delta n.+1).
Proof.
  rewrite ltnNge. 
  rewrite -!leq_root_delta.
  rewrite -ltnNge. 
  rewrite ltnS.
  rewrite -eqn_leq. 
  rewrite eq_sym.
  by [].
Qed.
(* Admitted. *)

Lemma troot_deltaK n : troot (delta n) = n.
Proof.
  apply/eqP. rewrite troot_delta.
  rewrite leqnn. rewrite deltaS.
  rewrite -(addn1 n) addnA addn1 addnC.
  rewrite -(addn1 (n + delta n)) -addnA.
  rewrite ltn_addl //.
  rewrite addn1 leqnn //.
Qed.
(* Admitted. *)

(**  The modulo for triangular numbers *)
Definition tmod n := n - delta (troot n).

Lemma tmodE n : tmod n = n - delta (troot n).
Proof. by []. Qed.

Lemma tmod_delta n : tmod (delta n) = 0.
Proof.
  by rewrite /tmod troot_deltaK subnn.
Qed.
(* Admitted. *)

Lemma delta_tmod n : n = delta (troot n) + tmod n.
Proof.
  rewrite addnC /tmod. Search (_ - _ + _).
  rewrite subnK //. by rewrite leq_delta_root.
Qed.
(* Admitted. *)

Lemma leq_tmod_troot n : tmod n <= troot n.
Proof.
  rewrite /tmod. rewrite leq_subLR. 
  rewrite -ltnS. rewrite -addnS.
  rewrite -deltaS. by rewrite ltn_delta_root.
Qed.
(* Admitted. *)

Lemma ltn_troot m n : troot m < troot n -> m < n.
Proof.
  (* rewrite leq_root_delta. move=> H.
  rewrite -addn1.
  pose proof (ltn_delta_root m).
  rewrite -addn1 in H0.
  apply (leq_trans H0 H). *)
  (*D*)rewrite leq_root_delta deltaS => /(leq_trans _) -> //.
  (*D*)rewrite [X in X < _]delta_tmod.
  rewrite ltn_add2l.
  rewrite ltnS.
  by rewrite leq_tmod_troot.
Qed.
(* Admitted. *)

Lemma leq_tmod m n : troot m = troot n -> (tmod m <= tmod n) = (m <= n).
Proof.
  move=> tmEtn.
  rewrite {2}(delta_tmod m) {2}(delta_tmod n).
  by rewrite tmEtn leq_add2l.
Qed.
(* Admitted. *)

Lemma leq_troot_mod m n : 
   m <= n = 
   ((troot m < troot n) || ((troot m == troot n) && (tmod m <= tmod n))).
Proof.
  (* case: (leqP (troot n) (troot m)) => [H|H]; last first.
    rewrite //=.
    apply ltn_troot in H.
    apply (ltnW H).
  rewrite //=. *)
  
  (*  "Prova do gabarito:" *)
  (*  "(1) Casos de '<=' e '<' entre (troot n) e (troot m)" *)
  case: leqP => [|dmGdn] /= ; last first.
  (*  "isto é equivalente à:" case: (leqP (troot n) (troot m)) => [|dmGdn] /= ; last first. *)
  (*  "(2) 'fold' do 'is_true':" *)
    apply/idP.
  (*  "(3) Comando semelhante ao 'transitivity' padrão do Coq:" *)
    apply: (leq_trans (_ : _ <= delta (troot m).+1)).
      by rewrite ltnW // ltn_delta_root.
  (*  "(4) Comando semelhante ao 'transitivity' padrão do Coq:" *)
    apply: (leq_trans (_ : _ <= delta (troot n))).
      by apply: leq_delta.
  (*  "(5) " *)
    by apply: leq_delta_root.
  (*  "(6) O seguinte comando faz o rewrite na premissa e introduz
      a mesma (fazendo destruct nesse caso):" *)
  rewrite leq_eqVlt => /orP[/eqP dnEdm|dmLdn].
    rewrite dnEdm eqxx /=.
  (*  "(7) Faz rewrite na expressão X conforme o padrão indicado:"*)
    rewrite [X in (X <= _) = _]delta_tmod [X in _ <= X = _]delta_tmod.
    by rewrite dnEdm leq_add2l.
  rewrite (gtn_eqF dmLdn) /=.
  apply/idP/negP.
  rewrite -ltnNge.
  apply: (leq_trans (ltn_delta_root _)).
  apply: (leq_trans _ (leq_delta_root _)).
  by apply: leq_delta.
Qed.
(* Admitted. *)

(** Fermat Numbers *)

Definition fermat n := (2 ^ (2 ^ n)).+1.

Lemma fermatE n : fermat n = (2 ^ (2 ^ n)).+1.
Proof. by []. Qed.

Compute elements (prime \o fermat) 4.

(** Hints : subn_sqr subnBA odd_double_half *)
Lemma dvd_exp_odd a k : 
  0 < a -> odd k -> a.+1 %| (a ^ k).+1.
Proof.
  move=> aP kO. 
  (*  "(1) Reescreve com o teorema 'odd_double_half' tendo k como argumento, elimina a premissa k0 e reescreve com o teorema 'add1n': " *)
  rewrite -[k]odd_double_half {}kO add1n.
  (*  "(2) Faz indução em k/2 e resolve o caso base após o 'first': " *)
  elim: {k}_./2 => [|k IH]; first by apply/dvdnn.
  (*  "(3) " *)
  rewrite doubleS. have eqH : (a ^ k.*2.+3) = (a ^ k.*2.+1) + ((a ^ 2) - 1) * (a ^ k.*2.+1).
    {
      Search (_ ^ _). rewrite !expnSr expn0 mul1n.
      rewrite -mulSn. rewrite subn1. Search (_.-1.+1).
      rewrite PeanoNat.Nat.succ_pred_pos; last first.
        {
          Search (reflect _ (_ < _)).
          apply /(@ltP 0 (a * a)). rewrite muln_gt0 aP //.
        }
        rewrite (mulnC (a ^ k.*2)) (mulnA (a * a) _ _).
        rewrite (mulnC a) -!expnSr.
        by rewrite mulnC !mulnA -!expnSr.    
    }
    rewrite eqH. rewrite -addSn.
    rewrite -[X in _ %| _ + (_ - X) * _](exp1n 2).
    rewrite subn_sqr. Search (_ %| _ + _).
    apply dvdn_add.
      {
        move=> //.
      }
      {
        Search (_ %| _ * _). apply dvdn_mulr.
        apply dvdn_mull. rewrite addn1. apply dvdnn.
      } 
Qed.
(* Admitted. *)

Compute (logn 2 8).
Compute (logn 2 10).
Compute (logn 2 20).
Compute (logn 2 21).
Print logn.

(** Hints: logn_gt0 mem_primes dvdn2 *)
Lemma odd_log_eq0 n : 0 < n -> logn 2 n = 0 -> odd n.
Proof.
  move=> oLn. move=> /eqP. apply: contraLR.
  rewrite -lt0n. move=> oddn. rewrite logn_gt0 mem_primes.
  rewrite -dvdn2 in oddn. rewrite oddn oLn //.
Qed.
(* Admitted. *)

(** Hints pfactor_dvdnn logn_div pfactorK *)
Lemma odd_div_log n : 0 < n -> odd (n %/ 2 ^ logn 2 n).
Proof.
  move=> oLn. 
  apply: odd_log_eq0.
    {
      pose proof (pfactor_dvdnn 2 n).
      move: H. move=> /dvdnP H. case: H => [q Hq].
      rewrite {1}Hq mulnK. move: Hq. move: q.
      move=> [|q].
        {
          move=> H. rewrite mul0n in H. subst n.
          rewrite // in oLn.  
        }
        {
          move=> H. rewrite //=. 
        } 
        rewrite expn_gt0. apply /orP.
        left. rewrite //=.
    }
  pose proof (pfactor_dvdnn 2 n). apply (logn_div 2) in H as H'.
  rewrite H'. rewrite [X in _ - X = _]pfactorK.
    rewrite subnn //.
  rewrite //=.
Qed.
(* Admitted. *)

(** Hints divnK pfactor_dvdnn prime_nt_dvdP prime_nt_dvdP *)
Lemma prime_2expS m : 
  0 < m -> prime (2 ^ m).+1 -> m = 2 ^ logn 2 m.
Proof.
(*D*)move=> mP Hp.
(*D*)pose a := 2 ^ logn 2 m.
(*D*)pose b := m %/ a.
(*D*)have : (2 ^ a).+1 %| (2 ^ m).+1. 
(*D*)  rewrite -(divnK (pfactor_dvdnn 2 m)).
(*D*)  rewrite mulnC expnM.
(*D*)apply: dvd_exp_odd; first by apply: expn_gt0.
(*D*)  by apply: odd_div_log.
(*D*)have F : (2 ^ a).+1 != 1.
(*D*)  by rewrite eq_sym neq_ltn ltnS expn_gt0.
(*D*)move=> /(prime_nt_dvdP Hp).
(*D*)move=> /(_ F) [] /eqP.
(*D*)by rewrite eqn_exp2l // => /eqP{1}<-.
(*A*)Qed.
(* Admitted. *)

(** Hints oddX neq_ltn expn_gt0 *)
Lemma odd_fermat n : odd (fermat n).
Proof.
  rewrite /fermat. Search (odd). rewrite -addn1 oddD.
  rewrite oddX.
  have : (2 ^ n == 0) = false.
    elim : n.
      { rewrite //=. }
      { move=> n /eqP Hn. rewrite expnS muln_eq0.
        apply /orP. rewrite /not. move=> H.
        case : H => H.
          move=> //.
        move: H. move=> /eqP H. apply Hn. apply H.
      }
    move=> H. rewrite H //.
Qed.
(* Admitted. *)

(** Hint subn_sqr *)
Lemma dvdn_exp2m1 a k : a.+1 %| (a ^ (2 ^ k.+1)).-1.
Proof.
  elim: k => [|k Ik].
    rewrite expn1 -subn1.
    rewrite -[X in _ %| _ ^ _ - X](exp1n 2) subn_sqr addn1.
    rewrite dvdn_mull //.
    rewrite expnS mulnC. rewrite expnM. rewrite -subn1.
    rewrite -[X in _ %| _ ^ _ - X](exp1n 2).
    rewrite subn_sqr.
    rewrite subn1 dvdn_mulr //.
Qed.
(* Admitted. *)

(** Hints subnK expnD expnM *)
Lemma dvdn_fermat m n : m < n -> fermat m %| (fermat n).-2.
Proof.
  rewrite /fermat. move=> mLn. rewrite -subn2 -[X in _ %| X - 2]addn1.
  rewrite (subnDr 1 _ 1). apply ltnW in mLn as H. apply subnK in H.
  rewrite -H expnD mulnC expnM.
  case Case : (n - m) => [|k].
    Search (_ - _ == 0). move: Case. move=> /eqP Case.
    rewrite subn_eq0 in Case. Search (~~ _ = false).
    apply Bool.negb_false_iff in mLn.
    Search (~~ (_ < _)). rewrite -leqNgt in mLn.
    rewrite Case in mLn. move=> //.
  rewrite subn1. apply dvdn_exp2m1.
Qed.
(* Admitted. *)

Lemma fermat_gt1 n : 1 < fermat n.
Proof.
    rewrite /fermat. elim: n => [ // |k Ik].
    rewrite expnSr. rewrite expnM. 
    (* Search (_ ^ 2). *)
    (* rewrite -mulnn. rewrite -[X in _ < X]addn1. *)
    (* rewrite -[X in _ < X]addn1 in Ik. *)
    have H : (2 ^ 2 ^ k).+1 <= ((2 ^ 2 ^ k) ^ 2).+1.
      {
        apply ltnSE in Ik.
        rewrite ltnS leq_pmulr //.
      }
      rewrite -{1}addn1. rewrite -addn1 in H.
      rewrite -{1}addn1 in Ik. rewrite -[X in _ <= X]addn1 in Ik.
      rewrite -[X in _ <= X]addn1 in H. rewrite -[X in _ <= X]addn1.
      apply: (leq_trans Ik H).
Qed. 
(* Admitted. *)

(** Hints gcdnMDl coprimen2 *)
Lemma coprime_fermat m n : m < n -> coprime (fermat m) (fermat n).
Proof.
  move=> mLn. move: (dvdn_fermat mLn) => mDn.
    rewrite /coprime. move: mDn. move=> /dvdnP mDn.
    case: mDn => q Hq.
    have {}Hq : (fermat n) = (q * fermat m).+2.
      rewrite -Hq. rewrite -addn2 -subn2 subnK // fermat_gt1 //.
      rewrite Hq. rewrite -addn2 gcdnMDl. 
      pose proof (coprimen2 (fermat m)).
      rewrite /coprime in H. rewrite H odd_fermat //.
Qed.
(* Admitted. *)