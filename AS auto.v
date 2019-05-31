From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat ssrfun 
eqtype seq choice fintype.
Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ====================================== *)
(* Множество (вычислительное определение) *)
(* ====================================== *)
Section BSet. 

Variable T : Type.

  Inductive BSet : Type :=
    | Empty : BSet
    | Elem : T -> BSet -> BSet
    .

  Axiom Ident1 : forall (s : BSet) (x : T), Elem x (Elem x s) = Elem x s.
  Axiom Ident2 : forall (s : BSet) (x y : T),
                         Elem x (Elem y s) = Elem y (Elem x s).

  Fixpoint power (s : BSet) : nat :=
    match s with
      | Empty => 0
      | Elem _ sub => 1 + (power sub)
    end.

End BSet. 

(* Сравнительный тип *)
Section BSetEqType.

  Variable T : eqType.

  Fixpoint In (x : T) (s : BSet T) : bool := 
    match s with
      | Empty => false
      | Elem y sub => (x == y) || (In x sub)
    end.

  Definition AddBSet (x : T) (s : BSet T) :=
    match (In x s) with
      | true => s
      | false => Elem x s
    end.

  Fixpoint SubBSet (s : BSet T) (x : T) :=
    match s with
      | Empty => s
      | Elem y s' => 
        match x == y with
          | true => (SubBSet s' x)
          | false => AddBSet y (SubBSet s' x)
        end
    end.

  Definition notIn (x : T) (s : BSet T) : bool :=
    (In x s) == false.

  Fixpoint subseteq (s1 s2 : BSet T) := 
    match s1 with
    | Empty => true
    | Elem x sub => (In x s2) && (subseteq sub s2)
    end.

  Definition supseteq (s1 s2 : BSet T) :=
    subseteq s2 s1.

End BSetEqType.

Arguments Empty [T].

(* Нотация для множества *)
Module BSetNotation.
  Notation "{ # }" := Empty.
  Notation "{ # x }" := (Elem x { # }).
  Notation "{ # x ; y ; .. ; z }" := (Elem x (Elem y  .. (Elem z { # }) ..)).
  Notation "| s |" := (power s) (at level 34).
  Notation "x /in s" := (In x s) (at level 43, left associativity).
  Notation "x /~in s" := (notIn x s) (at level 43, left associativity).
  Notation "s1 [= s2" := (subseteq s1 s2) (at level 43, left associativity).
  Notation "s1 ]= s2" := (supseteq s1 s2) (at level 43, left associativity).
  Notation "s \ x" := (SubBSet s x) (at level 43, left associativity).
  Notation "x =>> s" := (AddBSet x s) (at level 43, left associativity).
End BSetNotation.

Import BSetNotation.

(* Секция проверок *)
Check (Empty).
Check (Elem 3 Empty).
Check (Elem 3 (Elem 4 Empty)).
Check (Elem 3 (Elem 4 (Elem 5 Empty))).
 
Check ({ # }).
Check ({# 3}).
Check ({# 3; 4}).
Check ({# 3; 4; 5}).
Check ({# 3; 4; 1; 7}).

(* Секция вычислений *)
Eval compute in (|{ # }|).
Eval compute in (|{# 3}|).
Eval compute in (|{# 3; 4}|).
Eval compute in (|{# 3; 4; 5}|).
Eval compute in (|{# 3; 4; 1; 7}|).

Eval compute in (7 /in { # }).
Eval compute in (7 /in {# 7}).
Eval compute in (7 /in {# 3}).
Eval compute in (7 /in {# 7; 3}).
Eval compute in (7 /in {# 4; 7}).
Eval compute in (7 /in {# 4; 7; 6}).
Eval compute in (7 /in {# 4; 6; 9}).

Eval compute in (7 /~in {# 4; 7; 6}).
Eval compute in (7 /~in {# 4; 6; 9}).

Eval compute in ({ # } [= { # }).
Eval compute in ({ # } [= { # 3 }).
Eval compute in ({ # 3 } [= { # 4; 3}).
Eval compute in ({ # 3 } [= { # 4; 5}).
Eval compute in ({ # 7; 2; 6} [= { # 4; 8; 2; 0; 6; 1; 7; 5}).

Eval compute in ({ # } ]= { # }).
Eval compute in ({ # 3 } ]= { # }).
Eval compute in ({ # 4; 3 } ]= { # 3 }).
Eval compute in ({ # 4; 5 } ]= { # 3 }).
Eval compute in ({ # 4; 8; 2; 0; 6; 1; 7; 5} ]= { # 7; 2; 6}).

Eval compute in (3 =>> { # }).
Eval compute in (3 =>> { # 1 }).
Eval compute in (3 =>> { # 3 }).
Eval compute in (3 =>> { # 1; 3 }). 
Eval compute in (3 =>> { # 1; 2 }).

Eval compute in ({ # } \ 3).
Eval compute in ({ # 1 } \ 3).
Eval compute in ({ # 3 } \ 3).
Eval compute in ({ # 1; 3 } \ 3).
Eval compute in ({ # 1; 2 } \ 3).
Eval compute in ({ # 1; 3; 4; 3 } \ 3).

(* ====================================== *)
(* Множество (структурное определение) *)
(* ====================================== *)

(* Определение множества для произвольного типа *)
Section SetS.

  Variable T : Type.
  
  (* Множество *)
  Structure SetS := 
  {
    As :> BSet T;
  }.

  Check (SetS).

  (* Пустое множество *)
  Structure ESetS :=
  {
    Aes :> BSet T;

    power_cond : forall (s : BSet T), |s| = 0
  }.

  Structure group :=
  {
    G :> Set;

    id : G;
    op : G -> G -> G;
    inv : G -> G;

    op_assoc : forall (x y z : G), op x (op y z) = op (op x y) z;
    op_inv_l : forall (x : G), id = op (inv x) x;
    op_id_l : forall (x : G), x = op id x
  }.

  Check (id).
  Check (op).
  Check (inv).

  Arguments id {g}.
  Arguments op {g} _ _.
  Arguments inv {g} _.

  Check (id).
  Check (op).
  Check (inv).

  Notation "x $ y" := (op x y) (at level 50, left associativity).

  Check (op_id_l).
End SetS.

(* Множество для типов сравнения *)
Section SetSEqType.

  Variable T : eqType.

  Lemma falseP : False -> false.
  Proof.
    done.
  Qed.

  Ltac andT :=
    let V1 := fresh "V1" in 
      case: andP => /= //;
      unfold not => V1; apply: falseP;
      apply: V1.

  Ltac orT := 
    let V1 := fresh "V1" in 
      case: orP => /= //;
      unfold not => V1; try apply: falseP;
      apply: V1.

  Ltac eqT H := 
    move: H; case: eqP => // H _.

  Ltac andH  H :=
    let H' := fresh "H'" in
    let H'' := fresh "H''" in
    case: andP H => /= // H H''; destruct H as [H H'] => /= //.

  Ltac orH H :=
    let H' := fresh "H'" in
    case: orP H => /= // H H'; destruct H as [H | H] => /= //.

  Ltac rewriteA :=
  match goal with
    | H  : _ |- _ => rewrite H; rewriteA
    | _ => idtac
 end.

  Ltac applyA :=
  match goal with
    | H  : _, H2 : _ |- _ => apply H in H2; applyA
    | _ => idtac
  end.

  Ltac matchT := 
    repeat (multimatch  goal with
      | |- context [ if ?P then _ else _ ] => 
        match P with
        | context[ _ == _ ]  => case: eqP
        | _ => destruct P
        end
      | |- context [ AddBSet ] => unfold AddBSet  (* + *)
      | |- _ /\ _ => split                        (* + *)
      | |- context [ _ <-> _ ]  => split          (* + *)
      | |- context [ _ || _ ] => orT              (* + *)
      | |- context [ _ && _ ] => andT             (* + *)
      | H : _ \/ _ |- _ => destruct H             (* + *)
      | H : _ /\ _ |- _ => destruct H             (* + *)
      | H : context [ _ || _ ] |- _ => orH H      (* + *)
      | H : context [ _ && _ ] |- _ => andH H     (* + *)
      | H : context [ _ == _ ] |- _ => eqT H      (* + *)
      | H : context[ true ] |- _ => clear H       (* + *)
      | H : ?P = ?Q, H' : ?Q = ?P |- _ => clear H' (* + *)
      | H : ?P, H' : ?P |- _ => clear H'          (* + *)
      | H : ?x = _ |- context[?x] => rewrite H    (* + *)
      | H : ?x = _, H' : context[?x] |- _ => rewrite H in H' (* + *)
      | H : forall _, _ |- _ => rewrite H
      | H : ?P |- _ \/ ?P => right                 (* + *)
      | H : ?P |- ?P \/ _ => left                  (* + *)
      | H : _ -> ?P |- ?P => apply H
      | |- _ \/ _ => do [by left | by right]       (* + *)
      | |- context [ not ] => unfold not           (* + *)
      | |- context [ notIn ] => unfold notIn       (* + *)
      | H : context [ not ] |- _ => unfold not in H  (* + *)
      | H : context [ notIn ] |- _ => unfold notIn  (* + *)
      | |- context [ is_true(?P) \/ is_true(?P == false) ] => destruct P (* + *)
      | |- context [ is_true(?P == false) \/ is_true(?P) ] => destruct P (* + *)
      | |- context [ Elem ?x (Elem ?x _) ] => by rewrite Ident1
      | |- context [ Elem ?x (Elem ?y _) ] => by rewrite Ident2
    end) => /= //; try intros.

    Ltac matchT' := 
    repeat (multimatch  goal with
      | |- context [ AddBSet ] => unfold AddBSet  (* + *)
      | |- _ /\ _ => split                        (* + *)
      | |- context [ _ <-> _ ]  => split          (* + *)
      | |- context [ _ || _ ] => orT              (* + *)
      | |- context [ _ && _ ] => andT             (* + *)
      | H : _ \/ _ |- _ => destruct H             (* + *)
      | H : _ /\ _ |- _ => destruct H             (* + *)
      | H : context [ _ || _ ] |- _ => orH H      (* + *)
      | H : context [ _ && _ ] |- _ => andH H     (* + *)
      | H : context [ _ == _ ] |- _ => eqT H      (* + *)
      | H : context[ true ] |- _ => clear H       (* + *)
      | H : ?P, H' : ?P |- _ => clear H'          (* + *)
      | H : ?P |- _ \/ ?P => right                 (* + *)
      | H : ?P |- ?P \/ _ => left                  (* + *)
      | |- _ \/ _ => do [by left | by right]       (* + *)
      | |- context [ not ] => unfold not           (* + *)
      | |- context [ notIn ] => unfold notIn       (* + *)
      | H : context [ not ] |- _ => unfold not in H  (* + *)
      | H : context [ notIn ] |- _ => unfold notIn  (* + *)
      | |- context [ is_true(?P) \/ is_true(?P == false) ] => destruct P (* + *)
      | |- context [ is_true(?P == false) \/ is_true(?P) ] => destruct P (* + *)
    end) => /= //; try intros.

  Ltac baseT := 
    try elim => /= //; intros => /= //;
    repeat matchT.

  Ltac tacQ := 
    try elim => /= //; intros => /= //;
    repeat matchT'.

  Ltac baseT' :=
    try intros => /= //;
    repeat matchT.

  Ltac caseT := 
    try repeat case => /= //;
    repeat matchT.

  Lemma L1 : forall s : SetS T, |s| = |s|.
  Proof. 
    baseT.
  Qed.

  Check (SetS).
  Check ({# 3}).

  Lemma L2 : forall s : ESetS T, |s| = 0.
  Proof. 
    caseT.
  Qed.

  Lemma L3 : forall s : BSet T, s = Empty <-> | s | = 0.
  Proof. 
    baseT. 
  Qed.

  Lemma L4 : forall s : ESetS T, Aes s = Empty.
  Proof. 
    case => s' cond. pose (H := cond s').  
    by move: H; rewrite <- L3 => ->.
  Qed.

  Lemma L5 : forall (s1 : ESetS T) (s2 : SetS T), s1 [= s2.
  Proof. 
    baseT.
     - by rewrite L4.
  Qed.

  Theorem T1 : forall (s1 : SetS T) (s2 : ESetS T), |s1| = 0 -> As s1 = Aes s2.
  Proof. 
    move => s1 s2. rewrite <- L3 => H.
    by rewrite H L4.
  Qed.

  Lemma L6 : forall (s1 s2 : BSet T) (x : T), s1 [= s2 -> s1 [= Elem x s2.
  Proof. 
    baseT.
  Qed.

  Theorem T2 : forall (s : BSet T), s [= s.
  Proof.
    baseT.
    - by apply: L6.
  Qed.

  Theorem T2' : forall (s : SetS T), s [= s.
  Proof.
    by case => s; apply T2.
  Qed.

  Lemma L12 : forall (s1 s2 : BSet T) (x : T), Elem x s1 [= s2 -> s1 [= s2.
  Proof.
    baseT.
  Qed.

  Lemma L13 : forall (s1 s2 : BSet T) (x : T), x /in s1 -> s1 [= s2 -> x /in s2.
  Proof.
    baseT.
  Qed.

  Theorem T4 : forall (s1 s2 s3 : BSet T), s1 [= s2 -> s2 [= s3 
               -> s1 [= s3.
  Proof.
    baseT.
    - by apply L13 with (x := t) in H1.
    - by apply H in H1.
  Qed.

  Lemma L9 : forall (s : BSet T) (x : T),
             x /in s -> s = Elem x s.
  Proof. 
    baseT.
    rewrite Ident2; by apply H in H0; rewrite <- H0.
  Qed.

  Lemma L10 : forall (s : BSet T) (x : T), s [= { # x } -> 
              or (s = { # }) (s = { # x }).
  Proof.
    baseT.
    - apply H in H'. baseT'.
      - by right; rewrite Ident1.
  Qed.

  Lemma EL1 : forall (s1 s2 : BSet T) (x : T), x /in s1 -> s1 [= s2 
               <-> Elem x s1 [= s2.
  Proof.
    baseT.
    apply H'' with (x := x) in H'0; baseT.
  Qed.

  Lemma EL2 : forall (s1 s2 : BSet T) (x : T), x /in s2 -> s1 [= s2
              -> Elem x s1 [= s2.
  Proof.
    baseT.
  Qed.

  Lemma EL3 : forall (s1 s2 : BSet T) (x : T), s1 = s2 -> Elem x s1 = Elem x s2.
  Proof.
    baseT.
  Qed.

  (* ================================================== *)
  (* Каноничное сравнение для множеств *)
  (* ================================================== *)

  Fixpoint eqBSet (s1 s2 : BSet T) := 
    (subseteq s1 s2) && (subseteq s2 s1).

  Lemma EL4 : forall (x : T), eqBSet {# x; x} {# x}.
  Proof.
    baseT.
  Qed.

  Lemma EL5 : forall (s : BSet T) (x : T), x /in s -> s [= {# x}
              -> s = {# x}.
  Proof.
    baseT.
    - by apply L10 in H';
      baseT'; rewrite Ident1.
    - by apply H in H' => //;
      rewrite <- L9.
  Qed.

  Lemma EL7 : forall (s : BSet T) (x : T), or (x /in s) (x /~in s).
  Proof.
    baseT.
  Qed.

  Lemma EL8 : forall (s1 s2 : BSet T) (x : T), s1 [= Elem x s2
              -> s1 \ x [= s2.
  Proof.
    baseT.
  Qed.

  Lemma EL10''' : forall (s : BSet T) (x y : T), 
                  Elem x (y =>> s) = (y =>> (Elem x s)).
  Proof.
    baseT.
  Qed.

  Lemma EL10'' : forall (s : BSet T) (x : T), (Elem x s) = (x =>> s).
  Proof. 
    elim => /= //.
    move => y s iH x. rewrite <- EL10'''. rewrite Ident2.
    by apply EL3.
  Qed.

  Lemma EL10' : forall (s : BSet T) (x : T), Elem x (s \ x) = Elem x s.
  Proof. 
    elim => /= //.
    move => y s iH x. remember (x == y) as cond eqn: H1.
    destruct cond => /= //.
    - rewrite iH. eqT H1. rewrite <- H1. by rewrite Ident1.
    - rewrite <- EL10''. rewrite Ident2. rewrite <- Ident2 with (s := s).
      apply EL3. apply iH.
  Qed.

  Lemma EL10 : forall (s : BSet T) (x : T), x /in s -> Elem x (s \ x) = s.
  Proof. 
    elim => /= //.
    move => y s iH x H1.
    case: orP H1 => /= // H1 _; destruct H1 as [H1 | H1] => /= //.
    - eqT H1. rewrite <- H1. apply EL10'.
    - apply iH in H1. assert ((x == y) || ((x == y) == false)).
      destruct (x == y) => /= //.
      case: orP H => /= // H _; destruct H as [H | H] => /= //.
      - eqT H. rewrite <- H. apply EL10'.
      - destruct (x == y). inversion H. 
        rewrite <- EL10''. rewrite Ident2.
        by apply EL3.
  Qed.

  Ltac rewT := 
    match goal with
    | H : _ = ?x |- context [?x] => rewrite <- H
    end.

  Lemma EL11 : forall (s1 s2 : BSet T) (x : T), Elem x s1 = s2 -> x /in s2.
  Proof. 
    caseT; do [inversion H; baseT].
  Qed.

  Lemma EL9' : forall (s : BSet T) (x : T), x /in Elem x s.
  Proof.
    case => /= // [x| y s x]; by orT; left.
  Qed.

  Lemma EL13 : forall (s : BSet T) (x y : T), x /in s -> x /in Elem y s.
  Proof.
    case => /= //. move => a s x y H1.
    orT. case: orP H1 => /= // H1 _; destruct H1 as [H1 | H1]; by right.
  Qed.

  Lemma EL9''' : forall (s : BSet T) (x y : T), (x == y) = false -> 
                 x /in s -> x /in (s \ y).
  Proof.
    elim => /= //. move => a s iH x y H1 H2.
    case: orP H2 => /= // H2 _; destruct H2 as [H2 | H2].
    - eqT H2. rewrite <- H2. eqT H1. case: eqP => /= // H3.
      - rewrite H3 in H1. assert (False -> x /in (s \ y)) => //.
      - rewrite <- EL10''. apply EL9'.
    - apply iH with (x := x) (y := y) in H2 => /= //.
      remember (y == a) as cond eqn: H3. destruct cond => /= //.
      rewrite <- EL10''. by apply EL13.
  Qed.

  Lemma EL9'' : forall (s : BSet T) (x y : T), x /~in Elem y s -> x /~in s.
  Proof.
    case => /= //. move => a s x y H1.
    unfold notIn. case: eqP => /= // H2.
    unfold notIn in H1. eqT H1. rewrite <- H1.
    destruct H1. case: orP H2 => /= // H2 H3.
    - destruct H2 as [H1 | H1]. eqT H1. by orT; right.
    - by orT; right; orT; right. 
      have: forall (u v : bool), (u <> v) -> (v <> u). intuition.
      move => H4. apply H4 in H3. 
      by apply not_false_iff_true in H3.
  Qed. 

  Lemma EL9 : forall (s1 s2 : BSet T) (x : T), x /~in s1 -> s1 [= s2
              -> s1 [= (s2 \ x).
  Proof.
    elim => /= //.
    move => y s1 iH s2 x H1 H2.
    case: andP H2 => /= // H2 _; destruct H2 as [H2 H3].
    andT. remember (x == y) as cond eqn: H4. destruct cond.
    - eqT H4. rewrite <- H4 in H1. unfold notIn in H1.
      rewrite EL9' in H1. inversion H1. 
    - apply EL9'' in H1 => //. apply iH with (x := x) in H3 => /= //.
      split => /= //. apply EL9''' => //. eqT H4. case: eqP => // H5.
      rewrite H5 in H4. done.
  Qed.

  Ltac recAp t H := 
    apply EL3 with (x := t) in H; rewrite EL10 in H; 
    do [by baseT | by rewrite Ident2; baseT].

  Lemma EL12 : forall (s1 s2 : BSet T) (x : T), s1 [= s2 -> s2 [= Elem x s1
              -> or (s2 = s1) (s2 = Elem x s1).
  Proof.
    baseT.
    - by apply L10.
    - move: EL7 => H4. pose (H5 := H4 b t); baseT.
      - rewrite <- L9 with (s := b) in H1 => //.
        apply H in H1; baseT.
        - by apply L9 in H2; left.
        - by apply L9 in H0; rewrite Ident2 in H0; right. 
      - rewrite Ident2 in H1. apply EL8 in H1.
        apply EL9 with (x := t) in H' => //.
        apply H in H1; baseT; recAp t H1.
  Qed.

  Theorem T3_1 : forall (s1 s2 : BSet T), s1 [= s2 -> s2 [= s1
               -> s1 = s2.
  Proof.
    caseT. apply EL12 in H0; baseT.
    by rewrite <- L9.
  Qed.

  Theorem T3_2 : forall (s1 s2 : BSet T), s1 = s2 -> (s1 [= s2
               /\ s2 [= s1).
  Proof.
    caseT; try apply T2.
    - by apply EL11 in H.
    - rewrite <- H. apply L6.
      by apply T2.
  Qed.

  Lemma eqBSetP : Equality.axiom eqBSet.
  Proof. 
    caseT; try by constructor.
    - case: andP; constructor. 
      - baseT. apply EL2 with (x := t) in H' => //.
        by apply T3_1 in H'.
      - move => H1; apply n.
        by apply T3_2 in H1.
  Qed. 

  Canonical BSet_eqMixin := EqMixin eqBSetP.
  Canonical BSet_eqType := Eval hnf in EqType (BSet T) BSet_eqMixin.

  Lemma eqBSetE : eqBSet = eq_op.
  Proof.
    baseT.
  Qed.

  Definition subset (s1 s2 : BSet T) :=
    (subseteq s1 s2) && (s1 != s2).

  Definition supset (s1 s2 : BSet T) :=
    subset s2 s1.

  (* ================================================== *)
  (* ================================================== *)

End SetSEqType. 

(* Нотация для множества *)
Module BSetNotation2.
  Notation "s1 /[  s2" := (subset s1 s2) (at level 43, left associativity).
  Notation "s1 /]  s2" := (supset s1 s2) (at level 43, left associativity).
End BSetNotation2.

Import BSetNotation2.

Eval compute in ({ # } /] { # }).
Eval compute in ({ # 3 } /] { # }).

Eval compute in ({ # 4; 8; 2; 0; 6; 1; 7; 5} == { # 4; 8; 2; 0; 6; 1; 7; 5}).
Eval compute in ({ # 4; 7; 2; 0; 6; 1; 7; 5} == { # 4; 8; 2; 0; 6; 1; 7; 5}).
Eval compute in ({ # 4; 7; 2; 0; 6; 1; 7; 5} == { # 4; 2; 0; 6; 1; 7; 5}).
Eval compute in ({ # } == { # }).
Eval compute in ({ # } == { # 1 }).
Eval compute in ({ # 1 } == { # 2 }).
Eval compute in ({ # 1; 1; 1} == { # 1}).
Eval compute in ({ # 1; 2; 3; 1; 2} == { # 2; 1; 1; 3}).
Eval compute in ({ # 1; 2; 3; 1; 2} == { # 2; 1; 1 }).


















