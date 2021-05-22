Parameter LN : Set.

(* Axiom 1 *)
Parameter L1 : LN.

Theorem one_eq: L1 = L1.
Proof. reflexivity. Qed.

(* Axiom 2 *)
Parameter LS : LN -> LN.

Definition L2 : LN := LS L1.
Definition L3 : LN := LS L2.

Theorem LS_eq (x y : LN) : x = y -> LS x = LS y.
Proof. intros eq. rewrite eq. reflexivity. Qed.

(* Axiom 3 *)
Axiom LS_neq_one : forall x : LN, LS x <> L1.

Example two_neq_one : L2 <> L1.
Proof. unfold L2. apply LS_neq_one. Qed.

(* Axiom 4 *)
Axiom LS_inj : forall x y : LN, LS x = LS y -> x = y.

(* Axiom 5 *)
Axiom LS_ind : forall (P : LN -> Prop),
    P L1 -> (forall x : LN, P x -> P (LS x))
    -> forall x : LN, P x.

(* Theorem 1 *)
Theorem LS_save_neq (x y : LN)
  : x <> y -> LS x <> LS y.
Proof.
  intros neq HC. apply LS_inj in HC.
  contradiction.
Qed.

(* Theorem 2 *)
Theorem LS_neq : forall x : LN, LS x <> x.
Proof.
  apply LS_ind.
  - (* base *) apply two_neq_one.
  - (* step *) intros x IH.
    apply LS_save_neq. assumption.
Qed.

(* Theorem 3 *)
Theorem pred_exists : forall x : LN,
    x <> L1 -> exists ! u : LN, LS u = x.
Proof.
  apply (LS_ind (fun x : LN
                 => x <> L1 -> exists ! u : LN, LS u = x)).
  - (* base *) intros neq. exfalso.
    apply neq. reflexivity.
  - (* step *) intros x IH neq.
    exists x. split; try reflexivity.
    intros y eq. apply LS_inj.
    symmetry. assumption.
Qed.

Parameter sum_is : LN -> LN -> LN -> Prop.

Notation "x + y == z"
  := (sum_is x y z)
       (at level 40, no associativity) : LN_scope.

Open Scope LN_scope.

Axiom sum_one : forall x : LN, x + L1 == LS x.
Axiom sum_LS : forall x y z : LN, x + y == z -> x + LS y == LS z.
(* Axiom sum_uniq : forall x y z1 z2 : LN, *)
(*     x + y == z1 -> x + y == z2 -> z1 = z2. *)

(* Theorem 4 *)
Theorem sum_exists : forall x y, exists z, x + y == z.
Proof.
  intros x. apply LS_ind.
  - exists (LS x). apply sum_one.
  - intros y [z IH]. exists (LS z).
    apply sum_LS. assumption.
Qed.

Theorem sum_eq : forall x y z1 z2 : LN,
    x + y == z1 -> x + y == z2 -> z1 = z2.
Proof.
  intro x.
  apply (LS_ind (fun y => forall z1 z2,
                     x + y == z1 -> x + y == z2 -> z1 = z2)).
  - intros z1 z2 sum1 sum2. admit.
  - intros y IH z1 z2 sum1 sum2.
    (* тут становится ясно, что надо требовать что-то ещё,
       чтобы получилось воспроизвести доказательство из книги *)
Admitted.

Theorem sum_is_fun : forall x y, exists ! z, x + y == z.
Proof.
  intros x y. pose (sum_exists x y) as E.
  destruct E as [z eq]. exists z.
  split; try assumption.
  intro z'. apply sum_eq. assumption.
Qed.

Definition Lsum : forall x y, {z | x + y == z}.
  (* Не понятно, как определить сумму, как функцию, даже если доказано,
     что это функция *)
Admitted.
