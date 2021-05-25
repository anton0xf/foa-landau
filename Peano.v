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

Theorem LN_dec : forall x : LN, x = L1 \/ x <> L1.
Proof.
  apply LS_ind.
  - left. reflexivity.
  - intros x [H | H].
    + right. subst x. apply LS_neq.
    + right. apply LS_neq_one.
Qed.

Parameter Lsum : LN -> LN -> LN.

Declare Scope LN_scope.

Notation "x + y"
  := (Lsum x y)
       (at level 50, left associativity) : LN_scope.

Open Scope LN_scope.

Axiom sum_one : forall x : LN, x + L1 = LS x.
Axiom sum_LS : forall x y : LN, x + LS y = LS (x + y).

Theorem sum_two (x : LN) : x + L2 = LS (LS x).
Proof.
  unfold L2. rewrite sum_LS, sum_one. reflexivity.
Qed.

(* Theorem 4 *)
Theorem sum_exists (x y : LN) : exists z : LN, x + y = z.
Proof. exists (x + y). reflexivity. Qed.

Theorem sum_uniq (x y z1 z2 : LN) : x + y = z1 -> x + y = z2 -> z1 = z2.
Proof. intros H1 H2. subst z1 z2. reflexivity. Qed.

Theorem sum_is_LS (x y : LN) : exists z, x + y = LS z.
Proof.
  generalize dependent y. apply LS_ind.
  - exists x. apply sum_one.
  - intros y H. destruct H as [z H].
    exists (LS z). rewrite sum_LS. apply LS_eq, H.
Qed.

Theorem sum_is_not_one (x y : LN) : ~(x + y = L1).
Proof.
  pose (sum_is_LS x y) as H. destruct H as [z H].
  rewrite H. apply LS_neq_one.
Qed.

Theorem sum_LS_eq (x y z z' : LN)
  : x + y = z -> x + LS y = z' -> z' = LS z.
Proof.
  intros sum sum'. subst z z'. apply sum_LS.
Qed.

Theorem sum_eq (x y z1 z2 : LN) : x + y = z1 -> x + y = z2 -> z1 = z2.
Proof.
  intros H1 H2. subst z1 z2. reflexivity.
Qed.

Theorem fun_is_fun (A : Type) (f : A -> A) (x : A)
  : exists ! y, f x = y.
Proof.
  exists (f x). split; try reflexivity.
  intros y' H. subst y'. reflexivity.
Qed.

Theorem sum_is_fun : forall x y, exists ! z, x + y = z.
Proof.
  intros x y. apply (fun_is_fun LN (Lsum x) y).
Qed.

Theorem sum_LS_comm (x y z : LN) : x + LS y = z -> LS x + y = z.
Proof.
  generalize dependent z.
  generalize dependent x.
  generalize dependent y.
  apply (LS_ind (fun y => forall x z, x + LS y = z -> LS x + y = z)).
  - intros x z H. subst z. rewrite sum_two, sum_one. reflexivity.
  - intros y IH x z H. subst z. repeat rewrite sum_LS.
    apply LS_eq, IH. rewrite sum_LS. reflexivity.
Qed.
