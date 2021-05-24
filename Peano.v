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

Parameter sum_is : LN -> LN -> LN -> Prop.

Declare Scope LN_scope.

Notation "x + y == z"
  := (sum_is x y z)
       (at level 40, no associativity) : LN_scope.

Open Scope LN_scope.

Axiom sum_one : forall x : LN, x + L1 == LS x.
Axiom sum_one_uniq : forall x z1 z2 : LN,
    x + L1 == z1 -> x + L1 == z2 -> z1 = z2.

Axiom sum_LS : forall x y z : LN, x + y == z -> x + LS y == LS z.
Axiom sum_LS_uniq : forall x y z1 z2 : LN,
    x + LS y == z1 -> x + LS y == z2 -> z1 = z2.

Theorem sum_one_inv (x z : LN) : x + L1 == z -> z = LS x.
Proof.
  intro H. apply (sum_one_uniq x z (LS x) H), sum_one.
Qed.

Theorem sum_two (x : LN) : x + L2 == LS (LS x).
Proof. apply sum_LS, sum_one. Qed.

Theorem sum_two_inv (x z : LN) : x + L2 == z -> z = LS (LS x).
Proof.
  intro H. apply (sum_LS_uniq x L1 z (LS (LS x)) H).
  apply sum_LS, sum_one.
Qed.

Theorem sum_exist (x y : LN) : exists z : LN, x + y == z.
Proof.
  generalize dependent x.
  generalize dependent y.
  apply (LS_ind (fun y => forall x, exists z : LN, x + y == z)).
  - intro x. exists (LS x). apply sum_one.
  - intros y IH x. destruct (IH x) as [z H].
    exists (LS z). apply sum_LS, H.
Qed.

Theorem sum_uniq (x y z1 z2 : LN) : x + y == z1 -> x + y == z2 -> z1 = z2.
Proof.
  destruct (LN_dec y) as [H | H].
  - subst y. apply sum_one_uniq.
  - apply pred_exists in H. destruct H as [y' [H U]].
    subst y. apply sum_LS_uniq.
Qed.

Theorem sum_exist_and_not_one (x y : LN)
  : exists z : LN, x + y == z /\ z <> L1.
Proof.
  generalize dependent x.
  generalize dependent y.
  apply (LS_ind (fun y => forall x, exists z : LN, x + y == z /\ z <> L1)).
  - intro x. exists (LS x). split.
    + apply sum_one.
    + apply LS_neq_one.
  - intros y IH x. destruct (IH x) as [z [H neq]].
    exists (LS z). split.
    + apply sum_LS, H.
    + apply LS_neq_one.
Qed.

Theorem sum_is_not_one (x y : LN) : ~(x + y == L1).
Proof.
  pose (sum_exist_and_not_one x y) as H.
  destruct H as [z [sum neq]].
  intro C. apply neq. apply (sum_uniq x y); assumption.
Qed.

Theorem sum_LS_eq (x y z z' : LN)
  : x + y == z -> x + LS y == z' -> z' = LS z.
Proof.
  intros sum sum'.
  apply (sum_LS_uniq x y z' (LS z) sum').
  apply sum_LS, sum.
Qed.

Theorem sum_LS_inv (x y z : LN) : x + LS y == LS z -> x + y == z.
Proof.
  generalize dependent z.
  generalize dependent x.
  generalize dependent y.
  apply (LS_ind (fun y => forall x z, x + LS y == LS z -> x + y == z)).
  - intros x z H. apply sum_two_inv in H.
    apply LS_inj in H. subst z. apply sum_one.
  - intros y IH x z' H.
    pose (sum_exist x (LS y)) as sum.
    destruct sum as [z sum]. apply sum_LS in sum as sum'.
    pose (sum_LS_uniq x (LS y) (LS z') (LS z) H sum') as eq.
    apply LS_inj in eq. subst z'. assumption.
Qed.

(* Theorem 4 *)
Theorem sum_exists : forall x y, exists z, x + y == z.
Proof.
  intros x. apply LS_ind.
  - exists (LS x). apply sum_one'.
  - intros y [z IH]. exists (LS z).
    apply sum_LS'. assumption.
Qed.

Theorem sum_eq (x y z1 z2 : LN) : x + y == z1 -> x + y == z2 -> z1 = z2.
Proof.
  generalize dependent z2.
  generalize dependent z1.
  generalize dependent y.
  apply (LS_ind (fun y => forall z1 z2,
                     x + y == z1 -> x + y == z2 -> z1 = z2)).
  - intros z1 z2 sum1 sum2.
    apply sum_one_inv in sum1, sum2.
    subst z1 z2. reflexivity.
  - intros y IH z1 z2 sum1 sum2.
    apply sum_neq_L1 in sum1 as H1.
    apply sum_neq_L1 in sum2 as H2.
    apply pred_exists in H1 as [z1' [eq1 _]].
    apply pred_exists in H2 as [z2' [eq2 _]].
    subst z1 z2.
    apply sum_LS_inv in sum1, sum2.
    apply LS_eq, IH; assumption.
Qed.

Theorem sum_is_fun : forall x y, exists ! z, x + y == z.
Proof.
  intros x y. pose (sum_exists x y) as E.
  destruct E as [z eq]. exists z.
  split; try assumption.
  intro z'. apply sum_eq. assumption.
Qed.

Theorem sum_LS_comm (x y z : LN) : x + LS y == z -> LS x + y == z.
Proof.
  generalize dependent z.
  generalize dependent x.
  generalize dependent y.
  apply (LS_ind (fun y => forall x z, x + LS y == z -> LS x + y == z)).
  - intros x z H. apply sum_two_inv in H. subst z. apply sum_one.
  - intros y IH x z H. (* apply sum_LS. rewrite <- IH. *)
Admitted.

Theorem sum_neq_L1 (x y z : LN) : x + y == z -> z <> L1.
Proof.
  intro H. pose (LN_dec y) as D.
  destruct D as [D | D].
  - subst y.
Admitted.

Definition Lsum : forall x y, {z | x + y == z}.
  (* Не понятно, как определить сумму, как функцию, даже если доказано,
     что это функция *)
Admitted.
