From Coq Require Import List Arith Lia.
Import ListNotations. 
Require Import Coq.Lists.List.
 
 
Section Paper.

Context {S : Type}.
Variable n : nat. (** Comment - Anzahl der Klassen *)
Variable e : nat. (** Comment - epsilon *)

(** Definition 1: Classifier *)
Record classifier : Type := {
  classifier_fun   :> S -> nat;
  classifier_range : forall x, classifier_fun x < n;
  classifier_surj  : forall i, i < n -> exists x, classifier_fun x = i
}.

Definition subset := S -> Prop.

Definition class (c : classifier) (i : nat) : subset :=
  fun x => c x = i.

Definition classes (c : classifier) : list subset :=
  map (class c) (seq 0 n).

(** Definition 2: Distance *)
Record distance_function : Type := {
  distance_function_fun   :> S -> S -> nat;
  distance_function_refl : forall x : S, distance_function_fun x x = 0
}.

(** Definition 3: Local Robustness *)
Definition locally_robust_classifier(x : S) (c : classifier) (d : distance_function) : Prop :=
  forall y : S, d x y <= e -> c x = c y.

(** Definition 4: Global Robustness *)
Definition globally_robust_classifier(c : classifier) (d : distance_function) : Prop :=
  forall x : S, locally_robust_classifier x c d.

(** Definition 5: Partition
Record partition (P : list subset) : Prop := {
  partition_nonempty : forall A, In A P -> exists x, A x;
  partition_cover    : forall x, exists A, In A P /\ A x;
  partition_disjoint : forall A B, In A P -> In B P -> A <> B -> forall x, ~(A x /\ B x)
}. *)


(** Definition 5: Partition *)
Record partition : Type := {
  parts : list subset;
  part_nonempty : forall A, In A parts -> exists x, A x;
  part_cover    : forall x, exists A, In A parts /\ A x;
  part_disjoint : forall A B, In A parts -> In B parts -> A <> B -> forall x, ~(A x /\ B x)
}.


Definition induced_partition (c : classifier) : partition.
  Proof.
    refine ({| parts := classes c |}).
    - (* nonempty *)
      intros A H_in.
      unfold classes in H_in.
      apply in_map_iff in H_in.
      destruct H_in as [i [HAi Hi_seq]].
      subst A.
      unfold class.
      apply in_seq in Hi_seq as [_ Hi_lt_n].
      destruct (classifier_surj c i Hi_lt_n) as [x Hx].
      exists x. exact Hx.
      
    - (* cover *)
      intros x.
      exists (class c (c x)).
      split.
      + unfold classes.
        apply in_map.
        apply in_seq. split; auto with arith.
        apply classifier_range.
      + unfold class. reflexivity.
      
    - (* disjoint *)
      intros A B HA HB HAB x [HAx HBx].
      unfold classes in HA, HB.
      apply in_map_iff in HA.
      apply in_map_iff in HB.
      destruct HA as [i [H_A_i H_i_in]].
      destruct HB as [j [H_B_j H_j_in]].
      subst A B.
      unfold class in HAx, HBx.
      rewrite HAx in HBx.
      contradiction HAB.
      subst; reflexivity.
    Defined.

(** Theorem 1: A classifier induces a partition *)
Lemma classifier_induces_partition (c : classifier) : partition.
Proof.
  exact (induced_partition c).
Qed.

(** Class to Corresponding Part *)
Lemma class_to_part
      (c : classifier) (i : nat) : i < n -> In (class c i) (parts (induced_partition c)).
Proof.
  intros H_lt.
  unfold induced_partition.
  unfold classes.
  apply in_map.
  apply in_seq; lia.
Qed.

(** Part to Corresponding Class *)
Lemma part_to_class
      (c : classifier) (A : subset) : In A (parts (induced_partition c)) -> exists i : nat, i < n /\ A = class c i.
Proof.
  intros H_in.
  unfold induced_partition in H_in; simpl in H_in.
  unfold classes in H_in.
  apply in_map_iff in H_in as [i [H_eq H_i_seq]].
  exists i; split.
  - apply in_seq in H_i_seq; lia.
  - symmetry; exact H_eq.
Qed.


(* Definition 6: ε-Ball *)
Definition e_ball (dist_func : distance_function) (x : S) : S -> Prop :=
  fun y => dist_func y x <= e.


(* Definition 7: Global Robustness on a Partition *)
Definition globally_robust_partition (p : partition) (d : distance_function) : Prop :=
  forall x : S, exists A, In A (parts p) /\ (forall y, e_ball d x y -> A y).



(** Theorem 2.a (->): Equivalence of Definitions - Globally Robust Classifier Induces Globally Robust Partition *)
Lemma glob_rob_classifier_induces_glob_rob_partition :
  forall (c : classifier) (d : distance_function),
    globally_robust_classifier c d ->
    globally_robust_partition (induced_partition c) d.
Proof.
  intros c d H_glob_rob x.
  (* Find the class induced by classifier label at x (from partitions) *)
  set (A := class c (c x)).
  exists A.
  split. 
  - (* A in induced_partition c *)
    unfold induced_partition.
    apply in_map.
    apply in_seq.
    split.
    + lia.
    + apply classifier_range.
  - (* e-ball around x is contained in A *)
    intros y H_ball.
    unfold A, class.
    apply H_glob_rob.
    exact H_ball.
Qed.


(** Theorem 2.b (<-): Equivalence of Definitions - If Induced Partition is Globally Robust Classifier Is Globally Robust *)
Lemma induced_partition_glob_rob_then_classifier_glob_rob :
  forall (c : classifier) (d : distance_function),
    globally_robust_partition (induced_partition c) d -> globally_robust_classifier c d.
Proof.
  intros c d H_partition_glob x y H_dist.
  unfold globally_robust_partition in H_partition_glob.
  destruct (H_partition_glob y) as [A [H_A_in_parts H_ball_in_A]].

  (* x and y are both in A *)
  assert (H_y_in_A : A y).
  { apply H_ball_in_A.
    unfold e_ball.
    rewrite distance_function_refl; apply le_0_n. }

  assert (H_x_in_A : A x).
  { apply H_ball_in_A.
    unfold e_ball; exact H_dist. }

  (* 3. Identify the concrete block A: it must be some class c i. *)
  unfold induced_partition in H_A_in_parts.
  destruct (part_to_class c A H_A_in_parts)
        as [i [_ H_A_eq]].
  subst A.

  (* 4. Translate membership into label equalities and conclude. *)
  unfold class in H_x_in_A, H_y_in_A.
  rewrite H_x_in_A, H_y_in_A.
  reflexivity.
Qed.


(** Theorem 2: Equivalence of Definitions - Induced Partition is Globally Robust IFF Classifier Is Globally Robust *)
Lemma induced_partition_glob_rob_iff_classifier_glob_rob :
  forall (c : classifier) (d : distance_function),
    globally_robust_classifier c d <-> globally_robust_partition (induced_partition c) d.
Proof.
  intros c d.
  split.
  - apply glob_rob_classifier_induces_glob_rob_partition.
  - apply induced_partition_glob_rob_then_classifier_glob_rob.
Qed.

Definition robust_partition
           (p : partition) (d : distance_function) : Prop :=
  forall A B : subset,
    In A (parts p) ->
    In B (parts p) ->
    A <> B ->
    forall a b, A a -> B b -> e < d a b.


Lemma global_robustness_iff_separability :
  forall (c : classifier) (d : distance_function),
    globally_robust_classifier c d  <->
    robust_partition (induced_partition c) d.
Proof.
  intros c d; split.

  (* ------------------------------------------------------------------ *)
  (* (→) globally-robust classifier ⇒ ε-separable induced partition      *)
  - intros Hglob.
    unfold robust_partition.
    intros A B HA HB HAB a b Ha Hb.

    (* pick the concrete labels carried by A and B *)
    destruct (part_to_class c A HA) as [i [Hi_lt HAeq]].
    destruct (part_to_class c B HB) as [j [Hj_lt HBeq]].
    subst A B.

    (* want: e < d a b  —  prove its contrapositive with Nat.nle_gt     *)
    apply Nat.nle_gt.                    (* goal: d a b ≤ e → False *)
    intros Hle.

    (* distance ≤ ε ⇒ global robustness forces equal labels *)
    pose proof (Hglob a b Hle) as Hlab_eq.
    unfold class in Ha, Hb.
    rewrite Ha, Hb in Hlab_eq.           (* i = j *)
    subst j.

    (* but then the two sets are *syntactically* equal, contradicting HAB *)
    auto.

  (* ------------------------------------------------------------------ *)
  (* (←) ε-separable induced partition ⇒ globally-robust classifier     *)
  - intros Hsep x y Hdist.               (* d x y ≤ ε *)
    set (A := class c (c x)).
    set (B := class c (c y)).

    (* both blocks really belong to the induced partition *)
    assert (HA : In A (parts (induced_partition c)))
      by (unfold A; apply (class_to_part c (c x)), (classifier_range c x)).
    assert (HB : In B (parts (induced_partition c)))
      by (unfold B; apply (class_to_part c (c y)), (classifier_range c y)).

    (* either the labels are already equal … *)
    destruct (Nat.eq_dec (c x) (c y)) as [Heq|Hneq]; [exact Heq|].

    (* … or they differ, and then the ε-separability yields a contradiction *)
    exfalso.
    assert (A <> B) as HAB.
    { intro HeqAB.
      assert (B x) as Hbx by (rewrite <- HeqAB; unfold A, class; reflexivity).
      unfold B, class in Hbx. congruence. }

    (* witnesses of membership needed by Hsep *)
    assert (Hax : A x) by (unfold A, class; reflexivity).
    assert (Hby : B y) by (unfold B, class; reflexivity).

    pose proof (Hsep A B HA HB HAB x y Hax Hby) as Hgt.  (* e < d x y *)
    lia.                                 (* contradicts d x y ≤ e *)
Qed.




Definition restrict_subset (A : subset) (S0 : subset) : subset :=
  fun x => A x /\ S0 x.

(* The sub-partition P∣S0 – we keep every intersection,                     *)
(* even if it is empty; emptiness does not hurt the robustness condition.   *)
Definition subpartition (p : partition) (S0 : subset) : list subset :=
  map (fun A => restrict_subset A S0) (parts p).

Lemma in_subpartition :
  forall (p : partition) (S0 : subset) (A : subset),
    In A (parts p) ->
    In (restrict_subset A S0) (subpartition p S0).
Proof.
  intros p S0 A Hin.
  unfold subpartition.
  (* tell Coq exactly which f we are talking about *)
  apply (in_map (fun A0 => restrict_subset A0 S0)).
  exact Hin.
Qed.


(*--------------------------------------------------------------*)
(**  Robustness of a sub-partition on a chosen subset S0        *)
(*--------------------------------------------------------------*)

Definition globally_robust_subpartition 
(p : partition) (d : distance_function) (S0 : subset) : Prop :=
  forall x, S0 x ->
    exists A,
      In A (subpartition p S0) /\
      (forall y, S0 y -> e_ball d x y -> A y).

(*==============================================================*)
(**            Theorem 4  (Robustness of all Sub-partitions)    *)
(*==============================================================*)

Theorem robustness_of_all_subpartitions :
  forall (p : partition) (d : distance_function),
    (forall S0 : subset, globally_robust_subpartition p d S0) <->
    globally_robust_partition p d.
Proof.
  intros p d; split.

  (* ------------------------------------------------------------------ *)
  (* (→)  Robustness of every sub-partition ⇒ robustness of p            *)
  - intros Hsub x.
    (* Instantiate with S0 = whole universe *)
    specialize (Hsub (fun _ => True)).
    specialize (Hsub x I).                     (* proof that True x *)
    destruct Hsub as [A' [HA'in_sub Hball]].

    (* A' comes from some A0 ∈ parts p, via restrict_subset *)
    unfold subpartition in HA'in_sub.
    apply in_map_iff in HA'in_sub as [A0 [HA'eq HA0_in]].

    exists A0; split.
    + exact HA0_in.                            (* membership in parts p *)
    + (* ε-ball around x is included in A0 *)
      intros y Hy.
      (* use the ball-inclusion we already have for A' *)
      specialize (Hball y I Hy).               (* I : True y           *)
      rewrite <- HA'eq in Hball.                  (* turn A' into restrict_subset … *)
      unfold restrict_subset in Hball.
      destruct Hball as [HA0y _].              (* keep only A0 y       *)
      exact HA0y.

  (* ------------------------------------------------------------------ *)
  (* (←)  Robustness of p ⇒ robustness of every sub-partition            *)
  - intros Hglob S0 x Hx.                      (* S0 x holds           *)
    (* Global robustness gives a block A with the ε-ball *)
    specialize (Hglob x) as [A [HA_in Hball]].

    (* Restrict that block to S0 *)
    exists (restrict_subset A S0).
    split.
    + (* membership in the sub-partition list *)
      unfold subpartition.
      apply in_map_iff.
      exists A; split; [reflexivity | exact HA_in].

    + (* ε-ball inside the restricted block *)
      intros y HyS0 HyBall.
      specialize (Hball y HyBall).             (* A y                  *)
      unfold restrict_subset.
      exact (conj Hball HyS0).
Qed.


End Paper.

Arguments robustness_of_all_subpartitions {S e} _.
  
