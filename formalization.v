From Coq Require Import Classical List Arith Lia Sorting. 
Require Import Coq.Lists.List.
Import ListNotations. 
Require Import Classical_Prop.
Require Import Coq.Classes.RelationClasses.
From Coq Require Import Reals.
Require Import ClassicalDescription.
Require Import Coq.Init.Wf.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
From Coq.Wellfounded Require Import Wellfounded.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List Coq.Init.Peano.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.Classical_Prop.
From Coq.Logic Require Import ChoiceFacts.
From Coq.Logic Require Import Epsilon.
Require Import ClassicalEpsilon.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Wf.  (* for well_founded_induction *)
Require Import Coq.Arith.Wf_nat.  (* for lt_wf *)

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

(*---------- helper: classes are pair-wise different -------------------*)
Lemma class_injective (c : classifier) :
  forall i j, i < n -> j < n -> class c i = class c j -> i = j.
Proof.
  intros i j Hi Hj Heq.
  (* pick x with  c x = i *)
  destruct (classifier_surj c i Hi) as [x Hxi].
  (* evaluate the functional equality at that x *)
  specialize (f_equal (fun P => P x) Heq) as H.
  rewrite <- Hxi.                     (* goal becomes [c x = j] *)
  simpl in H.                          (* class c k x  ≡  c x = k *)
  unfold class in H.
  rewrite H in Hxi.    (* Hxi : c x = j *)
  exact Hxi.
Qed.

Lemma NoDup_map_injective
      (A B : Type) (f : A -> B) (l : list A) :
  NoDup l ->
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup (map f l).
Proof.
  intros Hndup Hinj.
  induction Hndup as [|x l Hnotin Hndup IH]; simpl.
  - constructor.                                           (* [] case *)
  - constructor.                                           (* x :: l case *)
    + (* prove  ~ In (f x) (map f l) *)
      intro Hin.
      apply in_map_iff in Hin as [y [Heq Hyin]].
      (* show x = y using injectivity on x :: l *)
      assert (x = y) as Hxy.
      { apply Hinj with (x:=x) (y:=y).
        - simpl; auto.                                     (* x ∈ x::l *)
        - right; exact Hyin.                               (* y ∈ l ⊂ x::l *)
        - symmetry; exact Heq. }
      subst y.                                             (* replace y by x *)
      contradiction.                                       (* Hnotin, Hyin *)
    + (* inductive step *)
      apply IH.
      intros u v Hu Hv Hfeq.
      apply Hinj with (x:=u) (y:=v).
      * right; exact Hu.
      * right; exact Hv.
      * exact Hfeq.
Qed.

(** Definition 2: Distance *)
Record distance_function : Type := {
  distance_function_fun   :> S -> S -> nat;
  distance_function_refl : forall x : S, distance_function_fun x x = 0;
  distance_function_nonneg : forall x y, 0 >= distance_function_fun x y;
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
  parts_nodup   : NoDup parts;
  parts_nonempty : forall A, In A parts -> exists x, A x;
  parts_cover    : forall x, exists A, In A parts /\ A x;
  parts_disjoint : forall A B, In A parts -> In B parts -> A <> B -> forall x, ~(A x /\ B x)
}.

Lemma classes_nodup (c : classifier) : NoDup (classes c).
Proof.
  unfold classes.                                  (* map (class c) (seq 0 n) *)
  apply NoDup_map_injective.
  - (* 1) [seq 0 n] has no duplicates *)
    exact (seq_NoDup n 0).
  - (* 2) [class c] is injective on those indices *)
    intros i j Hi Hj Hmap.
    apply (class_injective c i j).
     + apply in_seq in Hi.
      destruct Hi as [_ Hi].      (* we only need the upper bound        *)
      simpl in Hi.                 (* 0 + n  ⟶  n                        *)
      exact Hi. 
    + apply in_seq in Hj.
      destruct Hj as [_ Hj].
      exact Hj.
    + exact Hmap.
Qed.

Lemma classes_nonempty (c : classifier) : forall A, In A (classes c) -> exists x, A x.
Proof.
  intros A H_in.
  unfold classes in H_in.
  apply in_map_iff in H_in.
  destruct H_in as [i [HAi Hi_seq]].
  subst A.
  unfold class.
  apply in_seq in Hi_seq as [_ Hi_lt_n].
  destruct (classifier_surj c i Hi_lt_n) as [x Hx].
  exists x; exact Hx.
Qed.

Lemma classes_cover (c : classifier) :
  forall x, exists A, In A (classes c) /\ A x.
Proof.
  intros x.
  (* Pick the class determined by c x *)
  exists (class c (c x)).
  split.
  - (* show it is one of the classes *)
    unfold classes.
    apply in_map.
    apply in_seq. split.
    + (* lower bound 0 ≤ c x *) lia.
    + (* upper bound  c x < n  *)
      apply classifier_range.
  - (* and that it contains x *)
    unfold class. reflexivity.
Qed.

Lemma classes_disjoint (c : classifier) :
  forall A B,
    In A (classes c) ->
    In B (classes c) ->
    A <> B ->
    forall x, ~(A x /\ B x).
Proof.
  intros A B HA HB HAB x [HAx HBx].
  unfold classes in HA, HB.
  apply in_map_iff in HA.
  apply in_map_iff in HB.
  destruct HA as [i [HAi Hi_in]].
  destruct HB as [j [HBj Hj_in]].
  subst A B.               (* A = class c i,  B = class c j *)
  unfold class in HAx, HBx.
  rewrite HAx in HBx.      (* now HBx : i = j                       *)
  subst j.                 (* replace j by i everywhere             *)
  apply HAB.               (* A and B have become syntactically equal *)
  reflexivity.             (* finishes the contradiction             *)
Qed.

Definition induced_partition (c : classifier) : partition.
Proof.
  refine {|
      parts         := classes c;
      parts_nodup   := classes_nodup c;
      parts_nonempty := classes_nonempty c;
      parts_cover    := classes_cover c;
      parts_disjoint := classes_disjoint c
  |}.
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
intros c d; split. 
- intros Hglob. apply glob_rob_classifier_induces_glob_rob_partition; assumption. 
- intros Hpart. apply induced_partition_glob_rob_then_classifier_glob_rob; assumption.
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

(*==============================================================*)
(**            Theorem 5  (Distances Limit Global Robustness)   *)
(*==============================================================*)
Definition nonempty_proper_subset (A : subset) : Prop :=
  (exists x, A x) /\ (exists x, ~ A x).

Definition trivial_partition (p : partition) : Prop :=
  exists A, parts p = [A].

Definition compl (A : subset) : subset := fun x => ~ A x.



Lemma nontrivial_partition:
  forall (A : subset), nonempty_proper_subset A -> partition.
Proof.
  intros A [H_in H_out].
  refine {|
    parts := [A ; compl A];
    parts_nodup    := _;
    parts_nonempty := _;
    parts_cover := _;
    parts_disjoint := _
  |}.
  - constructor.
    + (* prove   ~ In A [compl A]   i.e. A ≠ compl A *)
      simpl. intros [Heq | []].       (* the only way is A = compl A *)
      subst.
      destruct H_in  as [x  HAx].     (* A  x           *)
      unfold compl in Heq.
      intuition.
      pose proof HAx as Hneg.        (* mak e copy *)
      rewrite <- Heq in Hneg.        (* Hneg : A x -> False *)
      exact (Hneg HAx).              (* contradiction between A x and ~A x  *)
    + (* NoDup for the singleton tail [compl A] *)
      constructor.                    (* ~In _ [] *)
      * simpl; tauto.
      * constructor.                  (* NoDup [] *)
  - (* part_nonempty *)
    intros A0 Hin.
    simpl in Hin.                            (* unfold the 2-element list *)
    destruct Hin as [Heq | [Heq | []]].
    + subst A0. exact H_in.                  (* A0 = A            *)
    + subst A0. exact H_out.                 (* A0 = complement A *)
  - (* part_cover *)
    intros x.
    destruct (classic (A x)) as [Hx | Hx].
    + exists A. split; [left; reflexivity | exact Hx].
    + exists (compl A); split; [right; left; reflexivity | exact Hx].
  - (* part_disjoint *)
    intros A1 A2 Hin1 Hin2 Hneq x [HA1 HA2].
    simpl in Hin1, Hin2.
    destruct Hin1 as [Heq1 | [Heq1 | []]];
    destruct Hin2 as [Heq2 | [Heq2 | []]];
    subst; auto.
Defined.

Lemma robust_partition_implies_global :
  forall (p : partition) (d : distance_function),
    robust_partition p d -> globally_robust_partition p d.
Proof.
  intros p d Hrob x.
  (* Pick the block that contains x. *)
  destruct (parts_cover p x) as [A [HAparts HAx]].
  exists A; split; [exact HAparts|].
  intros y HyBall.
  (* Pick the block that contains y. *)
  destruct (parts_cover p y) as [B [HBparts HBy]].

  (* Case analysis on whether the two blocks are identical. *)
  destruct (classic (A = B)) as [Heq | Hneq].
  - subst B.              (* same block ⇒ done *)
    exact HBy.

  - (* Different blocks would violate ε-separability.                *)
    (* First, obtain  e < d y x  with the right orientation.         *)
    assert (Hneq' : B <> A) by (intro H; apply Hneq; symmetry; exact H).
    specialize (Hrob B A HBparts HAparts Hneq' y x HBy HAx) as Hlt.

    (* But  e_ball d x y  gives  d y x ≤ e — contradiction.          *)
    exfalso.
    unfold e_ball in HyBall.
    lia.
Qed.

(* --------------------------------------------------------------------- *)
(**  If every cross-pair is farther than ε in **both** directions,
      the two-block split [A ; ¬A] is an ε-separable partition.         *)
(* --------------------------------------------------------------------- *)
(* --------------------------------------------------------------------- *)
(**  If every cross-pair is farther than ε in **both** directions,
      the two-block split [A ; ¬A] is an ε-separable partition.         *)
(* --------------------------------------------------------------------- *)
Lemma two_blocks_separated_is_robust
      (d   : distance_function)
      (A   : subset)
      (Hne : nonempty_proper_subset A)
      (Hsep : forall x y, ~ A x -> A y ->
                          e < d x y /\ e < d y x) :
  robust_partition (nontrivial_partition A Hne) d.
Proof.
  intros B C HB_in HC_in HBC a b Ha Hb.
  (* 1️⃣  make the ‘match Hne’ disappear *)
  destruct Hne as [H_in_A H_out_A].

  (* 2️⃣  the list is now visible *)
  simpl in HB_in, HC_in.           (* parts …  ⟹  [A ; compl A] *)

  (* 3️⃣  case-split on which block B is *)
  destruct HB_in as [HB_eqA | HB_tail].

  - (*── B = A ────────────────────────────────────────────────*)
    subst B.
    destruct HC_in as [HC_eqA | HC_tail].
    + subst C.  contradiction.
    + destruct HC_tail as [HC_eqComplA | HC_nil].
      * subst C.                     (* C = ¬A *)
        (*   Ha :      A a
             Hb :   ¬ A b             *)
        destruct (Hsep b a Hb Ha) as [_ Hlt]. exact Hlt.
      * contradiction.

    - (*── B = ¬A ───────────────────────────────────────────────*)
    destruct HB_tail as [HB_eqComplA | HB_nil]; [subst B | contradiction].
    destruct HC_in as [HC_eqA | HC_tail].
    + subst C.                       (* C = A *)
      (*   Ha :   ¬ A a
           Hb :      A b             *)
      destruct (Hsep a b Ha Hb) as [Hlt _]. exact Hlt.
    + destruct HC_tail as [HC_eqComplA | HC_nil]; [subst C | contradiction].
      contradiction.                 (* B = C would violate HBC *)
Qed.



Lemma separation_yields_globally_robust_nontrivial :
  forall (d : distance_function) (A : subset) (Hne : nonempty_proper_subset A),
    (forall x y, ~ A x -> A y -> e < d x y /\ e < d y x) ->
    let p := nontrivial_partition A Hne in
    globally_robust_partition p d /\ ~ trivial_partition p.
Proof.
  intros d A Hne Hfar p. split.
  - apply robust_partition_implies_global,
        two_blocks_separated_is_robust with (A:=A); assumption.
  - intro Htriv.
    destruct Htriv as [B Hp].          (* Hp : parts p = [B]          *)
    destruct Hne as [Hin Hout].        (* remove the “match Hne”      *)
    inversion Hp; subst; simpl in *;
    discriminate.
Qed.




Theorem distances_limit_global_robustness
  (d : distance_function):
    (forall p : partition,
        globally_robust_partition p d -> trivial_partition p) ->
    (forall A : subset,
      nonempty_proper_subset A ->
      exists x y,
        ~ A x /\ A y /\ (d x y <= e \/ d y x <= e)).
Proof.
  intros Hlim A Hne.

  (* Classical case-analysis on the existence we want to prove. *)
  destruct (classic (exists x y,
            ~ A x /\ A y /\ (d x y <= e \/ d y x <= e))) as [Hex | Hnex].
  - exact Hex.                                  (* happy branch *)

  - (* ¬ ∃ close pair  ⇒  build a globally robust, non-trivial partition,
       contradicting the premise -- thereby producing False. *)

    (* From ¬ ∃ close pair we get “all cross pairs are farther than ε”. *)
    assert (Hfar : forall x y,
             ~ A x -> A y -> e < d x y /\ e < d y x).
    { intros x y Hnx Hay.
      split.
      - destruct (le_lt_dec (d x y) e) as [Hle|Hlt]; [| exact Hlt].
        exfalso. apply Hnex.                          (* forbidden witness *)
        exists x, y. repeat split; try assumption; left; exact Hle.
      - destruct (le_lt_dec (d y x) e) as [Hle|Hlt]; [| exact Hlt].
        exfalso. apply Hnex.
        exists x, y. repeat split; try assumption; right; exact Hle. }

    (* Lemma 3: the two-block partition is globally robust & non-trivial. *)
    destruct (separation_yields_globally_robust_nontrivial
                d A Hne Hfar)
      as [Hglob Hnontriv].               (* p is implicit *)

    (* The premise says every globally robust partition is trivial. *)
    specialize (Hlim _ Hglob) as Htriv.

    (* Contradiction: p is both trivial and non-trivial. *)
    exfalso. apply (Hnontriv Htriv).
Qed.

Lemma cross_part_far
      (p : partition) (d : distance_function) :
  globally_robust_partition p d ->
  forall A B a b,
    In A (parts p) -> In B (parts p) -> A <> B ->
    A a -> B b ->
    e < d a b /\ e < d b a.
Proof.
  intros Hglob A B a b HA HB HAB Ha Hb.
  pose proof (Hglob a) as [A' [HA'parts HballA]].
  pose proof (Hglob b) as [B' [HB'parts HballB]].

  (* A’ and B’ are the blocks delivered by global robustness     *)
  (* for the two witnesses a and b; use disjointness to show     *)
  (* that A’ = A and B’ = B, then rule out d ≤ ε in either dir.  *)
    (* A' contains a (distance 0 ≤ ε)                                  *)
  assert (Ha' : A' a).
  { apply (HballA a). unfold e_ball.
    rewrite distance_function_refl. apply le_0_n. }

  (* B' contains b                                                   *)
  assert (Hb' : B' b).
  { apply (HballB b). unfold e_ball.
    rewrite distance_function_refl. apply le_0_n. }

  (* ---------- prove A' = A --------------------------------------- *)
  assert (A' = A) as HeqA.
  { destruct (classic (A' = A)) as [Heq|Hneq]; [exact Heq|].
    exfalso.
    apply (parts_disjoint p A' A HA'parts HA Hneq a); split; assumption. }

  (* ---------- prove B' = B --------------------------------------- *)
  assert (B' = B) as HeqB.
  { destruct (classic (B' = B)) as [Heq|Hneq]; [exact Heq|].
    exfalso.
    apply (parts_disjoint p B' B HB'parts HB Hneq b); split; assumption. }

  subst A' B'.

  (* ---------- now rule out each ≤ ε case ------------------------- *)
  split.
  - (* 1️⃣  assume d a b ≤ ε and derive a contradiction *)
    apply Nat.nle_gt.                      (* goal: ~(d a b ≤ e) *)
    intros Hle.                            (* Hle : d a b ≤ e    *)
    pose proof (HballB a Hle) as HBa.      (* B  a               *)
    apply (parts_disjoint p A B HA HB HAB a); split; [ exact Ha | exact HBa ].

  - (* 2️⃣  assume d b a ≤ ε and derive a contradiction *)
    apply Nat.nle_gt.                      (* goal: ~(d b a ≤ e) *)
    intros Hle.                            (* Hle : d b a ≤ e    *)
    pose proof (HballA b Hle) as HAb.      (* A  b               *)
    apply (parts_disjoint p A B HA HB HAB b); split; [ exact HAb | exact Hb ].
Qed.

Lemma nontrivial_partition_gives_part
      (p : partition) :
  exists A,
    In A (parts p) ->
    ~ trivial_partition p ->
    nonempty_proper_subset A.
Proof.
  destruct p as [parts Hnodup Hnonempty Hcover Hdisjoint].
  destruct parts as [|A0 rest].

  - (* parts = [] : the premise “In A []” is impossible *)
    exists (fun _ => False). intros Hin _. inversion Hin.

  - (* parts = A0 :: rest *)
    exists A0. intros _ Hnot_triv.
    unfold nonempty_proper_subset. split.

    + (* ∃x, A0 x  (non-empty) *)
      apply Hnonempty. simpl; left; reflexivity.

    + (* ∃x, ¬ A0 x  (proper) *)
      destruct rest as [|B rest'].
      * (* only one block ⇒ partition is [A0] ⇒ contradicts non-triviality *)
        exfalso. apply Hnot_triv. exists A0. reflexivity.
      * (* there is a second block B *)
        assert (HB_in : In B (A0 :: B :: rest')) by (simpl; right; left; reflexivity).
        destruct (Hnonempty _ HB_in) as [x HBx].      (* pick x ∈ B *)


        (* A0 and B are syntactically different – a consequence of [NoDup]. *)
        assert (A0 <> B) as Hneq.
        intro Heq. subst B.
        inversion Hnodup as [| Heq Hneq Hnotin _]; simpl in Hnotin.
        assert (Hin : In A0 (A0 :: rest')) by (left; reflexivity).
        apply Hnotin; left; reflexivity.
        inversion Hnodup as [| ? ? Hnotin _]; subst.
        pose proof (Hdisjoint A0 B (or_introl eq_refl) HB_in Hneq x) as Hnot_both.
        exists x.
        auto.
Qed.



Theorem global_robustness_limit_distances
        (d : distance_function) :
  (inhabited S) ->
    (forall A : subset,
      nonempty_proper_subset A ->
      exists x y,
        ~ A x /\ A y /\ (d x y <= e \/ d y x <= e)) ->
  forall p : partition,
    globally_robust_partition p d ->
    trivial_partition p.
Proof.
  intros Hclose Hglob p.
  destruct Hclose as [x].
  unfold trivial_partition.
  (* We do case analysis on the list of blocks that constitutes [p].      *)
  unfold globally_robust_partition.
  destruct (parts p) as [|A rest] eqn:Hparts.
  
  (* ------------------------------------------------------------------ *)
  (* Case 1: [parts p] = [] – IMPOSSIBLE                                 *)
  (* ------------------------------------------------------------------ *)
  -  (* Unpack the record *)
  
    destruct p as [parts_p Hnodup Hnonempty Hcover Hdisjoint].
    simpl in Hparts. rewrite Hparts in *. (* Replace parts_p with [] *)
    pose proof (Hcover x) as [A [Hin _]]. (* Apply parts_cover to x *)
    simpl in Hin. contradiction.
  (* ------------------------------------------------------------------ *)
  (* Case 2: nonempty parts          *)
  (* ------------------------------------------------------------------ *)
  - destruct rest as [|B rest'].
    + exists A. reflexivity.
    + assert (HA : In A (parts p))  by (rewrite Hparts; simpl; auto).
      assert (HB : In B (parts p))  by (rewrite Hparts; simpl; auto).
      destruct (parts_nonempty p A HA) as [a Ha].      (* a ∈ A          *)
      destruct (parts_nonempty p B HB) as [b Hb].      (* b ∈ B          *)

      pose proof (parts_nodup p) as Hnodup.
      rewrite Hparts in Hnodup. inversion Hnodup.

      assert (HAB : A <> B).
      {
        intro Heq.           (* assume A = B … *)
        subst B.
        inversion Hnodup as [| ? k Hnotin _].
        contradiction Hnotin. simpl. left. reflexivity.
      }
    
    assert (Hnb : ~ A b).
    { 
      intro Hab.
      pose proof (parts_disjoint p A B HA HB HAB b ltac:(now split)) as contra.
      tauto.
    }
    
    (* A is proper:  b ∉ A, because blocks are pairwise disjoint *)
    assert (Hproper : nonempty_proper_subset A).
    { 
      split.
      + exists a; exact Ha.                    (* non-empty *)
      + exists b. exact Hnb.                              (* not whole S *)
    }

    (* Apply the “two ε-close points” axiom to that proper subset A *)
    destruct (Hglob _ Hproper)
      as [x' [y [Hx_out [Hy_in Hd_le]]]].

    (* Obtain the unique block C that contains every ε-ball around x *)
    destruct (Hglob A) as [Csub [HCin HCball]].
    {unfold nonempty_proper_subset.
    split.
    + now exists a.    (* a : S is in the context *)
    + now exists b. }

  intros Hclose.
  destruct Hd_le as [Hxy_le | Hyx_le].
   (* e_ball d y x' holds *)

  * assert (Hball : e_ball d y x').
    { unfold e_ball; exact Hxy_le. }
  (* pick the unique ε-ball block around y *)
    destruct (Hclose y) as [A0 [HA0_in HA0_ball]].
    (* y and x' are both in that block *)
    assert (HyA0  : A0 y ) by
        (apply HA0_ball; unfold e_ball;
         rewrite distance_function_refl; apply le_0_n).
    assert (HxA0  : A0 x') by (apply HA0_ball; exact Hball).
    (* turn HA0_in into a fact about (parts p) -------------------------- *)
    assert (HA0_parts : In A0 (parts p))
      by (rewrite Hparts; exact HA0_in).

    (* If A0 ≠ A, disjointness is violated by y ∈ A ∩ A0 *)
    assert (A0 = A) as Heq.
    { destruct (classic (A0 = A)) as [|Hneq]; [assumption|].
      exfalso.
      apply (parts_disjoint p A0 A HA0_parts HA Hneq y).
      split; [ exact HyA0 | exact Hy_in ]. }

    contradict Hx_out.
    subst A0.                 (* replaces every A0 by A everywhere     *)
    exact HxA0.

  * 
    assert (Hball : e_ball d x' y ).
    { unfold e_ball; exact Hyx_le. }
  (* pick the unique ε-ball block around x' *)
    destruct (Hclose x') as [A0 [HA0_in HA0_ball]].
    (* y and x' are both in that block *)
    
    assert (HxA0  : A0 x' ) by
        (apply HA0_ball; unfold e_ball;
         rewrite distance_function_refl; apply le_0_n).
    
    assert (HyA0  : A0 y) by (apply HA0_ball; exact Hball).
    (* turn HA0_in into a fact about (parts p) -------------------------- *)
    assert (HA0_parts : In A0 (parts p))
      by (rewrite Hparts; exact HA0_in).

    (* If A0 ≠ A, disjointness is violated by y ∈ A ∩ A0 *)
    assert (A0 = A) as Heq.
    { destruct (classic (A0 = A)) as [|Hneq]; [assumption|].
      exfalso.
      apply (parts_disjoint p A0 A HA0_parts HA Hneq y).
      split; [ exact HyA0 | exact Hy_in ]. }

    contradict Hx_out.
    subst A0.                 (* replaces every A0 by A everywhere     *)
    exact HxA0.
    
    
    
    
Qed.



Theorem global_robustness_equals_distances (d : distance_function):
  (inhabited S) ->
    (forall p : partition,
        globally_robust_partition p d -> trivial_partition p) <->
    (forall A : subset,
      nonempty_proper_subset A ->
      exists x y,
        ~ A x /\ A y /\ (d x y <= e \/ d y x <= e)).
Proof.
intros *; 
split.
- apply distances_limit_global_robustness; assumption. 
- apply global_robustness_limit_distances; assumption.
Qed.








(*
  Precision Gap in Ordered Metric Sets
  ====================================
  This file formalises the material contained in Section "Precision Gap in
  Ordered Metric Sets" (see the accompanying LaTeX excerpt).  We proceed in
  three phases:

  1.  *Abstract setting.*  A *finite totally ordered set* is represented by a
      list `carrier : list A` whose elements are pairwise distinct and whose
      order, given by a binary relation `lt : A -> A -> Prop`, is total and
      strict.  The list is regarded as a *full enumeration* of the set; any
      `x : A` that belongs to the set appears exactly once in `carrier`.

  2.  *Metric structure.*  A distance function `d : A -> A -> R` is attached to
      the set.  The only property of `d` needed for the development is
      non-negativity.

  3.  *Precision gap.*  The *successor* relation is defined via adjacency inside
      `carrier`.  The *precision gap* is the maximum distance between any two
      successive elements.  We finally prove the *Precision-Gap Constraint*:
      every non-empty proper subset of the carrier has a boundary element whose
      distance to its complement is bounded by the precision gap.

  The formal proofs follow the textbook argument given in the LaTeX source.
  They rely only on elementary facts from the standard library
  (`List`, `Reals`, `Lia`).
*)


  (** * Abstract setting *)
  (** We work with a strict order [lt]. *)
  Variable lt : S -> S -> Prop.
  Variable d : distance_function.

  Definition ge (x y : S) : Prop := lt y x \/ x = y.
  Definition le (x y : S) : Prop := lt x y \/ x = y.

    Definition is_maximum (x : S) : Prop :=
    forall y : S, ge x y.

  Definition is_minimum (x : S) : Prop :=
    forall y : S, ge y x.



 (** A strict total order: irreflexive, transitive, and total. *)
  Hypothesis lt_irrefl  : forall x : S, ~ lt x x.
  Hypothesis lt_trans   : forall x y z : S, lt x y -> lt y z -> lt x z.
  Hypothesis lt_total   : forall x y : S, x = y \/ lt x y \/ lt y x.
  

  (** * Finiteness of S by an explicit list *)
  Variable elems : list S.
  (** every element of S appears in [elems] *)
  Hypothesis elems_complete : forall x : S, In x elems.
  (** no duplicates in [elems] *)
  Hypothesis elems_nodup    : NoDup elems.


  Definition is_successor (x y : S) : Prop := lt x y /\ (forall z : S, ~ (lt x z /\ lt z y)).

  Hypothesis lt_dec : forall x y, {lt x y} + {~ lt x y}.

   Definition succb (x y : S) : bool :=
    match lt_dec x y with
    | left Hlt =>
        if existsb (fun z =>
             match lt_dec x z, lt_dec z y with
             | left Hxz, left Hzy => true
             | _, _               => false
             end)
          elems
        then false
        else true
    | right _ => false
    end.


 (** 4) list all pairs *)
  Definition all_pairs : list (S * S) :=
    flat_map (fun x => map (fun y => (x,y)) elems) elems.

  (** 5) filter to just the successor-adjacent ones *)
Definition succ_pairs : list (S * S) :=
  filter (fun p : S * S =>
            let (x,y) := p in
            succb x y || succb y x)
         all_pairs.


  (** 6) pull out their distances *)
  Definition gaps : list nat :=
    map (fun p => d (fst p) (snd p)) succ_pairs.

  (** 7) a little utility to take the maximum of a non-empty list of reals *)
  Fixpoint max_list (l : list nat) : nat :=
    match l with
    | []    => 0     (* we’ll later show [gaps] is never empty, so this case won’t matter *)
    | r::rs => max r (max_list rs)
    end.

  (** 8) finally, the precision gap Δ *)
  Definition precision_gap : nat := max_list gaps.

Variable S' : list S.
Hypothesis S'_nonempty : exists x, In x S'.
Hypothesis S'_proper   : exists y, In y elems /\ ~ In y S'.
Hypothesis S'_subset   : forall x, In x S' -> In x elems.
Hypothesis S'_decidable: forall x y, In x S' /\ In y S' -> {x = y} + {x <> y}.
Hypothesis S'_nodup    : NoDup S'.



(** all elements strictly between [x] and [y] *)
Definition betw (x y : S) : list S :=
  filter (fun z =>
            if lt_dec x z
            then if lt_dec z y then true else false
            else false)
         elems.




Lemma length_split {A} (x : A) (l1 l2 : list A) :
  length (l1 ++ x :: l2) = Nat.succ (length (l1 ++ l2)).
Proof.
  (* rewrite app_length on *both* the LHS and the RHS *)
  rewrite !app_length.
  (* now the goal is
       length l1 + length (x::l2) = S (length l1 + length l2)
     and [simpl] will reduce the length on the LHS to
       length l1 + S (length l2) = S (length l1 + length l2)
  *)
  simpl.
  (* now we have “_ + S _ = …”, so plus_n_Sm applies *)
  rewrite plus_n_Sm.
  reflexivity.
Qed.





  
Lemma boundary_pair_exists :
    exists x x',
      In x elems /\ In x' elems /\
      ((In x' S' /\ ~ In x S') \/ (In x S' /\ ~ In x' S')) /\
      (succb x x' = true \/ succb x' x = true).
Proof.
(* TODO *)
Qed.




Lemma max_list_ge (l : list nat) (m : nat) :
  In m l -> m <= max_list l.
Proof.
  induction l as [| h t IH].
  - (* l = [] *) 
    simpl. intros [].
  - (* l = h :: t *)
    simpl. intros [-> | Hin].
    + (* m = h *) 
      lia.
    + (* m ∈ t *)
      (* First, by IH we know m ≤ max_list t *)
      apply Nat.le_trans with (m := max_list t).
      * apply IH; assumption.
      * (* and max_list t ≤ max h (max_list t) = max_list (h::t) *)
        destruct (max_list t); simpl; lia.
Qed.


Lemma in_map_fst {A B} (f : A -> B) (x:A) (l:list A) :
  In x l -> In (f x) (map f l).
Proof. induction l; [easy | intros [->| Hin] ]; simpl; auto. Qed.

Lemma gap_leq_precision_gap x x' :
  In (x, x') succ_pairs ->
  d x x' <= precision_gap.
Proof.
  intros Hin.
  unfold precision_gap.
  apply max_list_ge.
  unfold gaps.
  (* explicitly tell it which f and which x you mean *)
  apply in_map_fst
    with (f := fun p => d (fst p) (snd p))
         (x := (x, x')).
  exact Hin.
Qed.



Lemma in_filter_pair {A} (P : A -> bool) (l : list A) x :
  In x (filter P l) -> P x = true.
Proof.
  intros H. apply filter_In in H. destruct H as [_ H2]. exact H2.
Qed.


Theorem precision_gap_constraint :
  exists x x',
    In x elems /\ In x' elems /\
    ((In x' S' /\ ~ In x S') \/ (In x S' /\ ~ In x' S')) /\
    d x x' <= precision_gap.
Proof.
  (* 1. There is a boundary pair *)
  edestruct boundary_pair_exists as (x & x' & Hx & Hx' & Hbd & Hsucc).

  (* 2. This pair is in succ_pairs by definition *)
  assert (Hin : In (x, x') succ_pairs).
  {
    unfold succ_pairs, all_pairs.
    apply filter_In.
    split.
    - apply in_flat_map. exists x. split; [exact Hx|].
      apply in_map. exact Hx'.
    - destruct Hsucc as [Hs|Hs]; rewrite Hs; simpl; auto.
      apply orb_true_r.
  }

  (* 3. So its distance is in gaps, hence ≤ precision_gap *)
  assert (Hgap : d x x' <= precision_gap).
  { apply gap_leq_precision_gap; exact Hin. }

  exists x, x'. repeat (split; try assumption).
Qed.





End Paper.




Arguments precision_gap_constraint {S e} _.
  
