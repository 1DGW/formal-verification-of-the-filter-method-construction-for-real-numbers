(*    This file presents the formalization for construction of R.    *)
(*  It is developmented in the CoqIDE (version 8.13.2) for windows.  *)

(** Qs_to_R *)

Require Export fmcr.finity_and_infinity_in_Qs.

(* 定义一个关系R_Q', 之后可以证明: 此关系为 *Q_Arch 上的等价关系. *)
Definition R_Q' := \{\ λ u v, u ∈ Q'_Arch /\ v ∈ Q'_Arch /\ (u - v) ∈ I \}\.

(* 证明: 关系R_Q' 为 *Q_Arch 上的等价关系. *)
Property R_Q'_is_equRelation : equRelation R_Q' Q'_Arch.
Proof.
  repeat split; intros.
  - unfold Included; intros.
    apply AxiomII in H as [H[u[v[H0[H1[]]]]]].
    rewrite H0. apply AxiomII'; split; auto. rewrite <-H0; auto.
  - unfold Reflexivity. intros.
    apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
    assert (x - x = Q'0).
    { apply Q'_Minus_Plus; try apply Q'0_in_Q';
      try apply Q'_Arch_subset_Q'; auto.
      rewrite Q'_Plus_Property; auto. apply Q'_Arch_subset_Q'; auto. }
    rewrite H0. assert (∀ n, F0 <> F n). { destruct NPAUF; auto. }
    apply Q'0_Singleton_propersubset_I; auto. apply MKT41; auto.
    pose proof Q'0_in_Q'; eauto.
  - unfold Symmetry; intros. apply AxiomII' in H1 as [H1[H2[]]].
    apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
    apply AxiomII in H4 as [H4[]]. apply AxiomII.
    apply Q'_Arch_subset_Q' in H; apply Q'_Arch_subset_Q' in H0; auto.
    apply (Q'_Minus_in_Q' y x) in H; auto. repeat split; eauto. intros.
    apply H6 in H7. assert (|(x - y)| = |(y - x)|).
    { apply Q'_Arch_subset_Q' in H2; apply Q'_Arch_subset_Q' in H3; auto.
      apply Neg_Q'Abs_Equ; try apply Q'_Minus_in_Q'; auto.
      rewrite <-Q'_Mix_Association1,Q'_Plus_Commutation,
      <-Q'_Mix_Association1,Q'_Plus_Commutation,
      Q'_Mix_Association1,Q'_Plus_Commutation,
      Q'_Mix_Association1; try apply Q'_Minus_in_Q'; auto.
      assert (y - y = Q'0 /\ x - x = Q'0) as [].
      { split; apply Q'_Minus_Plus;
        try rewrite Q'_Plus_Property; try apply Q'0_in_Q'; auto. }
      rewrite H8,H9, Q'_Plus_Property; try apply Q'0_in_Q'; auto. }
    rewrite <-H8; auto.
  - unfold Transitivity; intros.
    apply AxiomII' in H2 as [H2[H4[]]].
    apply AxiomII' in H3 as [H3[H7[]]].
    apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
    assert (x - z = (x - y) + (y - z)).
    { apply Q'_Arch_subset_Q' in H; apply Q'_Arch_subset_Q' in H0;
      apply Q'_Arch_subset_Q' in H1; auto.
      rewrite <-Q'_Mix_Association1,Q'_Plus_Commutation,
      <-Q'_Mix_Association1,Q'_Plus_Commutation,
      (Q'_Mix_Association1 x y y); auto with Q'.
      assert (y - y = Q'0).
      { apply Q'_Minus_Plus; try apply Q'0_in_Q'; auto.
        rewrite Q'_Plus_Property; auto. }
      rewrite H10,Q'_Plus_Property; auto. }
    rewrite H10. auto with Q'.
Qed.

Declare Scope r_scope.
Delimit Scope r_scope with r.
Open Scope r_scope.

Notation "\[ u \] " := (equClass u R_Q' Q'_Arch)(at level 5) : r_scope.

(* 证明: [u] = [v] 等价于 u-v ∈ I. *)
Property R_Q'_Property : ∀ u v, u ∈ Q'_Arch -> v ∈ Q'_Arch
  -> \[u\] = \[v\] <-> (u - v) ∈ I.
Proof.
  split; intros.
  - apply equClassT1 in H1; try apply R_Q'_is_equRelation; auto.
    apply AxiomII' in H1; tauto.
  - symmetry. apply equClassT1; try apply R_Q'_is_equRelation; auto.
    apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
Qed.

(* 定义: R 为 *Q_Arch 关于 R_Q' 的商集. *)
Definition Ｒ := (Q'_Arch / R_Q')%eqr.

(* 关于R的推论: R是一个集 *)
Property R_is_Set : Ensemble Ｒ.
Proof.
  apply (MKT33 pow(Q'_Arch)). apply MKT38a,Q'_Arch_is_Set; auto.
  unfold Included; intros. apply AxiomII in H as [H[x[]]].
  apply AxiomII; split; auto. rewrite H1.
  unfold Included; intros. apply AxiomII in H2; tauto.
Qed.

(* R中元素的具体化 *)
Property R_Instantiate1 : ∀ u, u ∈ Ｒ
  -> ∃ x, x ∈ Q'_Arch /\ x ∈ Q' /\ u = \[x\].
Proof.
  intros. apply AxiomII in H as [H[x[]]]. exists x.
  repeat split; auto. apply Q'_Arch_subset_Q'; auto.
Qed.

Property R_Instantiate2 : ∀ x, x ∈ Q'_Arch -> \[x\] ∈ Ｒ.
Proof.
  intros. assert (Ensemble (\[x\])).
  { apply (MKT33 Q'_Arch). apply Q'_Arch_is_Set; destruct H; auto.
    unfold Included; intros. apply AxiomII in H0; tauto. }
  apply AxiomII; split; eauto.
Qed.

Ltac inR H x := apply R_Instantiate1 in H as [x[?[]]]; auto.

(* 定义一个新的类, 之后的证明可见, 此类实际为实数0. *)
Definition R0 := \[Q'0\].

(* 定义一个新的类, 之后的证明可见, 此类实际为实数1. *)
Definition R1 := \[Q'1\].

(* R0 = I (实数0就是*Q中的无穷小集) *)
Property R0_Property : R0 = I.
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H as [H[]].
    apply AxiomII' in H1 as [H2[H3[]]].
    assert (z = z - Q'0).
    { symmetry. apply Q'_Minus_Plus; auto with Q';
      try apply Q'_Arch_subset_Q'; auto.
      rewrite Q'_Plus_Commutation,Q'_Plus_Property;
      try apply Q'_Arch_subset_Q'; auto with Q'. }
    rewrite H5; auto.
  - apply AxiomII. repeat split; eauto.
    apply I_propersubset_Q'_Arch; auto.
    apply AxiomII'; repeat split; auto with Q'.
    pose proof Q'0_in_Q'. apply MKT49a; eauto.
    apply I_propersubset_Q'_Arch; auto.
    assert (z - Q'0 = z).
    { apply Q'_Minus_Plus; auto with Q';
      try apply Q'_Arch_subset_Q'; try apply I_propersubset_Q'_Arch; auto.
      rewrite Q'_Plus_Commutation,Q'_Plus_Property; auto with Q';
      apply Q'_Arch_subset_Q'; apply I_propersubset_Q'_Arch; auto. }
    rewrite H0; auto.
Qed.

(* 验证: R0 确实是R中的元素 *)
Property R0_in_R : R0 ∈ Ｒ.
Proof. intros. apply R_Instantiate2; auto with Q'. Qed.

Global Hint Resolve R0_in_R : R.

(* 验证: R1 确实是R中的元素 *)
Property R1_in_R : R1 ∈ Ｒ.
Proof.
  intros. apply R_Instantiate2; auto. pose proof Q'1_in_Q'.
  apply AxiomII; repeat split; eauto. exists Q'1. split.
  - destruct φ4_is_Function as [[][]]. replace Q'_N with ran(φ4); auto.
    rewrite <-φ4_1; auto. apply (@ Property_ran 1),Property_Value; auto.
    rewrite H2. apply in_ω_1.
  - left. apply mt_Q'0_Q'Abs; auto with Q'.
Qed.

Global Hint Resolve R1_in_R : R.

(* 验证 R中的性质(零元和幺元不相等) *)
Property R0_isnot_R1 : R0 <> R1.
Proof.
  intros; intro. symmetry in H. apply R_Q'_Property in H; auto with Q'.
  rewrite Q'_Minus_Property2 in H; auto with Q'. apply AxiomII in H as [H[]].
  assert (Q'1 ∈ (Q'_N ~ [Q'0])).
  { apply MKT4'; split. apply Q'1_in_Q'_N; auto. apply AxiomII; split; auto.
    intro. apply MKT41 in H2; eauto with Q'. elim Q'0_isnot_Q'1; auto. }
  apply H1 in H2. rewrite (mt_Q'0_Q'Abs Q'1),Q'_Divide_Property2 in H2;
  auto with Q'. elim (Q'_Ord_irReflex Q'1 Q'1); auto.
Qed.

Global Hint Resolve R0_isnot_R1 : R.

(* 定义 R上的序关系  R上的u和v, u前于v就是说, 所有 可以代表u的[x] 和
                   所有 可以代表v的[y] (其中x y不等价, 即u<>v)
                   都要满足:  x 前于 y.  *)
Definition R_Ord := \{\ λ u v, u <> v
  /\ (∀ x y, x ∈ Q'_Arch -> y ∈ Q'_Arch -> u = \[x\] -> v = \[y\] -> x < y) \}\.

Notation "u < v" := ([u,v] ∈ R_Ord) : r_scope.

(* 验证  R上序关系的定义的合理性: 所规定的序关系 与 表示元素的代表 无关.
        若 [x] = [x1]   [y] = [y1]  (指等价类相同)
        则  x 小于 y   就等价于   x1 小于 y1   *)
Open Scope q'_scope.

Property R_Ord_Reasonable : ∀ x x1 y y1, x ∈ Q'_Arch -> x1 ∈ Q'_Arch
  -> y ∈ Q'_Arch -> y1 ∈ Q'_Arch -> (\[x\] = \[x1\])%r -> (\[y\] = \[y1\])%r
  -> (\[x\] <> \[y\])%r -> x < y <-> x1 < y1.
Proof.
  assert (∀ x x1 y y1, x ∈ Q'_Arch -> x1 ∈ Q'_Arch
    -> y ∈ Q'_Arch -> y1 ∈ Q'_Arch -> (\[x\] = \[x1\])%r -> (\[y\] = \[y1\])%r
    -> (\[x\] <> \[y\])%r -> x < y -> x1 < y1).
  { intros. assert (x ∈ Q' /\ x1 ∈ Q' /\ y ∈ Q' /\ y1 ∈ Q') as [H7[H8[]]].
    { repeat split; try apply Q'_Arch_subset_Q'; auto. }
    symmetry in H3. apply R_Q'_Property in H3,H4; auto.
    assert (((x1 - x) + (y - y1)) ∈ I). { apply I_Plus_in_I; auto. }
    assert ((x1 - x) + (y - y1) = (y - x) + (x1 - y1)).
    { rewrite <-Q'_Mix_Association1,<-Q'_Mix_Association1; auto with Q'.
      apply Q'_Minus_Plus; auto with Q'.
      rewrite <-Q'_Mix_Association1,Q'_Plus_Commutation,Q'_Mix_Association1;
      auto with Q'. rewrite Q'_Minus_Property1,Q'_Plus_Property,
      Q'_Plus_Commutation,<-Q'_Mix_Association1,(Q'_Plus_Commutation (x1 - x)),
      <-Q'_Mix_Association1,Q'_Plus_Commutation; auto with Q'. }
    rewrite H12 in H11. clear H12. assert (Q'0 < (y - x)).
    { apply (Q'_Plus_PrOrder _ _ x); auto with Q'.
      rewrite Q'_Plus_Property,<-Q'_Mix_Association1,
      Q'_Plus_Commutation,Q'_Mix_Association1,Q'_Minus_Property1,
      Q'_Plus_Property; auto. }
    assert ((y - x) ∉ I).
    { intro. elim H5. symmetry. apply R_Q'_Property; auto. }
    set (A := (x1 - y1)).
    destruct (Q'_Ord_Tri A Q'0) as [H14|[|]]; unfold A; auto with Q'.
    - unfold A in H14. apply (Q'_Plus_PrOrder _ _ y1) in H14; auto with Q'.
      rewrite Q'_Plus_Property,<-Q'_Mix_Association1,Q'_Plus_Commutation,
      Q'_Mix_Association1,Q'_Minus_Property1,Q'_Plus_Property in H14; auto.
    - assert (∃ k, k ∈ (Q'_N ~ [Q'0])
        /\ (Q'1 / k = |(y - x)| \/ (Q'1 / k) < |(y - x)|)) as [k[]].
      { apply NNPP; intro. elim H13. apply AxiomII; repeat split;
        eauto with Q'. intros. apply NNPP; intro. elim H15.
        exists k. split; auto. destruct (Q'_Ord_Tri (|(y - x)|) (Q'1 / k))
        as [H18|[]]; try contradiction; auto with Q'.
        apply Q'_Divide_in_Q'; auto with Q'. apply MKT4' in H16 as [].
        apply Q'_N_subset_Q'; auto. apply MKT4' in H16 as [_].
        apply AxiomII in H16 as []. intro. elim H18.
        apply MKT41; eauto with Q'. }
      rewrite mt_Q'0_Q'Abs in H16; auto with Q'.
      assert ((Q'1 / k) < ((y - x) + A)).
      { apply (Q'_Plus_PrOrder _ _ (y - x)) in H14; auto with Q'.
        rewrite Q'_Plus_Property in H14; auto with Q'. destruct H16.
        rewrite H16; auto. apply (Q'_Ord_Trans _ (y - x)); unfold A;
        auto with Q'. apply Q'_Divide_in_Q'; auto with Q'.
        apply MKT4' in H15 as []. apply Q'_N_subset_Q'; auto.
        apply MKT4' in H15 as [_]. apply AxiomII in H15 as [].
        intro. elim H17. apply MKT41; eauto with Q'. apply Q'_Minus_in_Q'; auto. }
      apply AxiomII in H11 as [_[]]. rewrite mt_Q'0_Q'Abs in H18; auto.
      pose proof H15. apply MKT4' in H19 as []. apply Q'_N_subset_Q' in H19; auto.
      assert (k <> Q'0).
      { apply AxiomII in H20 as []. intro. elim H21. apply MKT41; eauto with Q'. }
      clear H20. pose proof H15. apply Q'_N_Q'0_is_FirstMember in H20; auto.
      apply H18 in H15. apply (Q'_Ord_Trans (Q'1 / k)) in H15; auto with Q'.
      elim (Q'_Ord_irReflex (Q'1 / k) (Q'1 / k)); auto with Q'.
      apply (Q'_Plus_PrOrder _ _ (y - x)) in H14; unfold A; auto with Q'.
      rewrite Q'_Plus_Property in H14; auto with Q'.
      apply (Q'_Ord_Trans _ (y - x)); auto with Q'.
    - unfold A in H14. rewrite H14,Q'_Plus_Property in H11; auto with Q'.
      elim H13; auto. }
  split; intros; [apply (H x x1 y y1)|apply (H x1 x y1 y)]; auto.
  intro; elim H6. rewrite H4,H5; auto.
Qed.

Close Scope q'_scope.

(* R上序关系的实例化描述: 
               [x]  R小于  [y]   (指等价类前于)
        就是指  x   Q'小于  y  并且 [x]<>[y].   *)
Property R_Ord_Instantiate : ∀ x y, x ∈ Q'_Arch -> y ∈ Q'_Arch
  -> \[x\] < \[y\] <-> ((x < y)%q' /\ \[x\] <> \[y\]).
Proof.
  split; intros.
  - apply AxiomII' in H1 as [H1[]]. split; auto.
  - destruct H1.
    assert (\[x\] ∈ Ｒ). { apply R_Instantiate2; auto. }
    assert (\[y\] ∈ Ｒ). { apply R_Instantiate2; auto. }
    apply AxiomII'; split. apply MKT49a; eauto. split; intros; auto.
    assert ((x < y)%q' /\ \[x\] <> \[y\]) as []; auto.
    apply (R_Ord_Reasonable x x0 y y0) in H9; auto.
Qed.

(* 验证 R0 小于R1. *)
Property R0_lt_R1 : R0 < R1.
Proof.
  apply R_Ord_Instantiate; auto with Q'. split. apply Q'0_lt_Q'1; auto. intro.
  symmetry in H. apply R_Q'_Property in H; auto with Q'.
  assert (Q'1 - Q'0 = Q'1)%q'. { rewrite Q'_Minus_Property2; auto with Q'. }
  rewrite H0 in H. clear H0. pose proof Q'0_lt_Q'1. pose proof H0.
  apply mt_Q'0_Q'Abs in H1; auto with Q'. apply AxiomII in H as [_[]].
  rewrite H1 in *. clear H1.
  assert (Q'1 ∈ (Q'_N ~ [Q'0])).
  { pose proof Q'0_in_Q'. apply MKT4'; split. apply Q'1_in_Q'_N; auto.
    apply AxiomII; split; eauto. intro. apply MKT41 in H3; eauto.
    elim Q'0_isnot_Q'1; auto. }
  apply H2 in H1. rewrite Q'_Divide_Property2 in H1; auto.
  elim (Q'_Ord_irReflex Q'1 Q'1); auto.
Qed.

Global Hint Resolve R0_lt_R1 : R.

(* R上定义的 R_Ord关系 具有反自反性. *)
Property R_Ord_irReflex : ∀ u v, u = v -> ~ u < v.
Proof. intros. intro. apply AxiomII' in H0 as [H0[]]; auto. Qed.

(* R上定义的 R_Ord关系 具有可传递性.  *)
Property R_Ord_Trans : ∀ u v w, u ∈ Ｒ -> v ∈ Ｒ -> w ∈ Ｒ
  -> u < v -> v < w -> u < w.
Proof.
  Open Scope q'_scope.
  intros. inR H x. inR H0 y. inR H1 z. rewrite H5,H7,H9 in *.
  apply R_Ord_Instantiate in H2 as []; apply R_Ord_Instantiate in H3 as []; auto.
  apply R_Ord_Instantiate; auto. split.
  - apply (Q'_Ord_Trans x y); auto.
  - assert ((y - x) < (z - x)).
    { pose proof H4. apply Q'_Neg in H4 as [x0[[]]]; auto.
      replace (y - x) with (y + x0). replace (z - x) with (z + x0).
      rewrite Q'_Plus_Commutation,(Q'_Plus_Commutation z); auto.
      apply Q'_Plus_PrOrder; auto. symmetry.
      apply Q'_Minus_Plus; auto with Q'.
      rewrite <-Q'_Plus_Association,(Q'_Plus_Commutation x),
      Q'_Plus_Association,H13,Q'_Plus_Property; auto.
      symmetry. apply Q'_Minus_Plus; auto with Q'.
      rewrite <-Q'_Plus_Association,(Q'_Plus_Commutation x),
      Q'_Plus_Association,H13,Q'_Plus_Property; auto. }
    assert (Q'0 < (y - x)).
    { pose proof H4. apply Q'_Neg in H4 as [x0[[]]]; auto.
      replace (y - x) with (y + x0). rewrite <-H14,Q'_Plus_Commutation,
      (Q'_Plus_Commutation y); auto. apply Q'_Plus_PrOrder; auto. symmetry.
      apply Q'_Minus_Plus; auto with Q'.
      rewrite <-Q'_Plus_Association,(Q'_Plus_Commutation x),
      Q'_Plus_Association,H14,Q'_Plus_Property; auto. }
    assert (Q'0 < (z - x)). { apply (Q'_Ord_Trans _ (y - x)); auto with Q'. }
    apply mt_Q'0_Q'Abs in H13; apply mt_Q'0_Q'Abs in H14; auto with Q'.
    assert ((z - x) ∉ I).
    { assert ((y - x) ∉ I).
      { intro. elim H10. symmetry. apply R_Q'_Property; auto. }
      intro. elim H15. apply AxiomII in H16 as [H16[]].
      assert ((y - x) ∈ Q'). { apply Q'_Minus_in_Q'; auto. }
      apply AxiomII; repeat split; eauto. intros. pose proof H20.
      apply H18 in H20. rewrite H13. rewrite H14 in H20. clear H13 H14 H18.
      assert (Q'0 < k). { apply Q'_N_Q'0_is_FirstMember; auto. }
      assert (k ∈ Q').
      { apply MKT4' in H21 as [].
        apply Q'_Arch_subset_Q',Q'_N_propersubset_Q'_Arch; auto. }
      apply (Q'_Ord_Trans _ (z - x)); auto with Q'.
      apply Q'_Divide_in_Q'; auto with Q'. intro. apply MKT4' in H21 as [].
      apply AxiomII in H22 as []. elim H23. apply MKT41; eauto with Q'. }
    intro. symmetry in H16. apply R_Q'_Property in H16; auto.
  Close Scope q'_scope.
Qed.

(* R上定义的 R_Ord关系 满足三分律.  *)
Property R_Ord_Tri : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ -> u < v \/ v < u \/ u = v.
Proof.
  intros. inR H x. inR H0 y.
  destruct (classic (u = v)); auto. assert (x ∈ Q' /\ y ∈ Q') as []; auto.
  apply (Q'_Ord_Tri x y) in H6 as [H6|[]]; auto; clear H7.
  - left. rewrite H2,H4. apply R_Ord_Instantiate; auto.
    rewrite <-H2,<-H4; auto.
  - right; left. rewrite H2,H4. apply R_Ord_Instantiate; auto.
    rewrite <-H2,<-H4; auto.
  - rewrite H2,H4,H6 in H5. contradiction.
Qed.

(* *Q中的序 与 R中序 的关联.  x<y -> [x]<=[y]*)
Property Q'_Ord_to_R_Ord : ∀ x y, x ∈ Q'_Arch -> y ∈ Q'_Arch
  -> (x < y)%q' -> \[x\] = \[y\] \/ \[x\] < \[y\].
Proof.
  intros. destruct (classic (\[x\] = \[y\])); auto.
  right. apply R_Ord_Instantiate; auto.
Qed.

(* 定义: R上的加法, u + v 就是说   任意一个和u相等的等价类[(a,b)]
                             和 任意一个和v相等的等价类[(c,d)] 做运算,
                         运算结果为等价类[(ad+bc , bd)].   *)
Definition R_Plus u v := ∩(\{ λ w, ∀ x y, x ∈ Q'_Arch -> y ∈ Q'_Arch
  -> u = \[x\] -> v = \[y\] -> w = \[(x + y)%q'\] \}).

Notation "u + v" := (R_Plus u v) : r_scope.

(* 验证 R中定义的加法运算的合理性: 对于任意R中的u和v, R上的加法定义中的{}中只有
                               一个元素, 并且该唯一的元素也在R中, 于是u与v的
                               相加结果形如 ∩[w] 是属于R且唯一的. ]     *)
Property R_Plus_Reasonable : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ -> ∃ w, w ∈ Ｒ
   /\ [w] = \{ λ w, ∀ x y, x ∈ Q'_Arch -> y ∈ Q'_Arch
     -> u = \[x\] -> v = \[y\]  -> w = \[(x + y)%q'\] \}.
Proof.
  Open Scope q'_scope.
  intros. inR H x. inR H0 y. exists (\[(x + y)%q'\])%r.
  assert (\[(x + y)%q'\] ∈ Ｒ)%r.
  { apply R_Instantiate2; try apply Q'_Arch_Plus_in_Q'_Arch; auto. }
  split; auto. apply AxiomI; split; intros.
  - apply MKT41 in H6; eauto. apply AxiomII; split. rewrite H6; eauto.
    intros. rewrite H6.
    apply R_Q'_Property; try apply Q'_Arch_Plus_in_Q'_Arch; auto.
    assert ((x + y) - (x0 + y0) = (x - x0) + (y - y0)).
    { apply Q'_Arch_subset_Q' in H7; apply Q'_Arch_subset_Q' in H8; auto.
      apply (Q'_Plus_Cancellation (x0 + y0)); auto with Q'.
      rewrite <-Q'_Mix_Association1,(Q'_Plus_Commutation (x0 + y0)),
      Q'_Mix_Association1; auto with Q'.
      assert ((x0 + y0) - (x0 + y0) = Q'0).
      { apply Q'_Minus_Plus; try rewrite Q'_Plus_Property; auto with Q'. }
      rewrite H11. rewrite Q'_Plus_Property,<-Q'_Plus_Association,
      (Q'_Plus_Commutation (x0 + y0)),<-Q'_Plus_Association,
      (Q'_Plus_Commutation _ x0),<-(Q'_Mix_Association1 x0),
      (Q'_Plus_Commutation _ x),Q'_Mix_Association1; auto with Q'.
      assert (x0 - x0 = Q'0).
      { apply Q'_Minus_Plus; try rewrite Q'_Plus_Property; auto with Q'. }
      rewrite H12,Q'_Plus_Property,Q'_Plus_Association,
      <-Q'_Mix_Association1,(Q'_Plus_Commutation y0 y),
      Q'_Mix_Association1; auto with Q'.
      assert (y0 - y0 = Q'0).
      { apply Q'_Minus_Plus; try rewrite Q'_Plus_Property; auto with Q'. }
      rewrite H13,Q'_Plus_Property; auto. }
    pose proof H7; pose proof H8. rewrite H11.
    apply Q'_Arch_subset_Q' in H7; apply Q'_Arch_subset_Q' in H8; auto.
    apply I_Plus_in_I; auto. rewrite H2 in H9. apply R_Q'_Property; auto.
    rewrite H4 in H10. apply R_Q'_Property; auto.
  - apply AxiomII in H6 as []. apply MKT41; eauto.
  Close Scope q'_scope.
Qed.

Property R_Plus_Instantiate : ∀ x y, x ∈ Q'_Arch -> y ∈ Q'_Arch
  -> (\[x\]) + (\[y\]) = \[(x + y)%q'\].
Proof.
  intros. assert (\[x\] ∈ Ｒ). { apply R_Instantiate2; auto. }
  assert (\[y\] ∈ Ｒ). { apply R_Instantiate2; auto. }
  pose proof H1. apply (R_Plus_Reasonable (\[x\]) (\[y\])) in H3 as [u[]]; auto.
  unfold R_Plus. rewrite <-H4. assert (u ∈ [u]). { apply MKT41; eauto. }
  rewrite H4 in H5. clear H4. apply AxiomII in H5 as [].
  assert (u = \[(x + y)%q'\]). { apply H5; auto. }
  rewrite <-H6. apply MKT44; auto.
Qed.

(* 进一步验证 R上定义的加法对R封闭 *)
Property R_Plus_in_R : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ -> (u + v) ∈ Ｒ.
Proof.
  intros. pose proof H. apply (R_Plus_Reasonable u v) in H1 as [a[]]; auto.
  assert (a ∈ [a]). { apply MKT41; eauto. }
  rewrite H2 in H3. clear H2. apply AxiomII in H3 as [].
  inR H x. inR H0 y. rewrite H5,H7. pose proof H.
  apply (H3 x y) in H8; auto. rewrite R_Plus_Instantiate,<-H8; auto.
Qed.

Global Hint Resolve R_Plus_in_R : R.

(* 定义: R上的乘法, u * v 就是说   任意一个和u相等的等价类[x]
                              和 任意一个和v相等的等价类[y] 做运算,
                                 运算结果为等价类[x*y].   *)
Definition R_Mult u v := ∩(\{ λ w, ∀ x y, x ∈ Q'_Arch -> y ∈ Q'_Arch
  -> u = \[x\] -> v = \[y\] -> w = \[(x · y)%q'\] \}).

Notation "u · v" := (R_Mult u v) : r_scope.

(* 验证 R中定义的乘法运算的合理性: 对于任意R中的u和v, R上的乘法定义中的{}中只有
                               一个元素, 并且该唯一的元素也在R中, 于是u与v的
                               相乘结果形如 ∩[a] 是属于R且唯一的.       *)
Property R_Mult_Reasonable : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ -> ∃ w, w ∈ Ｒ
  /\ [w] = \{ λ w, ∀ x y, x ∈ Q'_Arch -> y ∈ Q'_Arch
    -> u = \[x\] -> v = \[y\] -> w = \[(x · y)%q'\] \}.
Proof.
  Open Scope q'_scope.
  intros. inR H x. inR H0 y. exists (\[(x · y)%q'\])%r.
  assert (\[(x · y)%q'\] ∈ Ｒ)%r.
  { apply R_Instantiate2; try apply Q'_Arch_Mult_in_Q'_Arch; auto. }
  split; auto. apply AxiomI; split; intros.
  - apply MKT41 in H6; eauto. apply AxiomII; split. rewrite H6; eauto. intros.
    rewrite H6. apply R_Q'_Property; try apply Q'_Arch_Mult_in_Q'_Arch; auto.
    rewrite H2 in H9; rewrite H4 in H10.
    apply R_Q'_Property in H9; apply R_Q'_Property in H10; auto.
    assert ((x · y) - (x0 · y0) = (y · (x - x0)) + (x0 · (y - y0))).
    { pose proof H7; pose proof H8.
      apply Q'_Arch_subset_Q' in H11; auto.
      apply Q'_Arch_subset_Q' in H12; auto.
      rewrite Q'_Mult_Distribution_Minus,
      Q'_Mult_Distribution_Minus,<-Q'_Mix_Association1,
      (Q'_Plus_Commutation _ (x0 · y)),
      <-Q'_Mix_Association1,(Q'_Plus_Commutation _ (y · x)),
      Q'_Mix_Association1,(Q'_Mult_Commutation y),
      (Q'_Mult_Commutation y); auto with Q'.
      assert ((x0 · y) - (x0 · y) = Q'0).
      { apply Q'_Minus_Plus; try rewrite Q'_Plus_Property; auto with Q'. }
      rewrite H13,Q'_Plus_Property; auto with Q'. }
    rewrite H11. apply I_Plus_in_I; auto; try rewrite Q'_Mult_Commutation;
    try apply Q'_Arch_subset_Q'; auto with Q'.
  - apply AxiomII in H6 as []. apply MKT41; eauto.
  Close Scope q'_scope.
Qed.

Property R_Mult_Instantiate : ∀ x y, x ∈ Q'_Arch -> y ∈ Q'_Arch
  -> \[x\] · \[y\] = \[(x · y)%q'\].
Proof.
  intros. assert (\[x\] ∈ Ｒ). { apply R_Instantiate2; auto. }
  assert (\[y\] ∈ Ｒ). { apply R_Instantiate2; auto. }
  pose proof H1. apply (R_Mult_Reasonable (\[x\]) (\[y\])) in H3 as [u[]]; auto.
  unfold R_Mult. rewrite <-H4. assert (u ∈ [u]). { apply MKT41; eauto. }
  rewrite H4 in H5. clear H4. apply AxiomII in H5 as [].
  assert (u = \[(x · y)%q'\]). { apply H5; auto. }
  rewrite <-H6. apply MKT44; auto.
Qed.

(* 进一步验证 R上定义的乘法对R封闭 *)
Property R_Mult_in_R : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ -> (u · v) ∈ Ｒ.
Proof.
  intros. pose proof H.
  apply (R_Mult_Reasonable u v) in H1 as [a[]]; auto.
  assert (a ∈ [a]). { apply MKT41; eauto. }
  rewrite H2 in H3. clear H2. apply AxiomII in H3 as [].
  inR H x. inR H0 y. rewrite H5,H7. pose proof H.
  apply (H3 x y) in H8; auto. rewrite R_Mult_Instantiate,<-H8; auto.
Qed.

Global Hint Resolve R_Mult_in_R : R.

(* 验证 R中的关于零元的性质:
       u + R0 = u  ;  u * R0 = R0  ;  无零因子 *)
Property R_Plus_Property : ∀ u, u ∈ Ｒ -> u + R0 = u.
Proof.
  intros. inR H x. unfold R0. rewrite H1,R_Plus_Instantiate; auto with Q'.
  apply R_Q'_Property; auto with Q'.
  rewrite Q'_Plus_Property; auto. apply R_Q'_Property; auto.
Qed.

(* 验证 R中的加法满足交换律. *)
Property R_Plus_Commutation : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ -> u + v = v + u.
Proof.
  intros. inR H x. inR H0 y.
  rewrite H2,H4,R_Plus_Instantiate,R_Plus_Instantiate; auto.
  rewrite Q'_Plus_Commutation; auto.
Qed.

(* 验证 R中的加法满足结合律 *)
Property R_Plus_Association : ∀ u v w, u ∈ Ｒ -> v ∈ Ｒ -> w ∈ Ｒ
  -> (u + v) + w = u + (v + w).
Proof.
  intros. inR H x. inR H0 y. inR H1 z.
  rewrite H3,H5,H7,R_Plus_Instantiate,R_Plus_Instantiate,
  R_Plus_Instantiate,R_Plus_Instantiate,Q'_Plus_Association; auto with Q'.
Qed.

(* 验证 R中的加法满足消去律 *)
Property R_Plus_Cancellation : ∀ u v w, u ∈ Ｒ -> v ∈ Ｒ -> w ∈ Ｒ
  -> u + v = u + w -> v = w.
Proof.
  intros. inR H x. inR H0 y. inR H1 z. rewrite H4,H6,H8 in *.
  rewrite R_Plus_Instantiate,R_Plus_Instantiate in H2; auto.
  apply R_Q'_Property in H2; auto with Q'. apply R_Q'_Property; auto.
  assert ((x + y) - (x + z) = y - z)%q'.
  { apply Q'_Minus_Plus; auto with Q'. rewrite Q'_Plus_Association; auto with Q'.
    assert (z + (y - z) = y)%q'.
    { rewrite <-Q'_Mix_Association1,Q'_Plus_Commutation,Q'_Mix_Association1; auto.
      assert (z - z = Q'0)%q'.
      { apply Q'_Minus_Plus; try rewrite Q'_Plus_Property; auto with Q'. }
      rewrite H9,Q'_Plus_Property; auto with Q'. }
    rewrite H9; auto. }
  rewrite <-H9; auto.
Qed.

(* R上定义的 R_Ord关系 满足加法保序 (需注意和 消去律 的区别).  *)
Property R_Plus_PrOrder : ∀ u v w, u ∈ Ｒ -> v ∈ Ｒ -> w ∈ Ｒ
  -> u < v <-> (w + u) < (w + v).
Proof.
  intros. inR H x. inR H0 y. inR H1 z. rewrite H3,H5,H7.
  rewrite R_Plus_Instantiate,R_Plus_Instantiate; auto.
  assert ((z + x) - (z + y) = x - y)%q'.
  { apply Q'_Minus_Plus; auto with Q'.
    rewrite <-Q'_Mix_Association1,Q'_Plus_Association,
    (Q'_Plus_Commutation y x),<-Q'_Plus_Association,
    Q'_Mix_Association1,Q'_Minus_Property1,Q'_Plus_Property; auto with Q'. }
  split; intros.
  - apply R_Ord_Instantiate in H9 as []; auto.
    apply R_Ord_Instantiate; auto with Q'. split.
    + apply Q'_Plus_PrOrder; auto.
    + intro. elim H10. apply R_Q'_Property in H11; auto with Q'.
      apply R_Q'_Property; auto with Q'. rewrite <-H8; auto.
  - apply R_Ord_Instantiate in H9 as []; auto with Q'.
    apply R_Ord_Instantiate; auto. split.
    + apply Q'_Plus_PrOrder in H9; auto.
    + intro. elim H10. apply R_Q'_Property in H11; auto.
      apply R_Q'_Property; auto with Q'. rewrite H8; auto.
Qed.

Corollary R_Plus_PrOrder_Corollary : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ
  -> u < v <-> ∃! w, w ∈ Ｒ /\ R0 < w /\ u + w = v.
Proof.
  intros. pose proof H as Ha; pose proof H0 as Hb. inR H x. inR H0 y.
  split; intros.
  - pose proof H5. rewrite H2,H4 in H6.
    apply R_Ord_Instantiate in H6 as []; auto. pose proof H6.
    apply Q'_Plus_PrOrder_Corollary in H8 as [z[[H8[]]]]; auto.
    exists (\[z\]). assert (z ∈ Q'_Arch).
    { destruct NPAUF as [_]. apply NNPP; intro.
        assert (z ∈ (Q' ~ Q'_Arch)).
        { apply MKT4'; split; auto. apply AxiomII; split; eauto. }
        pose proof H8. apply Q'_Arch_lt_Q'_Infty_Abs in H15 as []; auto.
        clear H16. assert (y ∈ (Q' ~ Q'_Arch)).
        { rewrite <-H10,Q'_Plus_Commutation; auto.
          apply infinity_Plus_finity; auto. }
        apply MKT4' in H16 as []. apply AxiomII in H17 as []; auto. }
    assert (~ z ∈ I).
    { intro. apply Q'_Minus_Plus in H10; auto. rewrite <-H10 in H13. elim H7.
      symmetry. apply R_Q'_Property; auto. }
    repeat split.
    + apply R_Instantiate2; auto.
    + unfold R0. apply R_Ord_Instantiate; auto with Q'. split; auto. intro.
      symmetry in H14. apply R_Q'_Property in H14; auto with Q'.
      rewrite Q'_Minus_Property2 in H14; auto.
    + rewrite H2,R_Plus_Instantiate,H10; auto.
    + intros w [H14[]]. inR H14 z0. rewrite H18. symmetry.
      apply R_Q'_Property; auto. rewrite H2,H4,H18,R_Plus_Instantiate in H16; auto.
      apply R_Q'_Property in H16; auto with Q'. rewrite <-H10 in H16.
      replace (z0 - z)%q' with ((x + z0) - (x + z))%q'; auto.
      apply Q'_Minus_Plus; auto with Q'.
      rewrite <-Q'_Mix_Association1,Q'_Plus_Association,
      (Q'_Plus_Commutation z z0),<-Q'_Plus_Association,
      Q'_Mix_Association1,Q'_Minus_Property1,Q'_Plus_Property; auto with Q'.
  - destruct H5 as [w[[H5[]]]].
    assert (u ∈ Ｒ /\ v ∈ Ｒ) as [].
    { split; try rewrite H3; try rewrite H5; try apply R_Instantiate2; auto. }
    apply (R_Ord_Tri u v) in H9 as [H9|[]]; auto; clear H10.
    + apply (R_Plus_PrOrder _ _ w) in H9; apply (R_Plus_PrOrder _ _ v) in H6;
      try apply R0_in_R; auto. rewrite R_Plus_Property in H6; auto.
      rewrite R_Plus_Commutation,(R_Plus_Commutation w) in H9; auto.
      apply (R_Ord_Trans v) in H9; try apply R_Plus_in_R; auto.
      rewrite H7 in H9. elim (R_Ord_irReflex v v); auto.
    + apply (R_Plus_PrOrder _ _ u) in H6; try apply R0_in_R; auto.
      rewrite R_Plus_Property in H6; auto. rewrite H7,H9 in H6.
      elim (R_Ord_irReflex v v); auto.
Qed.

(* 验证 R中负元的性质:
       对任意R中的元u, 存在唯一的负元v使得 u+v=0. *)
Property R_Neg_Property : ∀ u, u ∈ Ｒ -> ∃! v, v ∈ Ｒ /\ u + v = R0.
Proof.
  intros. inR H x. pose proof H0. apply Q'_Neg in H2 as [x0[[]]]; auto.
  exists (\[x0\]). assert (x0 ∈ Q'_Arch).
  { apply AxiomII; repeat split; eauto. apply AxiomII in H as [H[H5[k[]]]].
    exists k. assert (|x| = |x0|)%q'. { apply Neg_Q'Abs_Equ; auto. }
    rewrite <-H8; auto. }
  assert (\[x0\] ∈ Ｒ). { apply R_Instantiate2; auto. }
  assert (u + \[x0\] = R0). { rewrite H1,R_Plus_Instantiate,H3; auto. }
  repeat split; auto. intros x1 []. rewrite <-H7 in H9.
  apply R_Plus_Cancellation in H9; auto.
  rewrite H1. apply R_Instantiate2; auto.
Qed.

(* 负元具体化:
       对任意 *Q_Arch 中的元x, 和R中的元u, 若[x] + u = 0, 则u = [-x].  *)
Property R_Neg_Instantiate : ∀ x x0 u, x ∈ Q'_Arch -> x0 ∈ Q'_Arch
  -> u ∈ Ｒ -> (x + x0 = Q'0)%q' -> \[x\] + u = R0 -> u = \[x0\].
Proof.
  intros. inR H1 y. rewrite H5 in *. rewrite R_Plus_Instantiate in H3; auto.
  apply R_Q'_Property in H3;auto with Q'.
  assert ((x + y) - Q'0 = x + y)%q'.
  { apply Q'_Minus_Plus; try apply Q'_Arch_subset_Q'; auto with Q'.
    rewrite Q'_Plus_Commutation,Q'_Plus_Property;
    try apply Q'_Arch_subset_Q'; auto with Q'. }
  rewrite H6 in H3.
  assert ((x + y) - (x + x0) = y - x0)%q'.
  { apply Q'_Minus_Plus; try apply Q'_Arch_subset_Q'; auto with Q'.
    rewrite <-Q'_Mix_Association1,(Q'_Plus_Commutation _ y),
    <-Q'_Plus_Association,Q'_Mix_Association1,
    (Q'_Plus_Commutation x); try apply Q'_Arch_subset_Q'; auto with Q'.
    assert (x0 - x0 = Q'0)%q'.
    { apply Q'_Minus_Plus; try apply Q'_Plus_Property;
      try apply Q'_Arch_subset_Q'; auto with Q'. }
    rewrite H7,Q'_Plus_Property; try apply Q'_Arch_subset_Q'; auto with Q'. }
  rewrite H2 in H7. apply Q'_Minus_Plus in H7;
  try apply Q'_Arch_subset_Q'; auto with Q'.
  rewrite Q'_Plus_Commutation,Q'_Plus_Property in H7;
  try apply Q'_Arch_subset_Q'; auto with Q'.
  apply R_Q'_Property; auto. rewrite H7; auto.
Qed.

Property R_Mult_Property1 : ∀ u, u ∈ Ｒ -> u · R0 = R0.
Proof.
  intros. inR H x. unfold R0. rewrite H1,R_Mult_Instantiate; auto with Q'.
  apply R_Q'_Property; auto with Q'. rewrite Q'_Mult_Property1; auto.
  apply R_Q'_Property; auto with Q'.
Qed.

(* 验证 R中的关于幺元的性质: u * R1 = u *)
Property R_Mult_Property2 : ∀ u, u ∈ Ｒ -> u · R1 = u.
Proof.
  intros. inR H x. unfold R1.
  rewrite H1,R_Mult_Instantiate,Q'_Mult_Property2; auto with Q'.
Qed.

(* 无零因子 *)
Property R_Mult_Property3 : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ -> u · v = R0
  -> u = R0 \/ v = R0.
Proof.
  intros. inR H x. inR H0 y. unfold R0 in *.
  rewrite H3,H5,R_Mult_Instantiate in *; auto.
  apply R_Q'_Property in H1; auto with Q'.
  rewrite Q'_Minus_Property2 in H1; auto with Q'.
  apply I_Mult_in_I_Corollary in H1 as []; auto;
  [(left)|right]; apply R_Q'_Property;
  try rewrite Q'_Minus_Property2; auto with Q'.
Qed.

(* 验证 R中的乘法满足交换律. *)
Property R_Mult_Commutation : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ -> u · v = v · u.
Proof.
  intros. inR H x. inR H0 y.
  rewrite H2,H4,R_Mult_Instantiate,R_Mult_Instantiate; auto.
  rewrite Q'_Mult_Commutation; auto.
Qed.

(* 验证 R中的乘法满足结合律 *)
Property R_Mult_Association : ∀ u v w, u ∈ Ｒ -> v ∈ Ｒ -> w ∈ Ｒ
  -> (u · v) · w = u · (v · w).
Proof.
  intros. inR H x. inR H0 y. inR H1 z.
  rewrite H3,H5,H7,R_Mult_Instantiate,R_Mult_Instantiate,
  R_Mult_Instantiate,R_Mult_Instantiate,Q'_Mult_Association; auto with Q'.
Qed.

(* 验证 R中的乘法满足分配律. *)
Property R_Mult_Distribution : ∀ u v w, u ∈ Ｒ -> v ∈ Ｒ -> w ∈ Ｒ
  -> u · (v + w) = (u · v) + (u · w).
Proof.
  intros. inR H x. inR H0 y. inR H1 z.
  rewrite H3,H5,H7,R_Plus_Instantiate,R_Mult_Instantiate,
  R_Mult_Instantiate,R_Mult_Instantiate,R_Plus_Instantiate,
  Q'_Mult_Distribution; auto with Q'.
Qed.

(* 验证: 乘法消去律 *)
Property R_Mult_Cancellation : ∀ w u v, w ∈ Ｒ -> u ∈ Ｒ -> v ∈ Ｒ
  -> w <> R0 -> w · u = w · v -> u = v.
Proof.
  intros. inR H z. inR H0 x. inR H1 y. rewrite H5,H7,H9 in *.
  rewrite R_Mult_Instantiate,R_Mult_Instantiate in H3; auto.
  apply R_Q'_Property in H3; auto with Q'.
  rewrite <-Q'_Mult_Distribution_Minus in H3; auto. apply R_Q'_Property; auto.
  apply I_Mult_in_I_Corollary in H3 as []; auto with Q'. elim H2.
  apply R_Q'_Property; auto with Q'. rewrite Q'_Minus_Property2; auto.
Qed.

(* R上定义的 R_Ord关系 满足乘法保序. *)
Property R_Mult_PrOrder : ∀ u v w, u ∈ Ｒ -> v ∈ Ｒ -> w ∈ Ｒ -> R0 < w
  -> u < v <-> (w · u) < (w · v).
Proof.
  intros. inR H x. inR H0 y. inR H1 z. rewrite H4,H6,H8 in *.
  rewrite R_Mult_Instantiate,R_Mult_Instantiate; auto.
  apply R_Ord_Instantiate in H2 as []; auto with Q'.
  assert (~ z ∈ I).
  { intro. elim H9. symmetry. apply R_Q'_Property; auto with Q'.
    rewrite Q'_Minus_Property2; auto. }
  split; intros.
  - apply R_Ord_Instantiate in H11 as []; auto.
    apply R_Ord_Instantiate; auto with Q'. split.
    + apply Q'_Mult_PrOrder; auto.
    + intro. apply R_Q'_Property in H13; auto with Q'.
      rewrite <-Q'_Mult_Distribution_Minus in H13; auto.
      apply I_Mult_in_I_Corollary in H13 as []; auto with Q'.
      elim H12. apply R_Q'_Property; auto.
  - apply R_Ord_Instantiate in H11 as []; auto with Q'.
    apply R_Ord_Instantiate; auto. split.
    + apply Q'_Mult_PrOrder in H11; auto.
    + intro. apply R_Q'_Property in H13; auto. elim H12.
      apply R_Q'_Property; auto with Q'.
      rewrite <-Q'_Mult_Distribution_Minus,Q'_Mult_Commutation; auto with Q'.
Qed.

(* 验证 R中逆元的性质:
       对任意R中的非零元u, 存在唯一的逆元v使得 u*v=1. *)
Property R_Inv : ∀ u, u ∈ Ｒ -> u <> R0
  -> ∃! v, v ∈ Ｒ /\ v <> R0 /\ u · v = R1.
Proof.
  intros. inR H x. assert (x <> Q'0).
  { intro. elim H0. unfold R0. rewrite <-H3; auto. }
  pose proof H1. apply (Q'_Inv x) in H4 as [x1[[H4[]]]]; auto.
  exists (\[x1\]). assert (~ x ∈ I).
  { intro. elim H0. rewrite H2. unfold R0. apply R_Q'_Property; auto with Q'.
    rewrite Q'_Minus_Property2; auto. }
  assert (x1 ∈ Q'_Arch).
  { destruct NPAUF as [_]. apply NNPP; intro.
      assert (x1 ∈ (Q' ~ Q'_Arch)).
      { apply MKT4'; split; auto. apply AxiomII; split; eauto. }
      apply (I_inv_Property2 x1 x) in H11; auto. apply MKT4' in H11 as []; auto.
      rewrite Q'_Mult_Commutation; auto. }
  assert (\[x1\] ∈ Ｒ). { apply R_Instantiate2; auto. }
  assert (\[x1\] <> R0).
  { intro. apply R_Q'_Property in H11; auto with Q'.
    rewrite Q'_Minus_Property2 in H11; auto.
    assert ((x · x1)%q' ∈ I).
    { rewrite Q'_Mult_Commutation; auto. auto with Q'. }
    rewrite H6 in H12. apply AxiomII in H12 as [H12[]].
    assert (Q'1 ∈ (Q'_N ~ [Q'0])).
    { apply MKT4'; split. apply Q'1_in_Q'_N; auto.
      apply AxiomII; split; auto. intro. apply MKT41 in H15.
      elim Q'0_isnot_Q'1; auto. pose proof Q'0_in_Q'. eauto. }
    apply H14 in H15. rewrite mt_Q'0_Q'Abs,Q'_Divide_Property2 in H15; auto with Q'.
    elim (Q'_Ord_irReflex Q'1 Q'1); auto. }
  assert (u · \[x1\] = R1). { rewrite H2,R_Mult_Instantiate,H6; auto. }
  repeat split; auto. intros y [H13[]]. inR H13 y1.
  rewrite H2,H17,R_Mult_Instantiate in H15; auto.
  rewrite H2,R_Mult_Instantiate in H12; auto. rewrite <-H12 in H15.
  apply R_Q'_Property in H15; auto with Q'.
  rewrite <-Q'_Mult_Distribution_Minus in H15; auto.
  apply I_Mult_in_I_Corollary in H15 as []; auto with Q'.
  elim H8; auto. rewrite H17. symmetry. apply R_Q'_Property; auto.
Qed.

(* 逆元具体化:
       对任意 *Q_Arch 中的元x, 和R中的元u, 若[x] * u = 1, 则u = [x^-1]. *)
Property R_Inv_Instantiate : ∀ x x1 u, x ∈ Q'_Arch -> x1 ∈ Q'_Arch
  -> u ∈ Ｒ -> (x · x1 = Q'1)%q' -> \[x\] · u = R1 -> u = \[x1\].
Proof.
  intros. inR H1 y. rewrite H5. apply R_Q'_Property; auto.
  rewrite H5,R_Mult_Instantiate in H3; auto. unfold R1 in H3.
  apply R_Q'_Property in H3; auto with Q'.
  rewrite <-H2,<-Q'_Mult_Distribution_Minus in H3;
  try apply Q'_Arch_subset_Q'; auto.
  apply I_Mult_in_I_Corollary in H3 as []; try apply Q'_Arch_subset_Q';
  auto with Q'. destruct NPAUF as [_]. apply I_Inv_Property1 in H2;
  try apply Q'_Arch_subset_Q'; auto. apply MKT4' in H2 as [].
  apply AxiomII in H7 as []. elim H8; auto. apply MKT4'; split; auto.
  apply AxiomII; split; eauto. intro. pose proof Q'0_in_Q'.
  apply MKT41 in H7; eauto. rewrite Q'_Mult_Commutation,H7,Q'_Mult_Property1
  in H2; try apply Q'_Arch_subset_Q'; auto. elim Q'0_isnot_Q'1; auto.
Qed.

(* 定义: R中的减法. *)
Definition R_Minus v u := ∩(\{ λ w, w ∈ Ｒ /\ u + w = v \}).
(*  {}中元素的唯一性已经由上一条预定理所保证, 于是此定义的合理性也随之成立. *)

Notation "u - v" := (R_Minus u v) : r_scope.

(* 减法合理性: 任何R中的u和v, 都存在唯一u0使得 u + u0 = v. *)
Property R_Minus_Reasonable : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ
  -> ∃! u0, u0 ∈ Ｒ /\ u + u0 = v.
Proof.
  intros. assert (u ∈ Ｒ /\ v ∈ Ｒ) as []; auto.
  apply (R_Ord_Tri u v) in H1 as [H1|[]]; auto; clear H2.
  - apply R_Plus_PrOrder_Corollary in H1 as [x[[H1[]]]]; auto.
    exists x. repeat split; auto. intros x' []. rewrite <-H3 in H6.
    apply R_Plus_Cancellation in H6; auto.
  - apply R_Plus_PrOrder_Corollary in H1 as [x[[H1[]]]]; auto.
    pose proof H1. apply R_Neg_Property in H5 as [x0[[]]]; auto.
    exists x0. repeat split; auto.
    rewrite <-H3,R_Plus_Association,H6,R_Plus_Property; auto.
    intros x' []. rewrite <-H3,R_Plus_Association in H9; auto.
    assert (v + (x + x') = v + R0). { rewrite R_Plus_Property; auto. }
    apply R_Plus_Cancellation in H10; auto. apply R_Plus_in_R; auto.
    apply R0_in_R; auto.
  - exists R0. pose proof R0_in_R. repeat split; auto.
    rewrite R_Plus_Property; auto. intros x []. rewrite H1 in H4.
    assert (v + x = v + R0). { rewrite R_Plus_Property; auto. }
    apply R_Plus_Cancellation in H5; auto.
Qed.

(* 减法和加法的关系 *)
Property R_Minus_Plus : ∀ u w v, u ∈ Ｒ -> w ∈ Ｒ -> v ∈ Ｒ
  -> u + w = v <-> v - u = w.
Proof.
  split; intros.
  - assert (\{ λ w, w ∈ Ｒ /\ u + w = v \} = [w]).
    { apply AxiomI; split; intros. apply AxiomII in H3 as [].
      apply (R_Minus_Reasonable u v) in H as [x[[]]]; auto.
      apply MKT41; eauto. assert (x = w). { apply H6; auto. }
      assert (x = z). { apply H6; auto. }
      rewrite <-H7,<-H8; auto. apply MKT41 in H3; eauto.
      rewrite H3. apply AxiomII; split; eauto. }
    unfold R_Minus. rewrite H3. destruct (@ MKT44 w); eauto.
  - assert (∃ x, Ensemble x /\ [x] = \{ λ a, a ∈ Ｒ /\ u + a = v \}).
    { pose proof H. apply (R_Minus_Reasonable u v) in H3 as [x[[]]]; auto.
      exists x. split; eauto. apply AxiomI; split; intros.
      apply MKT41 in H6; eauto. rewrite H6. apply AxiomII; split; eauto.
      apply AxiomII in H6 as [H6[]]. apply MKT41; eauto.
      symmetry. apply H5; auto. }
    destruct H3 as [x[]]. unfold R_Minus in H2. rewrite <-H4 in H2.
    destruct (@ MKT44 x); auto. rewrite H5 in H2.
    assert (x ∈ [x]). { apply MKT41; auto. }
    rewrite H4 in H7. apply AxiomII in H7 as [H7[]]. rewrite <-H2; auto.
Qed.

(* 验证: R中定义的减法在R中封闭. *)
Property R_Minus_in_R : ∀ v u, v ∈ Ｒ -> u ∈ Ｒ -> (v - u) ∈ Ｒ.
Proof.
  intros. pose proof H. apply (R_Minus_Reasonable u) in H1 as [x[[]]]; auto.
  apply R_Minus_Plus in H2; auto. rewrite H2; auto.
Qed.

Global Hint Resolve R_Minus_in_R : R.

(* 定义: R中的除法. *)
Definition R_Divide v u := ∩(\{ λ w, w ∈ Ｒ /\ u <> R0 /\ u · w = v \}).

Notation "v / u" := (R_Divide v u) : r_scope.

(* 除法合理性: 任何R中的非零u和任何v, 都存在唯一w使得 u · w = v. *)
Property R_Divide_Reasonable : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ -> u <> R0
  -> ∃! w, w ∈ Ｒ /\ u · w = v.
Proof.
  intros. pose proof H. apply R_Inv in H2 as [w[[H2[]]]]; auto.
  exists (w · v). repeat split; auto with R.
  - rewrite <-R_Mult_Association,H4,R_Mult_Commutation,
    R_Mult_Property2; auto with R.
  - intros x []. rewrite <-H7,<-R_Mult_Association,(R_Mult_Commutation w),
    H4,R_Mult_Commutation,R_Mult_Property2; auto with R.
Qed.

(* 除法和乘法的关系 *)
Property R_Divide_Mult : ∀ u w v, u ∈ Ｒ -> u <> R0 -> w ∈ Ｒ -> v ∈ Ｒ
  -> u · w = v <-> v / u = w.
Proof.
  split; intros.
  - assert (\{ λ x, x ∈ Ｒ /\ u <> R0 /\ u · x = v \} = [w]).
    { apply AxiomI; split; intros.
      - apply AxiomII in H4 as [_[H4[]]]. rewrite <-H3 in H6.
        apply MKT41; eauto. apply (R_Mult_Cancellation u); auto.
      - apply AxiomII; split; eauto. apply MKT41 in H4; eauto. subst; auto. }
    unfold R_Divide. rewrite H4. apply MKT44; eauto.
  - assert (∃ a, Ensemble a
      /\ [a] = \{ λ x, x ∈ Ｒ /\ u <> R0 /\ u · x = v \}) as [a[]].
    { pose proof H. apply (R_Divide_Reasonable u v) in H4 as [a[[]]]; auto.
      exists a. split; eauto. apply AxiomI; split; intros.
      - apply MKT41 in H7; eauto. rewrite H7. apply AxiomII; split; eauto.
      - apply AxiomII in H7 as [_[H7[]]]. apply MKT41; eauto. rewrite <-H5 in H9.
        apply R_Mult_Cancellation in H9; auto. }
    unfold R_Divide in H3. rewrite <-H5 in H3.
    assert (a ∈ [a]). { apply MKT41; auto. }
    rewrite H5 in H6. apply AxiomII in H6 as [_[H6[]]].
    apply MKT44 in H4 as [H4 _]. rewrite <-H3,H4; auto.
Qed.

(* 验证: R中定义的除法在R中封闭. *)
Property R_Divide_in_R : ∀ v u, v ∈ Ｒ -> u ∈ Ｒ -> u <> R0
  -> (v / u) ∈ Ｒ.
Proof.
  intros. pose proof H0. apply (R_Divide_Reasonable u v) in H2 as [w[[]]]; auto.
  apply R_Divide_Mult in H3; auto. rewrite H3; auto.
Qed.

Global Hint Resolve R_Divide_in_R : R.

(* u - u = 0 *)
Property R_Minus_Property1 : ∀ u, u ∈ Ｒ -> u - u = R0.
Proof.
  intros. pose proof R0_in_R. apply R_Minus_Plus; auto. 
  apply R_Plus_Property; auto.
Qed.

(* u - 0 = u *)
Property R_Minus_Property2 : ∀ u, u ∈ Ｒ -> u - R0 = u.
Proof.
  intros. pose proof R0_in_R. apply R_Minus_Plus; auto.
  rewrite R_Plus_Commutation,R_Plus_Property; auto.
Qed.

Property R_Divide_Property1 : ∀ u, u ∈ Ｒ -> u <> R0 -> u / u = R1.
Proof.
  intros. apply R_Divide_Mult; auto with R.
  rewrite R_Mult_Property2; auto.
Qed.

Property R_Divide_Property2 : ∀ u, u ∈ Ｒ -> u / R1 = u.
Proof.
  intros. apply R_Divide_Mult; auto with R.
  rewrite R_Mult_Commutation,R_Mult_Property2; auto with R.
Qed.

Property R_Divide_Property3 : ∀ v u, v ∈ Ｒ -> u ∈ Ｒ -> u <> R0
  -> u · (v / u) = v.
Proof. intros. apply R_Divide_Mult; auto. apply R_Divide_in_R; auto. Qed.

(* 验证: 加减法的混合运算结合律. *)
Property R_Mix_Association1 : ∀ u v w, u ∈ Ｒ -> v ∈ Ｒ -> w ∈ Ｒ
  -> (u + v) - w = u + (v - w).
Proof.
  intros. assert ((u + v) ∈ Ｒ). { apply R_Plus_in_R; auto. }
  pose proof H1. apply (R_Minus_Reasonable w (u + v)) in H3 as [x[[]]]; auto.
  pose proof H1. apply (R_Minus_Reasonable w v) in H6 as [y[[]]]; auto.
  apply R_Minus_Plus in H4; auto. rewrite H4,<-H7.
  assert ((w + y) - w = y).
  { apply R_Minus_Plus; auto. apply R_Plus_in_R; auto. }
  rewrite H9. rewrite <-H7 in H4.
  apply R_Minus_Plus in H4; try apply R_Plus_in_R; auto.
  rewrite <-R_Plus_Association,(R_Plus_Commutation u w),
  R_Plus_Association in H4; auto.
  apply R_Plus_Cancellation in H4; try apply R_Plus_in_R; auto.
  apply R_Plus_in_R; auto.
Qed.

Property R_Mix_Association2 : ∀ u v w, u ∈ Ｒ -> v ∈ Ｒ -> w ∈ Ｒ -> w <> R0
  -> u · (v / w) = (u · v) / w.
Proof.
  intros. apply (R_Mult_Cancellation w); auto with R.
  rewrite R_Divide_Property3; auto with R.
  rewrite <-R_Mult_Association,(R_Mult_Commutation w),
  R_Mult_Association,R_Divide_Property3; auto; apply R_Divide_in_R; auto.
Qed.

(* 乘法对减法的分配律 *)
Property R_Mult_Distribution_Minus : ∀ u v w, u ∈ Ｒ -> v ∈ Ｒ -> w ∈ Ｒ
  -> u · (v - w) = (u · v) - (u · w).
Proof.
  intros. pose proof H1. apply (R_Minus_Reasonable w v) in H2 as [x[[]]]; auto.
  pose proof H3. apply R_Minus_Plus in H5; auto.
  rewrite H5,<-H3. rewrite R_Mult_Distribution,R_Plus_Commutation,
  R_Mix_Association1; try apply R_Mult_in_R; auto.
  assert ((u · w) - (u · w) = R0).
  { apply R_Minus_Plus; try apply R_Mult_in_R; auto. apply R0_in_R; auto.
    rewrite R_Plus_Property; try apply R_Mult_in_R; auto. }
  rewrite H6,R_Plus_Property; try apply R_Mult_in_R; auto.
Qed.

(* 定义: R中的绝对值函数, 用于表示R中元素的绝对值. *)
Definition R_Abs := \{\ λ u v, u ∈ Ｒ
  /\ ((u < R0 /\ v = R0 - u ) \/ (u = R0 /\ v = R0) \/ (R0 < u /\ v = u)) \}\.

Notation "| u | " := ((R_Abs)[u])(u at level 0, at level 5) : r_scope.

Property RAbs_is_Function : Function R_Abs /\ dom(R_Abs) = Ｒ /\ ran(R_Abs) ⊂ Ｒ.
Proof.
  intros. assert (Function R_Abs).
  { split.
    - unfold Relation; intros. apply AxiomII in H as [H[x[y[]]]]; eauto.
    - intros. apply AxiomII' in H as [H[]].
      apply AxiomII' in H0 as [H0[]]. destruct H2,H4.
      + destruct H2,H4. rewrite H5,H6; auto.
      + destruct H2,H4; destruct H4. rewrite <-H4 in H2.
        elim (R_Ord_irReflex x x); auto. apply (R_Ord_Trans x _ x) in H2; auto.
        elim (R_Ord_irReflex x x); auto. apply R0_in_R; auto.
      + destruct H2; destruct H2; destruct H4. rewrite <-H2 in H4.
        elim (R_Ord_irReflex x x); auto. apply (R_Ord_Trans x _ x) in H4; auto.
        elim (R_Ord_irReflex x x); auto. apply R0_in_R; auto.
      + destruct H2,H4; destruct H2,H4; rewrite H5,H6; auto. }
  split; auto. split.
  - apply AxiomI; split; intros.
    + apply AxiomII in H0 as [H0[y]]. apply AxiomII' in H1; tauto.
    + apply AxiomII; split; eauto. pose proof R0_in_R.
      assert (z ∈ Ｒ /\ R0 ∈ Ｒ) as []; auto.
      apply (R_Ord_Tri z R0) in H2 as [H2|[]]; auto; clear H3.
      * exists (R0 - z). apply AxiomII'; repeat split; auto.
        apply (R_Minus_in_R _ z) in H1; auto. apply MKT49a; eauto.
      * exists z. apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
      * exists z. apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
  - unfold Included; intros. apply AxiomII in H0 as [H0[]]. pose proof R0_in_R.
    apply AxiomII' in H1 as [H1[H3[H4|[]]]]; destruct H4; rewrite H5; auto.
    apply R_Minus_in_R; auto.
Qed.

(* 绝对值在R中 *)
Property RAbs_in_R : ∀ u, u ∈ Ｒ -> |u| ∈ Ｒ.
Proof.
  intros. destruct RAbs_is_Function as [H0[]].
  rewrite <-H1 in H. apply Property_Value,Property_ran in H; auto.
Qed.

Global Hint Resolve RAbs_in_R : R.

(*---------------------以下为关于绝对值的常见性质----------------------*)
(* 大于零的实数 绝对值等于本身. *)
Property mt_R0_RAbs : ∀ u, u ∈ Ｒ -> R0 < u -> |u| = u.
Proof.
  intros. destruct RAbs_is_Function as [H1[]]. rewrite <-H2 in H.
  apply Property_Value in H; auto. pose proof R0_in_R.
  apply AxiomII' in H as [H[H5[H6|[]]]]; destruct H6; auto.
  - apply (R_Ord_Trans u _ u) in H6; auto. elim (R_Ord_irReflex u u); auto.
  - rewrite <-H6 in H0. elim (R_Ord_irReflex u u); auto.
Qed.

(* 0的绝对值就是0 *)
Fact eq_R0_RAbs : ∀ u, u ∈ Ｒ -> |u| = R0 <-> u = R0.
Proof.
  intros. pose proof R0_in_R. destruct RAbs_is_Function as [H1[]].
  rewrite <-H2 in H. apply Property_Value,AxiomII' in H as [H[]]; auto.
  split; intros; destruct H5 as [H5|[]]; destruct H5; auto.
  - rewrite H7 in H6. apply R_Minus_Plus in H6; auto.
    rewrite R_Plus_Property in H6; auto.
  - rewrite H7 in H6; auto.
  - rewrite H7. apply R_Minus_Plus; auto. rewrite R_Plus_Property; auto.
  - rewrite <-H6; auto.
Qed.

(* 小于0的实数u的绝对值是0-u *)
Property lt_R0_RAbs : ∀ u, u ∈ Ｒ -> u < R0 -> |u| = R0 - u.
Proof.
  intros. pose proof R0_in_R. destruct RAbs_is_Function as [H2[]].
  rewrite <-H3 in H. apply Property_Value,AxiomII' in H as [H[]]; auto.
  destruct H6 as [H6|[]]; destruct H6; auto.
  - rewrite <-H6 in H0. elim (R_Ord_irReflex u u); auto.
  - apply (R_Ord_Trans u _ u) in H0; auto. elim (R_Ord_irReflex u u); auto.
Qed.

(* 0小于等于任何数的绝对值. *)
Property R0_le_RAbs : ∀ u, u ∈ Ｒ -> |u| ∈ Ｒ /\ (|u| = R0 \/ R0 < |u|).
Proof.
  intros. destruct RAbs_is_Function as [H0[]].
  assert (|u| ∈ Ｒ).
  { rewrite <-H1 in H. apply Property_Value,Property_ran,H2 in H; auto. }
  split; auto. pose proof R0_in_R.
  assert (R0 ∈ Ｒ /\ u ∈ Ｒ) as []; auto.
  apply (R_Ord_Tri _ u) in H5 as [H5|[]]; auto; clear H6.
  - right. pose proof H5. apply mt_R0_RAbs in H5; auto. rewrite H5. apply H6.
  - pose proof H5. apply lt_R0_RAbs in H6; auto.
    apply R_Plus_PrOrder_Corollary in H5 as [u0[[H5[]]]]; auto.
    right. rewrite H6. apply R_Minus_Plus in H8; auto. rewrite H8. apply H7.
  - left. symmetry in H5. apply eq_R0_RAbs in H5; auto.
Qed.

(* 任何数小于等于自己的绝对值*)
Property Self_le_RAbs : ∀ u, u ∈ Ｒ -> u = |u| \/ u < |u|.
Proof.
  intros. pose proof H. apply R0_le_RAbs in H0 as []; auto. pose proof R0_in_R.
  assert (R0 ∈ Ｒ /\ u ∈ Ｒ) as []; auto.
  apply (R_Ord_Tri _ u) in H3 as [H3|[]]; auto; clear H4.
  - apply mt_R0_RAbs in H3; auto.
  - destruct H1. apply (eq_R0_RAbs u) in H1; auto.
    rewrite <-H1 in H3. elim (R_Ord_irReflex u u); auto.
    apply (R_Ord_Trans u) in H1; auto.
  - pose proof H3. symmetry in H3. apply eq_R0_RAbs in H3; auto.
    rewrite H4 in H3; auto.
Qed.

(* 绝对值对乘法保持 |ab| = |a|*|b| *)
Property RAbs_PrMult : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ -> |(u · v)| = |u| · |v|.
Proof.
  intros. pose proof R0_in_R; pose proof R1_in_R.
  assert (R0 ∈ Ｒ /\ u ∈ Ｒ) as []; auto.
  apply (R_Ord_Tri _ u) in H3; auto; clear H4.
  assert (R0 ∈ Ｒ /\ v ∈ Ｒ) as []; auto.
  apply (R_Ord_Tri _ v) in H4; auto; clear H5.
  destruct H3 as [H3|[]].
  - destruct H4 as [H4|[]].
    + pose proof H4. apply (R_Mult_PrOrder _ _ u) in H5; auto.
      rewrite R_Mult_Property1 in H5; auto.
      apply mt_R0_RAbs in H5; try apply R_Mult_in_R; auto.
      apply mt_R0_RAbs in H3; apply mt_R0_RAbs in H4; auto.
      rewrite H3,H4,H5; auto.
    + pose proof H4. apply (R_Mult_PrOrder _ _ u) in H5; auto.
      rewrite R_Mult_Property1 in H5; auto.
      apply lt_R0_RAbs in H5; try apply R_Mult_in_R; auto.
      pose proof H4. apply lt_R0_RAbs in H6; auto.
      apply mt_R0_RAbs in H3; auto. rewrite H3,H5,H6.
      rewrite R_Mult_Distribution_Minus,R_Mult_Property1; auto.
    + rewrite <-H4,R_Mult_Property1; auto. symmetry in H4.
      pose proof H4. apply eq_R0_RAbs in H4; auto.
      rewrite <-H5,H4,R_Mult_Property1; auto. apply RAbs_in_R; auto.
  - destruct H4 as [H4|[]].
    + pose proof H3. apply (R_Mult_PrOrder _ _ v) in H5; auto.
      rewrite R_Mult_Property1 in H5; auto.
      apply lt_R0_RAbs in H5; try apply R_Mult_in_R; auto.
      pose proof H3. apply lt_R0_RAbs in H6; auto. apply mt_R0_RAbs in H4; auto.
      rewrite R_Mult_Commutation,H4,H5,H6; auto.
      rewrite (R_Mult_Commutation _ v),R_Mult_Distribution_Minus,R_Mult_Property1;
      auto. rewrite <-H6. apply RAbs_in_R; auto.
    + assert (R0 < (u · v)).
      { pose proof H4. apply R_Plus_PrOrder_Corollary in H5 as [v0[[H5[]]]]; auto.
        apply (R_Mult_PrOrder _ _ v0) in H3; auto.
        rewrite R_Mult_Property1 in H3; auto. pose proof H7.
        apply R_Minus_Plus in H9; auto.
        rewrite <-H9,R_Mult_Commutation,R_Mult_Distribution_Minus,
        R_Mult_Property1 in H3; try apply R_Minus_in_R; auto.
        apply (R_Plus_PrOrder _ _ (u · v)) in H3; try apply R_Mult_in_R; auto.
        rewrite R_Plus_Property,<-R_Mix_Association1,
        R_Plus_Property in H3; try apply R_Mult_in_R; auto.
        assert ((u · v) - (u · v) = R0).
        { apply R_Minus_Plus; try apply R_Mult_in_R; auto.
          rewrite R_Plus_Property; try apply R_Mult_in_R; auto. }
        rewrite H10 in H3; auto.
        apply R_Minus_in_R; try apply R_Mult_in_R; auto. }
      apply lt_R0_RAbs in H3; apply lt_R0_RAbs in H4; auto.
      apply mt_R0_RAbs in H5; try apply R_Mult_in_R; auto.
      rewrite H3,H4,H5,R_Mult_Distribution_Minus,
      R_Mult_Property1,(R_Mult_Commutation (R0 - u)),
      R_Mult_Distribution_Minus,R_Mult_Property1,
      R_Mult_Commutation; try apply R_Minus_in_R; auto. symmetry.
      apply R_Minus_Plus; try apply R_Minus_in_R;
      try apply R_Mult_in_R; auto.
      rewrite R_Plus_Commutation,<-R_Mix_Association1,
      R_Plus_Property; try apply R_Mult_in_R; auto.
      apply R_Minus_Plus; try apply R_Mult_in_R; auto.
      rewrite R_Plus_Property; try apply R_Mult_in_R; auto.
      apply R_Minus_in_R; try apply R_Mult_in_R; auto.
    + rewrite <-H4,R_Mult_Property1; auto. symmetry in H4.
      pose proof H4. apply eq_R0_RAbs in H4; auto.
      rewrite <-H5,H4,R_Mult_Property1; auto. apply RAbs_in_R; auto.
  - clear H4. rewrite <-H3,R_Mult_Commutation,R_Mult_Property1; auto.
    symmetry in H3. pose proof H3. apply eq_R0_RAbs in H3; auto.
    rewrite <-H4,H3,R_Mult_Commutation,R_Mult_Property1; auto;
    apply RAbs_in_R; auto.
Qed.

(* 绝对值不等式 |a+b| <= |a|+|b| *)
Property RAbs_inEqu : ∀ u v, u ∈ Ｒ -> v ∈ Ｒ
  -> |(u + v)| = (|u| + |v|) \/ |(u + v)| < (|u| + |v|).
Proof.
  intros. pose proof R0_in_R. pose proof H. apply (R_Plus_in_R u v) in H2; auto.
  assert (u ∈ Ｒ /\ R0 ∈ Ｒ) as []; auto.
  apply (R_Ord_Tri u R0) in H3; auto; clear H4.
  assert (v ∈ Ｒ /\ R0 ∈ Ｒ) as []; auto.
  apply (R_Ord_Tri v R0) in H4; auto; clear H5.
  assert ((R_Plus u v) ∈ Ｒ /\ R0 ∈ Ｒ) as []; auto.
  apply (R_Ord_Tri _ R0) in H5; auto; clear H6.
  destruct H5 as [H5|[]].
  - assert (∀ a b, a ∈ Ｒ -> b ∈ Ｒ -> (a + b) < R0 -> a < R0 -> R0 < b
      -> |(a + b)| < (|a| + |b|)).
    { intros. pose proof H8. apply lt_R0_RAbs in H11; try apply R_Plus_in_R; auto.
      pose proof H9. apply lt_R0_RAbs in H12; auto. pose proof H10.
      apply mt_R0_RAbs in H13; auto. rewrite H11,H12,H13.
      apply (R_Plus_PrOrder _ _ (a + b));
      try apply R_Plus_in_R; try apply R_Minus_in_R; auto.
      apply R_Plus_in_R; auto. rewrite <-R_Mix_Association1,
      R_Plus_Property,<-R_Plus_Association,<-R_Mix_Association1,
      R_Plus_Property,(R_Plus_Commutation a b),
      (R_Mix_Association1 b a a); try apply R_Plus_in_R;
      try apply R_Minus_in_R; auto.
      assert (a - a = R0 /\ (b + a) - (b + a) = R0) as [].
      { split; apply R_Minus_Plus; try rewrite R_Plus_Property;
        try apply R_Plus_in_R; try apply R_Plus_in_R; auto. }
      rewrite H14,H15. rewrite R_Plus_Property; auto.
      pose proof H10. apply (R_Plus_PrOrder _ _ b) in H16; auto.
      rewrite R_Plus_Property in H16; auto.
      apply (R_Ord_Trans _ b _); auto. apply R_Plus_in_R; auto. }
    pose proof H5 as H5'. apply lt_R0_RAbs in H5; auto.
    destruct H3 as [H3|[]].
    + pose proof H3 as H3'. apply lt_R0_RAbs in H3; auto.
      destruct H4 as [H4|[]].
      * apply lt_R0_RAbs in H4; auto. rewrite H3,H4,H5. left.
        apply R_Minus_Plus; auto. apply R_Plus_in_R; try apply R_Minus_in_R; auto.
        rewrite <-R_Plus_Association,<-(R_Mix_Association1 _ _ u),
        R_Plus_Property,(R_Plus_Commutation u v),
        R_Mix_Association1,<-R_Mix_Association1,R_Plus_Property,
        R_Plus_Commutation,R_Mix_Association1; auto;
        try apply R_Plus_in_R; try apply R_Minus_in_R; auto.
        assert (u - u = R0 /\ v - v = R0) as [].
        { split; apply R_Minus_Plus; try rewrite R_Plus_Property; auto. }
        rewrite H7,H8,R_Plus_Property; auto.
      * right. apply H6; auto.
      * left. pose proof H4. apply eq_R0_RAbs in H7; auto.
        rewrite H7,H4,R_Plus_Property,R_Plus_Property; auto. apply RAbs_in_R; auto.
    + pose proof H3. apply mt_R0_RAbs in H7; auto. destruct H4 as [H4|[]].
      * right. rewrite R_Plus_Commutation,
        (R_Plus_Commutation (|u|)); try apply RAbs_in_R; auto.
        apply H6; auto. rewrite R_Plus_Commutation; auto.
      * apply (R_Plus_PrOrder _ _ u) in H4; auto.
        rewrite R_Plus_Property in H4; auto.
        apply (R_Ord_Trans R0),(R_Ord_Trans _ _ R0) in H4; auto.
        elim (R_Ord_irReflex R0 R0); auto.
      * apply (R_Plus_PrOrder _ _ v) in H3; auto.
        rewrite H4,R_Plus_Property,R_Plus_Commutation,
        R_Plus_Property in H3; auto.
        rewrite H4,R_Plus_Property in H5'; auto.
        apply (R_Ord_Trans _ _ u) in H5'; auto.
        elim (R_Ord_irReflex u u); auto.
    + left. pose proof H3. apply eq_R0_RAbs in H7; auto.
      rewrite H7,H3,R_Plus_Commutation,R_Plus_Property,
      R_Plus_Commutation,R_Plus_Property; auto; apply RAbs_in_R; auto.
  - pose proof H2. apply mt_R0_RAbs in H6; auto.
    rewrite H6. destruct H3 as [H3|[]].
    + pose proof H3. apply lt_R0_RAbs in H7; auto.
      pose proof H3. apply R_Plus_PrOrder_Corollary in H8 as [u0[[H8[]]_]]; auto.
      apply R_Minus_Plus in H10; auto. destruct H4 as [H4|[]].
      * apply (R_Plus_PrOrder _ _ u) in H4; auto.
        rewrite R_Plus_Property in H4; auto.
        apply (R_Ord_Trans _ _ R0),(R_Ord_Trans R0) in H4; auto.
        elim (R_Ord_irReflex R0 R0); auto.
      * right. apply mt_R0_RAbs in H4; auto.
        rewrite H4,H7,H10,R_Plus_Commutation,(R_Plus_Commutation _ v); auto.
        apply R_Plus_PrOrder; auto. apply (R_Ord_Trans _ R0); auto.
      * right. pose proof H4. apply eq_R0_RAbs in H11; auto.
        rewrite H11,H4,R_Plus_Property,R_Plus_Property; auto.
        rewrite H7,H10. apply (R_Ord_Trans _ R0); auto. apply RAbs_in_R; auto.
    + pose proof H3. apply mt_R0_RAbs in H7; auto. rewrite H7.
      destruct H4 as [H4|[]].
      * pose proof H4. apply lt_R0_RAbs in H8; auto. pose proof H4.
        apply R_Plus_PrOrder_Corollary in H4 as [v0[[H4[]]_]]; auto. right.
        apply R_Minus_Plus in H11; auto. rewrite H8,H11.
        apply R_Plus_PrOrder; auto. apply (R_Ord_Trans _ R0); auto.
      * apply mt_R0_RAbs in H4; auto. left. rewrite H4; auto.
      * pose proof H4. apply eq_R0_RAbs in H8; auto. left. rewrite H8,H4; auto.
    + left. pose proof H3. apply eq_R0_RAbs in H7; auto.
      rewrite <-H6,H7,H3,R_Plus_Commutation,R_Plus_Property,
      R_Plus_Commutation,R_Plus_Property; try apply RAbs_in_R; auto.
  - pose proof H5. apply eq_R0_RAbs in H6; auto. rewrite H6.
    pose proof H; pose proof H0.
    apply R0_le_RAbs in H7 as []; apply R0_le_RAbs in H8 as []; auto.
    destruct H9,H10.
    + left. rewrite H9,H10. rewrite R_Plus_Property; auto.
    + right. rewrite H9,R_Plus_Commutation,R_Plus_Property; auto.
    + right. rewrite H10,R_Plus_Property; auto.
    + right. apply (R_Plus_PrOrder _ _ (|u|)) in H10; auto.
      rewrite R_Plus_Property in H10; auto. apply (R_Ord_Trans R0) in H10; auto.
      apply R_Plus_in_R; auto.
Qed.

(* 互为负元的数, 其绝对值相等. *)
Property Neg_RAbs_Equ : ∀ u v, u∈ Ｒ -> v ∈ Ｒ -> u + v = R0
  -> |u| = |v|.
Proof.
  intros. pose proof R0_in_R.
  assert (R0 ∈ Ｒ /\ u ∈ Ｒ) as []; auto.
  apply (R_Ord_Tri _ u) in H3; auto; clear H4.
  assert (R0 ∈ Ｒ /\ v ∈ Ｒ) as []; auto.
  apply (R_Ord_Tri _ v) in H4; auto; clear H5.
  assert (∀ a b, a ∈ Ｒ -> b ∈ Ｒ -> a + b = R0
    -> R0 < a -> b < R0 -> |a| = |b|) as G.
  { intros. pose proof H8. apply mt_R0_RAbs in H8; auto.
    pose proof H9. apply lt_R0_RAbs in H9; auto.
    apply R_Plus_PrOrder_Corollary in H11 as [b0[[H11[]]]]; auto.
    assert (b0 = a).
    { apply H14; repeat split; auto. rewrite R_Plus_Commutation; auto. }
    clear H14. apply R_Minus_Plus in H13; auto. rewrite H8,<-H15,<-H13,H9; auto. }
  destruct H3 as [H3|[]].
  - pose proof H3. apply mt_R0_RAbs in H5; auto. rewrite H5.
    destruct H4 as [H4|[]].
    + apply (R_Plus_PrOrder _ _ u) in H4; auto.
      rewrite H1,R_Plus_Property in H4; auto.
      apply (R_Ord_Trans _ _ u) in H4; auto. elim (R_Ord_irReflex u u); auto.
    + rewrite <-H5. apply G; auto.
    + rewrite <-H4,R_Plus_Property in H1; auto.
      rewrite <-H1 in H3. elim (R_Ord_irReflex u u); auto.
  - pose proof H3. apply lt_R0_RAbs in H5; auto. rewrite H5.
    destruct H4 as [H4|[]].
    + rewrite <-H5. symmetry. apply G; auto. rewrite R_Plus_Commutation; auto.
    + apply (R_Plus_PrOrder _ _ u) in H4; auto. rewrite R_Plus_Property in H4; auto.
      apply (R_Ord_Trans _ _ R0) in H4; auto. rewrite H1 in H4.
      elim (R_Ord_irReflex R0 R0); auto. apply R_Plus_in_R; auto.
    + rewrite <-H4,R_Plus_Property in H1; auto. rewrite <-H1 in H3.
      elim (R_Ord_irReflex u u); auto.
  - rewrite <-H3,R_Plus_Commutation,R_Plus_Property in H1; auto.
    rewrite <-H3,H1; auto.
Qed.

