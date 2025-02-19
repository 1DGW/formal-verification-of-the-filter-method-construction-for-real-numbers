(*    This file presents the formalization of rational numbers in *Q.   *)
(*   It is developmented in the CoqIDE (version 8.13.2) for windows.    *)

(** N_Z_Q_in_Qs *)

Require Export fmcr.Zs_to_Qs.

(* 为了讨论*Q所具备的性质, 下面的论证将会与之前*N和*Z的讨论有所不同：

  接下来, 需要考虑将ω同构嵌入*Q, 以为建立*Q的Archimedes子集做准备.

  参考已有的结果, 利用φ将ω同构嵌入了*N, 利用φ1将*N同构嵌入了*Z, 又利用φ2将*Z同构
  嵌入了*Q, 于是很自然的, 利用φ φ1 φ2三者的复合即可将W同构嵌入Q'.           *)
Definition φ4 := φ2 ∘ (φ1 ∘ φ).

Property φ4_is_Function : Function1_1 φ4 /\ dom(φ4) = ω /\ ran(φ4) ⊂ Q'.
Proof.
  destruct φ_is_Function as [H[]]. pose proof N'_N_subset_N'.
  destruct φ1_is_Function as [H3[]]. destruct Z'_N'_propersubset_Z'.
  destruct φ2_is_Function as [H8[]]. destruct Q'_Z'_propersubset_Q'.
  destruct H,H3,H8. assert (Function1_1 φ4) as [].
  { split. repeat apply MKT64; auto. unfold φ4.
    repeat (rewrite MKT62; apply MKT64); auto. }
  split. split; auto. split.
  - apply AxiomI; split; intros.
    + apply Property_Value in H18; auto.
      apply AxiomII' in H18 as [H18[y[]]].
      apply AxiomII' in H19 as [H19[y1[]]].
      apply AxiomII' in H21; tauto.
    + rewrite <-H0 in H18. apply Property_Value in H18; auto.
      pose proof H18. apply Property_ran in H19. rewrite H1 in H19.
      apply H2 in H19. rewrite <-H4 in H19.
      apply Property_Value in H19; auto. pose proof H19.
      apply Property_ran in H20. rewrite H5 in H20. apply H6 in H20.
      rewrite <-H9 in H20. apply Property_Value in H20; auto.
      assert ([z,φ2[φ1[φ[z]]]] ∈ φ4).
      { apply AxiomII'; split. apply Property_dom in H18.
        apply Property_ran in H20. apply MKT49a; eauto.
        exists (φ1[φ[z]]). split; auto. apply AxiomII'; split; eauto.
        apply Property_dom in H18. apply Property_ran in H19.
        apply MKT49a; eauto. }
      apply Property_dom in H21; auto.
  - unfold Included; intros. apply AxiomII in H18 as [H18[]].
    apply AxiomII' in H19 as [H19[y[]]]. apply Property_ran in H21.
    rewrite H10 in H21; auto.
Qed.

Lemma φ4_Lemma : ∀ m, m ∈ ω -> φ2[φ1[φ[m]]] = φ4[m].
Proof.
  intros. destruct φ_is_Function as [H0[]].
  pose proof N'_N_subset_N'. destruct φ1_is_Function as [H4[]].
  destruct Z'_N'_propersubset_Z'. destruct φ2_is_Function as [H9[]].
  destruct Q'_Z'_propersubset_Q'. destruct H0,H4,H9. rewrite <-H1 in H.
  apply Property_Value in H; auto. pose proof H.
  apply Property_ran in H17. rewrite H2 in H17. apply H3 in H17.
  rewrite <-H5 in H17. apply Property_Value in H17; auto.
  pose proof H17. apply Property_ran in H18. rewrite H6 in H18.
  apply H7 in H18. rewrite <-H10 in H18. apply Property_Value in H18; auto.
  assert ([m,φ2[φ1[φ[m]]]] ∈ φ4).
  { apply AxiomII'; split. apply Property_dom in H.
    apply Property_ran in H18. apply MKT49a; eauto.
    exists (φ1[φ[m]]). split; auto. apply AxiomII'; split; eauto.
    apply Property_dom in H. apply Property_ran in H17. apply MKT49a; eauto. }
  apply Property_dom in H. rewrite H1 in H. destruct φ4_is_Function as [H20[]].
  rewrite <-H21 in H. destruct H20. apply Property_Value in H; auto.
  destruct H20. apply (H24 m); auto.
Qed.

(* φ4是序保持的. *)
Property φ4_PrOrder : ∀ m n, m ∈ ω -> n ∈ ω -> m ∈ n <-> φ4[m] < φ4[n].
Proof.
  intros. destruct φ4_is_Function as [H1[]]. pose proof H.
  apply (φ_PrOrder m n) in H4; auto. destruct φ_is_Function as [H5[]].
  pose proof H as Ha; pose proof H0 as Hb. rewrite <-H6 in H,H0.
  destruct H5. apply Property_Value,Property_ran in H; auto.
  apply Property_Value,Property_ran in H0; auto. pose proof N'_N_subset_N'.
  rewrite H7 in H,H0. apply H9 in H. apply H9 in H0. pose proof H.
  apply (φ1_PrOrder _ (φ[n])) in H10; auto. destruct φ1_is_Function as [H11[]].
  rewrite <-H12 in H,H0. destruct H11. apply Property_Value,Property_ran in H;
  auto. apply Property_Value, Property_ran in H0; auto.
  destruct Z'_N'_propersubset_Z'. rewrite H13 in H,H0.
  apply H15 in H; apply H15 in H0. pose proof H.
  apply (φ2_PrOrder _ (φ1[φ[n]])) in H17; auto.
  rewrite (φ4_Lemma m),(φ4_Lemma n) in H17; auto.
  split; intros; try apply H17,H10,H4; auto; apply H4,H10,H17; auto.
Qed.

(* φ4是加法保持的 *)
Property φ4_PrPlus : ∀ m n, m ∈ ω -> n ∈ ω -> φ4[(m + n)%ω] = φ4[m] + φ4[n].
Proof.
  intros. destruct φ4_is_Function as [H1[]]. pose proof H.
  apply (φ_PrPlus m n) in H4; auto. destruct φ_is_Function as [H5[]].
  pose proof H as Ha; pose proof H0 as Hb. rewrite <-H6 in H,H0. destruct H5.
  apply Property_Value,Property_ran in H; auto.
  apply Property_Value,Property_ran in H0; auto. pose proof N'_N_subset_N'.
  rewrite H7 in H,H0. apply H9 in H. apply H9 in H0.
  pose proof H. apply (φ1_PrPlus _ (φ[n])) in H10; auto.
  destruct φ1_is_Function as [H11[]]. rewrite <-H12 in H,H0. destruct H11.
  apply Property_Value,Property_ran in H; auto.
  apply Property_Value,Property_ran in H0; auto. destruct Z'_N'_propersubset_Z'.
  rewrite H13 in H,H0. apply H15 in H; apply H15 in H0. pose proof H.
  apply (φ2_PrPlus _ (φ1[φ[n]])) in H17; auto.
  rewrite (φ4_Lemma m),(φ4_Lemma n) in H17; auto.
  rewrite <-H17,<-H10,<-H4,(φ4_Lemma (m + n)%ω); auto.
  apply ω_Plus_in_ω; auto.
Qed.

(* φ4是乘法保持的 *)
Property φ4_PrMult : ∀ m n, m ∈ ω -> n ∈ ω -> φ4[(m · n)%ω] = φ4[m] · φ4[n].
Proof.
  intros. destruct φ4_is_Function as [H1[]]. pose proof H.
  apply (φ_PrMult m n) in H4; auto. destruct φ_is_Function as [H5[]].
  pose proof H as Ha; pose proof H0 as Hb. rewrite <-H6 in H,H0.
  destruct H5. apply Property_Value,Property_ran in H; auto.
  apply Property_Value,Property_ran in H0; auto. pose proof N'_N_subset_N'.
  rewrite H7 in H,H0. apply H9 in H. apply H9 in H0. pose proof H.
  apply (φ1_PrMult _ (φ[n])) in H10; auto. destruct φ1_is_Function as [H11[]].
  rewrite <-H12 in H,H0. destruct H11. apply Property_Value,Property_ran in H;
  auto. apply Property_Value,Property_ran in H0; auto.
  destruct Z'_N'_propersubset_Z'. rewrite H13 in H,H0.
  apply H15 in H; apply H15 in H0. pose proof H.
  apply (φ2_PrMult _ (φ1[φ[n]])) in H17; auto.
  rewrite (φ4_Lemma m),(φ4_Lemma n) in H17; auto.
  rewrite <-H17,<-H10,<-H4,(φ4_Lemma (m · n)%ω); auto.
  apply ω_Mult_in_ω; auto.
Qed.

(* 关于φ4的两个实例. *)
Property φ4_0 : φ4[0] = Q'0.
Proof.
  intros. pose proof in_ω_0. rewrite <-φ4_Lemma; auto.
  destruct φ_is_Function as [[][]]. destruct φ1_is_Function as [[][]].
  destruct φ2_is_Function as [[][]]. rewrite <-H2 in H.
  apply Property_Value in H; auto. pose proof H. apply Property_ran in H12.
  rewrite H3 in H12. apply N'_N_subset_N' in H12. rewrite <-H6 in H12.
  apply Property_Value in H12; auto. pose proof H12. apply Property_ran in H13.
  rewrite H7 in H13. apply Z'_N'_propersubset_Z' in H13; auto.
  rewrite <-H10 in H13. apply Property_Value in H13; auto.
  apply AxiomII' in H as [H[]]. rewrite H15 in H12.
  apply AxiomII' in H12 as [H12[]]. rewrite <-Z'0_Property in H17; auto.
  rewrite H15,H17 in H13. apply AxiomII' in H13 as [H13[]].
  rewrite H15,H17,Q'0_Property; auto.
Qed.

Property φ4_1 : φ4[1] = Q'1.
Proof.
  pose proof in_ω_1. rewrite <-φ4_Lemma; auto.
  destruct φ_is_Function as [[][]]. destruct φ1_is_Function as [[][]].
  destruct φ2_is_Function as [[][]]. rewrite <-H2 in H.
  apply Property_Value in H; auto. pose proof H. apply Property_ran in H12.
  rewrite H3 in H12. apply N'_N_subset_N' in H12. rewrite <-H6 in H12.
  apply Property_Value in H12; auto. pose proof H12. apply Property_ran in H13.
  rewrite H7 in H13. apply Z'_N'_propersubset_Z' in H13. rewrite <-H10 in H13.
  apply Property_Value in H13; auto. apply AxiomII' in H as [H[]].
  rewrite H15 in H12. apply AxiomII' in H12 as [H12[]].
  rewrite <-Z'1_Property in H17; auto. rewrite H15,H17 in H13.
  apply AxiomII' in H13 as [H13[]]. rewrite H15,H17,Q'1_Property; auto.
Qed.

Definition Q'_N := ran(φ4).
(* 至此, ω被同构嵌入了*Q中. *)

Property Q'_N_subset_Q' : Q'_N ⊂ Q'.
Proof.
  unfold Included; intros. unfold Q'_N in H.
  destruct φ4_is_Function as [[][]]; auto.
Qed.

(* Q'0是*Q_N中的元素 *)
Property Q'0_in_Q'_N : Q'0 ∈ Q'_N.
Proof.
  destruct φ4_is_Function as [[][]]. pose proof φ4_0. pose proof in_ω_0.
  rewrite <-H1 in H4. apply Property_Value,Property_ran in H4; auto.
  rewrite <-H3; auto.
Qed.

(* Q'1是*Q_N中的元素 *)
Property Q'1_in_Q'_N : Q'1 ∈ Q'_N.
Proof.
  destruct φ4_is_Function as [[][]]. pose proof φ4_1. pose proof in_ω_1.
  rewrite <-H1 in H4. apply Property_Value,Property_ran in H4; auto.
  rewrite <-H3; auto.
Qed.

(* 验证: *Q_N对加法封闭. *)
Property Q'_N_Plus_in_Q'_N : ∀ u v, u ∈ Q'_N -> v ∈ Q'_N -> (u + v) ∈ Q'_N.
Proof.
  intros. destruct φ4_is_Function as [[][]].
  assert (u ∈ ran(φ4) /\ v ∈ ran(φ4)) as []; auto.
  rewrite reqdi in H5,H6. apply Property_Value,Property_ran in H5;
  apply Property_Value,Property_ran in H6; auto. rewrite <-deqri,H3 in H5,H6.
  pose proof H5. apply (φ4_PrPlus ((φ4⁻¹)[u]) ((φ4⁻¹)[v])) in H7; auto.
  rewrite f11vi,f11vi in H7; auto. apply (ω_Plus_in_ω ((φ4⁻¹)[u])) in H6; auto.
  rewrite <-H3 in H6. apply Property_Value,Property_ran in H6; auto.
  rewrite <-H7; auto.
Qed.

(* 验证: *Q_N对乘法封闭. *)
Property Q'_N_Mult_in_Q'_N : ∀ u v, u ∈ Q'_N -> v ∈ Q'_N -> (u · v) ∈ Q'_N.
Proof.
  intros. destruct φ4_is_Function as [[][]].
  assert (u ∈ ran(φ4) /\ v ∈ ran(φ4)) as []; auto. rewrite reqdi in H5,H6.
  apply Property_Value,Property_ran in H5;
  apply Property_Value,Property_ran in H6; auto. rewrite <-deqri,H3 in H5,H6.
  pose proof H5. apply (φ4_PrMult ((φ4⁻¹)[u]) ((φ4⁻¹)[v])) in H7; auto.
  rewrite f11vi,f11vi in H7; auto. apply (ω_Mult_in_ω ((φ4⁻¹)[u])) in H6; auto.
  rewrite <-H3 in H6. apply Property_Value,Property_ran in H6; auto.
  rewrite <-H7; auto.
Qed.

(* *Q中定义的序对于*Q_N是良序的.
   此性质对于构造*Q中的分数列有重要作用(可以根据良序性选取元素). *)
Property Q'_Ord_WellOrder_Q'_N : WellOrdered Q'_Ord Q'_N.
Proof.
  split; intros.
  - unfold Connect; intros. apply Q'_Ord_Tri; auto; apply Q'_N_subset_Q'; auto.
  - assert (WellOrdered E ω) as [_ H1].
    { apply MKT107. pose proof MKT138. apply AxiomII in H1; tauto. }
    destruct φ4_is_Function as [[][]]. assert (ω = φ4⁻¹「Q'_N」).
    { apply AxiomI; split; intros.
      - apply AxiomII; repeat split; eauto. rewrite H4; auto.
        rewrite <-H4 in H6. apply Property_Value,Property_ran in H6; auto.
      - apply AxiomII in H6 as [H6[]]. rewrite <-H4; auto. }
    assert (φ4⁻¹「y」 ⊂ ω /\ φ4⁻¹「y」 <> 0).
    { split.
      - unfold Included; intros. apply AxiomII in H7 as [_[]].
        rewrite H4 in H7; auto.
      - apply PreimageSet_Fact; auto. intro. elim H0.
        apply AxiomI; split; intros. pose proof H8. apply H in H9.
        assert (z ∈ (y ∩ Q'_N)). { apply MKT4'; auto. }
        rewrite <-H7; auto. elim (@ MKT16 z); auto. }
    destruct H7. apply H1 in H7 as [x[]]; auto; clear H8.
    exists ((φ4)[x]). split.
    + apply AxiomII in H7; tauto.
    + intros. assert ((φ4⁻¹)[y0] ∈ φ4⁻¹「y」).
      { pose proof H8 as H8'. apply H in H8. unfold Q'_N in H8.
        rewrite reqdi in H8. apply Property_Value,Property_ran in H8; auto.
        rewrite <-deqri in H8. apply AxiomII; repeat split; eauto.
        rewrite f11vi; auto. }
      pose proof H10. apply H9 in H10. intro. elim H10. apply AxiomII'; split.
      apply MKT49a; eauto. apply φ4_PrOrder; auto. apply AxiomII in H11 as [_[]].
      rewrite <-H4; auto. apply AxiomII in H7 as [_[]].
      rewrite <-H4; auto. rewrite f11vi; auto.
Qed.

(* *Q_N 中的Q'0为首元 *)
Property Q'_N_Q'0_is_FirstMember : ∀ u, u ∈ (Q'_N ~ [Q'0]) -> Q'0 < u.
Proof.
  intros. apply MKT4' in H as []. destruct φ4_is_Function as [[][]].
  assert (u ∈ ran(φ4)); auto. rewrite reqdi in H5.
  apply Property_Value,Property_ran in H5; auto.
  rewrite <-deqri,H3 in H5. pose proof in_ω_0.
  assert (Ordinal 0 /\ Ordinal ((φ4⁻¹)[u])) as [].
  { apply AxiomII in H5 as [H5[]]; apply AxiomII in H6 as [H6[]]; auto. }
  apply (@ MKT110 0 ((φ4⁻¹)[u])) in H7 as [H7|[]]; auto; clear H8.
  - apply φ4_PrOrder in H7; auto. rewrite f11vi in H7; auto.
    rewrite φ4_0 in H7; auto.
  - elim (@ MKT16 (φ4⁻¹)[u]); auto.
  - pose proof φ4_0. rewrite H7,f11vi in H8; auto. apply AxiomII in H0 as [].
    elim H9. apply MKT41; auto. rewrite <-H8; auto.
Qed.

Lemma Q'_N_propersubset_Q'_N'_Lemma : ∀ f1 f2 x, Function f1
  -> Function f2 -> (f1 ∘ f2)[x] = f1[f2[x]].
Proof.
  intros. assert (Function (f1 ∘ f2)). { apply MKT64; auto. }
  assert (dom(f1 ∘ f2) ⊂ dom(f2)).
  { unfold Included; intros. apply AxiomII in H2 as [H2[]].
    apply AxiomII' in H3 as [H3[y[]]].
    apply Property_dom in H4; auto. }
  assert (dom(f1 ∘ f2) = f2⁻¹「ran(f2) ∩ dom(f1)」).
  { apply AxiomI; split; intros.
    - apply AxiomII in H3 as [H3[]].
      apply AxiomII' in H4 as [H4[y[]]].
      apply AxiomII; split; auto. split.
      apply Property_dom in H5; auto. pose proof H5.
      apply Property_dom,Property_Value in H7; auto.
      apply MKT4'; split. apply Property_ran in H7; auto.
      rewrite MKT70 in H5; auto. apply AxiomII' in H5 as [].
      rewrite <-H8. apply Property_dom in H6; auto.
    - apply AxiomII in H3 as [H3[]]. apply MKT4' in H5 as [].
      apply AxiomII; split; auto. exists (f1[f2[z]]).
      apply Property_Value in H6; auto. pose proof H6.
      apply Property_ran in H7. apply AxiomII'; split.
      apply MKT49a; eauto. exists f2[z]. split; auto.
      apply Property_Value; auto. }
  destruct (classic (x ∈ dom(f1 ∘ f2))).
  - pose proof H4. apply Property_Value in H4; auto.
    rewrite H3 in H5. apply AxiomII in H5 as [H5[]].
    apply MKT4' in H7 as []. apply Property_Value in H6;
    apply Property_Value in H8; auto. destruct H1.
    apply (H9 x); auto. pose proof H8. apply Property_ran in H10.
    apply AxiomII'; split; eauto.
  - destruct (classic (x ∈ dom(f2))).
    + pose proof H5. apply Property_Value,Property_ran in H6; auto.
      assert (~ f2[x] ∈ dom(f1)).
      { intro. elim H4. rewrite H3.
        apply AxiomII; repeat split; eauto. apply MKT4'; auto. }
      apply MKT69a in H4; apply MKT69a in H7. rewrite H4,H7; auto.
    + apply MKT69a in H4; apply MKT69a in H5.
      assert (~ f2[x] ∈ dom(f1)).
      { intro. rewrite H5 in H6. elim MKT39. eauto. }
      apply MKT69a in H6. rewrite H4,H6; auto.
Qed.

(* *Q_*N 真包含 *Q_N. *)
Property Q'_N_propersubset_Q'_N' : Q'_N ⊂ Q'_N' /\ Q'_N <> Q'_N'.
Proof.
  destruct NPAUF. destruct φ_is_Function as [[][]].
  destruct φ3_is_Function as [[][]]. destruct φ4_is_Function as [[][]].
  pose proof φ3_ran. split; unfold Included; intros.
  - pose proof H14. unfold Q'_N in H15. rewrite reqdi in H15.
    apply Property_Value,Property_ran in H15; auto.
    rewrite <-deqri,H11 in H15. pose proof H15. rewrite <-H3 in H16.
    apply Property_Value,Property_ran in H16; auto.
    rewrite H4 in H16. apply N'_N_subset_N' in H16; auto.
    rewrite <-H7 in H16. pose proof H16.
    apply Property_Value,Property_ran in H17; auto.
    rewrite H13,<-φ3_Lemma,φ4_Lemma,f11vi in H17; auto.
    rewrite <-H7; auto.
  - destruct N'_N_propersubset_N'. assert ((N' ~ N'_N) <> 0).
    { intro. elim H15. apply AxiomI; split; intros; auto.
      apply NNPP; intro. assert (z ∈ (N' ~ N'_N)).
      { apply MKT4'; split; [ |apply AxiomII; split]; eauto. }
      rewrite H16 in H19. elim (@ MKT16 z); auto. }
    apply NEexE in H16 as []. apply MKT4' in H16 as [].
    rewrite <-H7 in H16. pose proof H16.
    apply Property_Value,Property_ran in H18; auto.
    rewrite H13 in H18. pose proof H18. intro.
    rewrite <-H20 in H19. unfold Q'_N in H19. rewrite reqdi in H19.
    apply Property_Value,Property_ran in H19; auto.
    rewrite <-deqri,H11 in H19. pose proof H19. rewrite <-H3 in H21.
    apply Property_Value,Property_ran in H21; auto.
    unfold φ4 in H21. rewrite MKT62,MKT62,MKT58,<-MKT62 in H21.
    rewrite Q'_N_propersubset_Q'_N'_Lemma in H21; auto.
    replace ((φ2 ∘ φ1)⁻¹) with (φ3⁻¹) in H21; auto.
    rewrite (f11iv φ3) in H21; auto. assert (~ x ∈ ran(φ)).
    { intro. rewrite H4 in H22. apply AxiomII in H17 as []; auto. }
    rewrite reqdi in H22. apply MKT69a in H22.
    assert (~ (φ⁻¹)[x] ∈ dom(φ)).
    { intro. rewrite H22 in H23. elim MKT39; eauto. }
    apply MKT69a in H23. rewrite H23 in H21. elim MKT39. eauto.
Qed.

(* *Q_Z 是 *Q中 分母(第二坐标)为1分子(第一坐标)为*Z_Z中元的等价类组成的集. *)
Definition Q'_Z := \{ λ u, ∃ a, a ∈ Z'_Z /\ u = \[[a,Z'1]\] \}.

Property Q'_Z_subset_Q' : Q'_Z ⊂ Q'.
Proof.
  unfold Included; intros. apply AxiomII in H as [H[x[]]].
  apply AxiomII. split; auto. exists [x,Z'1]. split; auto.
  apply AxiomII'. pose proof Z'1_in_Z'. apply Z'_Z_subset_Z' in H0.
  repeat split; auto. apply MKT49a; eauto. apply MKT4'; split; auto.
  apply AxiomII; split; eauto. intro. apply MKT41 in H3.
  elim Z'0_isnot_Z'1; auto. pose proof Z'0_in_Z'; eauto.
Qed.

Property Q'_Z_Instantiate : Q'_Z = φ2「Z'_Z」.
Proof.
  destruct φ2_is_Function as [[][]]. apply AxiomI; split; intros.
  - apply AxiomII in H3 as [H3[x[]]]. apply AxiomII; split; auto.
    exists x. split; auto. apply Z'_Z_subset_Z' in H4; auto.
    rewrite <-H1 in H4. apply Property_Value,AxiomII' in H4 as [_[]]; auto.
    rewrite H6,H5; auto.
  - apply AxiomII in H3 as [H3[x[]]]. apply AxiomII; split; auto.
    exists x. split; auto. apply Z'_Z_subset_Z' in H5; auto.
    rewrite <-H1 in H5. apply Property_Value,AxiomII' in H5 as [_[]]; auto.
    rewrite <-H6,H4; auto.
Qed.

Property Q'0_in_Q'_Z : Q'0 ∈ Q'_Z.
Proof.
  rewrite Q'_Z_Instantiate. apply AxiomII; split; eauto with Q'. exists Z'0.
  split. rewrite φ2_Z'0; auto. apply Z'0_in_Z'_Z; auto.
Qed.

Property Q'1_in_Q'_Z : Q'1 ∈ Q'_Z.
Proof.
  rewrite Q'_Z_Instantiate. apply AxiomII; split; eauto with Q'. exists Z'1.
  split. rewrite φ2_Z'1; auto. apply Z'1_in_Z'_Z; auto.
Qed.

(* *Q_Z对加法封闭 *)
Property Q'_Z_Plus_in_Q'_Z : ∀ u v, u ∈ Q'_Z -> v ∈ Q'_Z -> (u + v) ∈ Q'_Z.
Proof.
  intros. pose proof H; pose proof H0.
  apply Q'_Z_subset_Q' in H1; apply Q'_Z_subset_Q' in H2; auto.
  pose proof H1. apply (Q'_Plus_in_Q' u v) in H3; auto.
  apply AxiomII; split; eauto. apply AxiomII in H as [H[x[]]], H0 as [H0[y[]]].
  exists (x + y)%z'. split.
  - apply Z'_Z_Plus_in_Z'_Z; auto.
  - rewrite H5,H7,Q'_Plus_Instantiate,Z'_Mult_Property2,
    Z'_Mult_Commutation,Z'_Mult_Property2,Z'_Mult_Property2;
    auto with Z'; apply Z'_Z_subset_Z'; auto.
Qed.

(* *Q_Z对乘法封闭 *)
Property Q'_Z_Mult_in_Q'_Z : ∀ u v, u ∈ Q'_Z -> v ∈ Q'_Z -> (u · v) ∈ Q'_Z.
Proof.
  intros. pose proof H; pose proof H0.
  apply Q'_Z_subset_Q' in H1; apply Q'_Z_subset_Q' in H2; auto.
  pose proof H1. apply (Q'_Mult_in_Q' u v) in H3; auto.
  apply AxiomII; split; eauto. apply AxiomII in H as [H[x[]]].
  apply AxiomII in H0 as [H0[y[]]]. exists (x · y)%z'. split.
  - apply Z'_Z_Mult_in_Z'_Z; auto.
  - rewrite H5,H7,Q'_Mult_Instantiate,Z'_Mult_Property2;
    auto with Z'; apply Z'_Z_subset_Z'; auto.
Qed.

(* *Q_Z对减法封闭需要的引理. *)
(* *N_N中, 若m < n, 则使得m+a=n的a是唯一且也在*N_N中的. (即n-m在*N_N中) *)
Lemma Q'_Z_Minus_in_Q'_Z_Lemma1 : ∀ m n, m ∈ N'_N -> n ∈ N'_N -> (m < n)%n'
  -> (∃! k, k ∈ N'_N /\ (F 0) < k /\ m + k = n)%n'.
Proof.
  intros. apply AxiomII in H as [H[a[]]]. apply AxiomII in H0 as [H0[b[]]].
  destruct φ_is_Function as [[][]]. rewrite <-H8 in H2,H4.
  apply Property_Value in H2; apply Property_Value in H4; auto.
  apply AxiomII' in H2 as [_[]]. apply AxiomII' in H4 as [_[]].
  pose proof H1. rewrite H3,H5,<-H10,<-H11 in H1. apply φ_PrOrder in H1; auto.
  apply Plus_PrOrder_Corollary in H1 as [c[[H1[]]]]; auto.
  exists (φ[c]). pose proof in_ω_0. rewrite <-H8 in H1,H16.
  apply Property_Value in H1; apply Property_Value in H16; auto.
  apply AxiomII' in H1 as [_[]]. apply AxiomII' in H16 as [_[]].
  apply φ_PrOrder in H13; auto. rewrite H18 in H13. rewrite <-H14 in H11.
  rewrite φ_PrPlus in H11; auto. rewrite H10,<-H3,H14,<-H5 in H11.
  assert (φ[c] ∈ N'_N). { rewrite H17. apply Fn_in_N'_N; auto. }
  repeat split; auto. intros x [H20[]]. rewrite <-H11 in H22.
  apply N'_Plus_Cancellation in H22; try apply N'_N_subset_N'; auto.
  rewrite H3. apply Fn_in_N'_N; auto.
Qed.

(* *Z_Z中, 对任意u v, 则使得u+a=v的a是唯一且也在*Z_Z中的. (即v-u在*Z_Z中)*)
Lemma Q'_Z_Minus_in_Q'_Z_Lemma2 : ∀ u v, u ∈ Z'_Z -> v ∈ Z'_Z
  -> ∃! w, w ∈ Z'_Z /\ (u + w = v)%z'.
Proof.
  intros. pose proof H; pose proof H0. pose proof H; pose proof H0.
  apply Z'_Z_subset_Z' in H3; apply Z'_Z_subset_Z' in H4; auto.
  apply AxiomII in H as [H[x[y[H5[]]]]]. apply AxiomII in H0 as [H0[x1[y1[H8[]]]]].
  pose proof H5; pose proof H6; pose proof H8; pose proof H9.
  apply N'_N_subset_N' in H11,H12,H13,H14; auto.
  assert (u ∈ Z' /\ v ∈ Z') as []; auto.
  apply (Z'_Ord_Tri u v) in H15 as [H15|[]]; auto; clear H16;
  rewrite H7,H10 in H15; try apply Z'_Ord_Instantiate in H15; auto.
  - apply Q'_Z_Minus_in_Q'_Z_Lemma1 in H15 as [a[[H15[]]]];
    try apply N'_N_Plus_in_N'_N; auto. set (A := (\[[a,(F 0)]\])%z').
    exists A. assert (Ensemble A).
    { apply (MKT33 (N' × N')). apply MKT74; apply N'_is_Set; auto.
      unfold Included; intros. apply AxiomII in H19; tauto. }
    assert (A ∈ Z'_Z).
    { apply AxiomII; split; auto. exists a,(F 0).
      repeat split; auto. apply Fn_in_N'_N; auto. }
    assert (u + A = v)%z'.
    { pose proof H15. apply N'_N_subset_N' in H21; auto.
      pose proof in_ω_0. apply Fn_in_N'_N in H22.
      pose proof H22. apply N'_N_subset_N' in H22; auto. unfold A.
      rewrite H7,H10,Z'_Plus_Instantiate,N'_Plus_Property; auto.
      apply R_N'_Property; auto. apply N'_Plus_in_N'; auto.
      rewrite N'_Plus_Association,(N'_Plus_Commutation a),
      <-N'_Plus_Association,H17; auto. }
    repeat split; auto. intros k []. rewrite <-H21 in H23.
    apply Z'_Plus_Cancellation in H23; auto; apply Z'_Z_subset_Z'; auto.
  - apply Q'_Z_Minus_in_Q'_Z_Lemma1 in H15 as [a[[H15[]]]];
    try apply N'_N_Plus_in_N'_N; auto. set (A := (\[[(F 0),a]\])%z'). exists A.
    assert (Ensemble A).
    { apply (MKT33 (N' × N')). apply MKT74; apply N'_is_Set; auto.
      unfold Included; intros. apply AxiomII in H19; tauto. }
    assert (A ∈ Z'_Z).
    { apply AxiomII; split; auto. exists (F 0),a.
      repeat split; auto. apply Fn_in_N'_N; auto. }
    assert (u + A = v)%z'.
    { pose proof H15. apply N'_N_subset_N' in H21; auto.
      pose proof in_ω_0. apply Fn_in_N'_N in H22.
      pose proof H22. apply N'_N_subset_N' in H22; auto. unfold A.
      rewrite H7,H10,Z'_Plus_Instantiate,N'_Plus_Property; auto.
      apply R_N'_Property; auto. apply N'_Plus_in_N'; auto.
      rewrite N'_Plus_Commutation,(N'_Plus_Commutation _ x1),
      <-N'_Plus_Association,H17; auto. apply N'_Plus_in_N'; auto. }
    repeat split; auto. intros k []. rewrite <-H21 in H23.
    apply Z'_Plus_Cancellation in H23; auto; apply Z'_Z_subset_Z'; auto.
  - exists Z'0. assert (Z'0 ∈ Z'_Z).
    { pose proof Z'0_in_Z'. apply AxiomII; split; eauto.
      assert ((F 0) ∈ N'_N). { apply Fn_in_N'_N,in_ω_0. }
      exists (F 0),(F 0). repeat split; auto. rewrite Z'0_Property; auto. }
    assert (u + Z'0 = v)%z'.
    { rewrite Z'_Plus_Property; auto. rewrite H7,H10; auto. }
    repeat split; auto. intros k []. rewrite <-H17 in H19.
    apply Z'_Plus_Cancellation in H19; auto; apply Z'_Z_subset_Z'; auto.
Qed.

(* *Q_Z对减法封闭 *)
Property Q'_Z_Minus_in_Q'_Z : ∀ u v, u ∈ Q'_Z -> v ∈ Q'_Z -> (u - v) ∈ Q'_Z.
Proof.
  intros. pose proof H; pose proof H0. apply Q'_Z_subset_Q' in H1,H2; auto.
  pose proof H; pose proof H0. apply AxiomII in H3 as [_[x[]]].
  apply AxiomII in H4 as [_[y[]]]. pose proof H4.
  apply (Q'_Z_Minus_in_Q'_Z_Lemma2 y x) in H7 as [a[[]_]]; auto.
  set (b := \[[a, Z'1]\]). assert (b ∈ Q' ).
  { apply Q'_Instantiate2; auto with Z'. apply Z'_Z_subset_Z'; auto. }
  assert (u - v = b).
  { apply Q'_Minus_Plus; auto. unfold b.
    rewrite H5,H6,Q'_Plus_Instantiate,Z'_Mult_Property2,
    Z'_Mult_Property2,Z'_Mult_Commutation,Z'_Mult_Property2,H8;
     auto with Z'; try apply Z'_Z_subset_Z'; auto. }
  rewrite H10. apply AxiomII; split; eauto.
Qed.

(* *Q_N与*Q_Z的关系:
   *Q_N是*Q_Z中大于等于0的部分. 即, 自然数是非负整数 *)
Property Q'_N_equ_Q'_Z_me_Q'0 : Q'_N = \{ λ u, u ∈ Q'_Z /\ (Q'0 = u \/ Q'0 < u) \}.
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII; repeat split; eauto.
    + apply AxiomII in H as [H[]]. apply AxiomII; split; auto.
      destruct φ4_is_Function as [[][]]. pose proof H0. apply Property_dom in H5.
      rewrite H3 in H5. pose proof H5. rewrite <-H3 in H6.
      apply Property_Value in H6; auto. pose proof H5.
      apply (φ4_Lemma x) in H7; auto. destruct φ_is_Function as [[][]].
      pose proof H5. rewrite <-H10 in H12. apply Property_Value in H12; auto.
      pose proof H12. apply Property_ran in H12.
      apply AxiomII' in H13 as [_[_ H13]]. destruct φ1_is_Function as [[][]].
      rewrite H11 in H12. apply N'_N_subset_N' in H12; auto. rewrite <-H16 in H12.
      apply Property_Value in H12; auto. pose proof H12. apply Property_ran in H12.
      rewrite H17 in H12. apply AxiomII' in H18 as [_[_ H18]].
      destruct φ2_is_Function as [[][]]. apply Z'_N'_propersubset_Z' in H12; auto.
      rewrite <-H21 in H12. pose proof H12 as H12'.
      apply Property_Value in H12; auto. apply AxiomII' in H12 as [_[_ H12]].
      assert (z = φ4[x]). { destruct H1. apply (H23 x); auto. }
      exists (φ1[φ[x]]). rewrite H23,<-H7,H12,H18,H13; split; auto.
      apply AxiomII; split. rewrite <-H13,<-H18. eauto. exists (F x),(F 0).
      repeat split; try apply Fn_in_N'_N; auto.
    + destruct (classic (z = Q'0)); auto. assert (z ∈ (Q'_N ~ [Q'0])).
      { apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
        pose proof Q'0_in_Q'. apply MKT41 in H1; eauto. }
      apply Q'_N_Q'0_is_FirstMember in H1; auto.
  - apply AxiomII in H as [H[]]. apply AxiomII in H0 as [_[x[]]].
    pose proof H0. apply Z'_Z_subset_Z' in H0.
    apply AxiomII in H3 as [H3[M[N[H4[]]]]]. apply AxiomII in H4 as [H4[m[]]].
    apply AxiomII in H5 as [H5[n[]]]. destruct φ_is_Function as [[][]].
    destruct φ1_is_Function as [[][]]. destruct φ2_is_Function as [[][]].
    destruct φ4_is_Function as [[][]]. destruct H1.
    + rewrite H2,Q'0_Property in H1; auto. apply R_Z'_Property in H1;
      auto with Z'. rewrite Z'_Mult_Property2,Z'_Mult_Commutation,
      Z'_Mult_Property2 in H1; auto with Z'. apply AxiomII; split; auto.
      rewrite <-H1 in H2. exists 0. pose proof in_ω_0. rewrite <-H13 in H27.
      apply Property_Value in H27; auto. pose proof H27.
      apply Property_ran in H28. rewrite H14 in H28.
      apply N'_N_subset_N' in H28; auto. rewrite <-H17 in H28.
      apply Property_Value in H28; auto. pose proof H28.
      apply Property_ran in H29. rewrite H18 in H29.
      apply Z'_N'_propersubset_Z' in H29; auto. rewrite <-H21 in H29.
      apply Property_Value in H29; auto. apply AxiomII' in H29 as [_[_ H29]].
      apply AxiomII' in H27 as [_[_ H27]]. apply AxiomII' in H28 as [_[_ H28]].
      rewrite φ4_Lemma,H28,H27,<-Z'0_Property,<-H2 in H29; auto;
      try apply in_ω_0. rewrite <-H29. apply Property_Value; auto.
      rewrite H25. apply in_ω_0.
    + rewrite H2,Q'0_Property in H1; auto.
      apply Q'_Ord_Instantiate in H1; auto with Z'.
      rewrite Z'_Mult_Property2,Z'_Mult_Commutation,
      Z'_Mult_Property2 in H1; auto with Z'. rewrite H6,Z'0_Property in H1; auto.
      assert (M ∈ N' /\ N ∈ N') as [].
      { rewrite H8,H10. split; apply N'_N_subset_N';try apply Fn_in_N'_N; auto. }
      apply Z'_Ord_Instantiate in H1; auto; try apply N'_N_subset_N';
      try apply Fn_in_N'_N; try apply in_ω_0; auto.
      rewrite N'_Plus_Commutation,N'_Plus_Property,
      N'_Plus_Commutation,N'_Plus_Property in H1; auto;
      try apply N'_N_subset_N'; try apply Fn_in_N'_N; try apply in_ω_0; auto.
      apply N'_Plus_PrOrder_Corollary in H1 as [A[[H1[]]_]]; auto.
      assert (M ∈ N'_N /\ N ∈ N'_N /\ A ∈ N'_N) as [H31[]].
      { rewrite H8,H10. repeat split; try apply Fn_in_N'_N; auto.
        assert (∀ w, F0 <> F w). { destruct NPAUF; auto. }
        apply NNPP; intro. assert (A ∈ (N' ~ N'_N)).
        { apply MKT4'; split; auto. apply AxiomII; split; eauto. }
        apply (N'_Infty A (F m)) in H33; auto. rewrite <-H8 in H33.
        rewrite <-H30,N'_Plus_Commutation in H33; auto.
        replace ((A + N) < A)%n' with ((A + N) < (A + (F 0)))%n' in H33.
        apply N'_Plus_PrOrder in H33; auto; try apply N'_N_subset_N';
        try apply Fn_in_N'_N; try apply in_ω_0; auto. rewrite H10 in H33.
        assert (Ensemble 0 /\ Ensemble n) as [].
        { pose proof in_ω_0. split; eauto. }
        assert (ω <> 0) as HH.
        { intro. pose proof in_ω_0. rewrite H36 in H37. elim (@ MKT16 0); auto. }
        apply (Const_is_Function ω) in H34 as [H34[]]; auto.
        apply (Const_is_Function ω) in H35 as [H35[]]; auto.
        pose proof H9. pose proof in_ω_0.
        apply (F_Const_Fa F0 ω) in H40,H41; auto. rewrite <-H40,<-H41 in H33.
        assert (ran(Const 0) ⊂ ω /\ ran(Const n) ⊂ ω) as [].
        { rewrite H37,H39. pose proof in_ω_0. split; unfold Included; intros;
          apply MKT41 in H43; eauto; rewrite H43; auto. }
        apply N'_Ord_Instantiate in H33; auto.
        assert (\{ λ w, (Const n)[w] ∈ (Const 0)[w] \} = 0).
        { apply AxiomI; split; intros; elim (@ MKT16 z0); auto.
          apply AxiomII in H44 as [].
          assert (z0 ∈ ω).
          { apply NNPP; intro. rewrite <-H38 in H46.
            apply MKT69a in H46. rewrite H46 in H45. elim MKT39; eauto. }
          pose proof H46. rewrite <-H36 in H46. rewrite <-H38 in H47.
          apply Property_Value,Property_ran in H46;
          apply Property_Value,Property_ran in H47; auto.
          rewrite H37 in H46. rewrite H39 in H47. pose proof in_ω_0.
          apply MKT41 in H46; apply MKT41 in H47; eauto.
          rewrite H46,H47 in H45. elim (@ MKT16 n); auto. }
        rewrite H44 in H33. destruct NPAUF as [[_[H45 _]]_].
        apply AxiomII in H45 as [H45[[H46[]]]]; auto.
        rewrite N'_Plus_Property; auto. apply Fn_in_N'_N; auto. }
      assert ((F 0) ∈ N'). { apply Fn_in_N',in_ω_0. }
      assert (x = \[[A,(F 0)]\])%z'.
      { rewrite H6. apply R_N'_Property; auto.
        rewrite N'_Plus_Property; auto. } clear H6.
      pose proof H33. apply AxiomII in H6 as [_[a[]]].
      apply AxiomII; split; auto. exists a. pose proof H6.
      rewrite <-H13 in H37. apply Property_Value in H37; auto.
      pose proof H37. apply Property_ran in H38. rewrite H14 in H38.
      apply N'_N_subset_N' in H38; auto. rewrite <-H17 in H38.
      apply Property_Value in H38; auto. pose proof H38.
      apply Property_ran in H39. rewrite H18 in H39.
      apply Z'_N'_propersubset_Z' in H39; auto. rewrite <-H21 in H39.
      apply Property_Value in H39; auto. apply AxiomII' in H39 as [_[_ H39]].
      apply AxiomII' in H38 as [_[_ H38]]. apply AxiomII' in H37 as [_[_ H37]].
      rewrite φ4_Lemma,H38,H37,<-H36,<-H35,<-H2 in H39; auto.
      rewrite <-H39. apply Property_Value; auto. rewrite H25; auto.
Qed.

(* *Q_N与*Q_Z的关系:
   *Q_N的非零负元组成的集 是*Q_Z中小于0的部分. 即, 负整数是 自然数的负值 *)
Property Q'_N_Neg_equ_Q'_Z_lt_Q'0 : \{ λ u, u ∈ Q'_Z /\ u < Q'0 \}
    = \{ λ u, u ∈ Q'  /\ ∃ v, v ∈ (Q'_N ~ [Q'0]) /\ u + v = Q'0 \}.
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H as [H[]]. apply AxiomII; repeat split; auto.
    apply Q'_Z_subset_Q'; auto. pose proof H0. apply Q'_Z_subset_Q' in H2; auto.
    pose proof H2. apply Q'_Neg in H3 as [z0[[]_]]; auto.
    exists z0. split; auto. apply MKT4'; split.
    + rewrite Q'_N_equ_Q'_Z_me_Q'0; auto. apply AxiomII; split; eauto.
      rewrite <-H4 in H1. assert ((z + Q'0) < (z + z0)).
      { rewrite Q'_Plus_Property; auto. }
      apply Q'_Plus_PrOrder in H5; try apply Q'0_in_Q'; auto. split; auto.
      apply AxiomII; split; eauto. pose proof H0.
      apply AxiomII in H6 as [_[u[]]]. pose proof H6.
      apply Z'_Z_subset_Z' in H8; auto. pose proof H8.
      apply Z'_Neg in H9 as [u0[[]_]]; auto.
      assert (z0 = \[[u0,(Z'1)]\]).
      { apply (Q'_Neg_Instantiate u u0 _ z0); auto with Z'.
        rewrite <-H7; auto. } exists u0. split; auto.
      apply AxiomII in H6 as [_[M[N[H6[]]]]].
      assert (u0 = \[[N,M]\])%z'.
      { apply Z'_Neg_Instantiate; auto; try apply N'_N_subset_N'; auto.
        rewrite <-H13; auto. }
      apply AxiomII; split; eauto.
    + apply AxiomII; split; eauto. intro. pose proof Q'0_in_Q'.
      apply MKT41 in H5; eauto. rewrite H5,Q'_Plus_Property in H4; auto.
      rewrite <-H4 in H1. elim (Q'_Ord_irReflex z z); auto.
  - apply AxiomII in H as [H[H0[x[]]]]. apply MKT4' in H1 as [].
    pose proof H1. apply Q'_N_subset_Q' in H4; auto.
    pose proof H1. rewrite Q'_N_equ_Q'_Z_me_Q'0 in H5; auto.
    apply AxiomII in H5 as [_[]]. apply AxiomII; repeat split; auto.
    + rewrite Q'_Plus_Commutation in H2; auto.
      apply Q'_Minus_Plus in H2; auto with Q'. rewrite <-H2.
      apply Q'_Z_Minus_in_Q'_Z; auto. apply Q'0_in_Q'_Z; auto.
    + destruct H6.
      * rewrite H6 in H3. apply AxiomII in H3 as []. elim H7. apply MKT41; eauto.
      * rewrite <-H2 in H6. apply (Q'_Plus_PrOrder _ _ x);
        try apply Q'0_in_Q'; auto. rewrite Q'_Plus_Commutation,
        Q'_Plus_Property; auto.
Qed.

(* 根据以上分析立得: *Q_N 是 *Q_Z 的真子集. *)
Property Q'_N_propersubset_Q'_Z : Q'_N ⊂ Q'_Z /\ Q'_N <> Q'_Z.
Proof.
  split.
  - unfold Included; intros. rewrite Q'_N_equ_Q'_Z_me_Q'0 in H; auto.
    apply AxiomII in H; tauto.
  - intro. pose proof Q'1_in_Q'_N. pose proof Q'1_in_Q'.
    pose proof H1. apply Q'_Neg in H2 as [a[[]_]]; auto.
    assert (a ∈ \{ λ u, u ∈ Q' /\ ∃ v, v ∈ (Q'_N ~ [Q'0]) /\ u + v = Q'0 \}).
    { apply AxiomII; repeat split; eauto. exists Q'1. split.
      apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
      pose proof Q'0_in_Q'. apply MKT41 in H4; eauto.
      elim Q'0_isnot_Q'1; auto. rewrite Q'_Plus_Commutation; auto. }
    rewrite <-Q'_N_Neg_equ_Q'_Z_lt_Q'0 in H4; auto.
    apply AxiomII in H4 as [H4[]]. rewrite <-H,Q'_N_equ_Q'_Z_me_Q'0 in H5; auto.
    apply AxiomII in H5 as [_[H7[]]].
    + rewrite H5 in H6. elim (Q'_Ord_irReflex a a); auto.
    + apply (Q'_Ord_Trans a) in H5; try apply Q'0_in_Q'; auto.
      elim (Q'_Ord_irReflex a a); auto.
Qed.

(* *Q_*N真包含 *Q_N. *)
Property Q'_Z_propersubset_Q'_Z' : Q'_Z ⊂ Q'_Z' /\ Q'_Z <> Q'_Z'.
Proof.
  destruct NPAUF as []. split.
  - unfold Included; intros. apply AxiomII in H1 as [H1[x[]]].
    apply AxiomII; split; eauto. exists x. split; auto. apply Z'_Z_subset_Z'; auto.
  - destruct Z'_Z_propersubset_Z'.
    assert (Z' ~ Z'_Z <> Φ).
    { intro. elim H2. apply AxiomI; split; intros. apply H1; auto.
      apply NNPP; intro. elim (@ MKT16 z). rewrite <-H3.
      apply MKT4'; split; auto. apply AxiomII; split; eauto. }
    apply NEexE in H3 as []. set (u := \[[x,(Z'1)]\]). assert (u ∈ Q').
    { apply Q'_Instantiate2; auto. apply MKT4' in H3; tauto.
      apply MKT4'; split; eauto with Z'. apply AxiomII; split; eauto with Z'.
      intro. apply MKT41 in H4; eauto with Z'. elim Z'0_isnot_Z'1; auto. }
    assert (u ∈ Q'_Z').
    { apply AxiomII; split; eauto. exists x. split; auto.
      apply MKT4' in H3; tauto. }
    intro. rewrite <-H6 in H5. apply AxiomII in H5 as [_[y[]]]. unfold u in H7.
    apply MKT4' in H3 as []. apply R_Z'_Property in H7; auto with Z'.
    rewrite Z'_Mult_Property2,Z'_Mult_Commutation,Z'_Mult_Property2 in H7;
    auto with Z'. apply AxiomII in H8 as []. elim H9. rewrite H7; auto.
Qed.

(* *Q_Q 是由 *Z_Z 以 *Z × ( *Z ~ [0] ) 上的等价关系扩张而来.*)
Definition Q'_Q := \{ λ u, ∃ a b, a ∈ Z'_Z
  /\ b ∈ (Z'_Z ~ [Z'0]) /\ u = \[[a,b]\] \}.

Property Q'_Q_subset_Q' : Q'_Q ⊂ Q' .
Proof.
  unfold Included; intros. apply AxiomII in H as [H[x[x0[H0[]]]]].
  rewrite H2. Z'split1 H1 H3. apply Q'_Instantiate2; auto.
  apply Z'_Z_subset_Z'; auto.
Qed.

Property Q'0_in_Q'_Q : Q'0 ∈ Q'_Q.
Proof.
  intros. apply AxiomII; split; eauto with Q'.
  exists (Z'0),(Z'1). split. apply Z'0_in_Z'_Z; auto.
  split. apply MKT4'; split. apply Z'1_in_Z'_Z; auto.
  apply AxiomII; split. eauto with Z'. intro.
  apply MKT41 in H; eauto with Z'. elim Z'0_isnot_Z'1; auto.
  rewrite Q'0_Property; auto.
Qed.

Property Q'1_in_Q'_Q : Q'1 ∈ Q'_Q.
Proof.
  intros. apply AxiomII; split; eauto with Q'.
  exists (Z'1),(Z'1). split. apply Z'1_in_Z'_Z; auto.
  split. apply MKT4'; split. apply Z'1_in_Z'_Z; auto.
  apply AxiomII; split. eauto with Z'. intro.
  apply MKT41 in H; eauto with Z'. elim Z'0_isnot_Z'1; auto.
  rewrite Q'1_Property; auto.
Qed.

(* *Q_Q对加法封闭. *)
Property Q'_Q_Plus_in_Q'_Q : ∀ u v, u ∈ Q'_Q -> v ∈ Q'_Q -> (u + v) ∈ Q'_Q.
Proof.
  intros. pose proof H; pose proof H0.
  apply Q'_Q_subset_Q' in H1; apply Q'_Q_subset_Q' in H2; auto.
  pose proof H1. apply (Q'_Plus_in_Q' u v) in H3; auto.
  apply AxiomII; split; eauto. apply AxiomII in H as [H[x[y[H4[]]]]].
  apply AxiomII in H0 as [H0[x1[y1[H7[]]]]].
  exists ((x · y1) + (y · x1))%z',(y · y1)%z'.
  Z'split1 H5 H10. Z'split1 H8 H13. repeat split.
  - apply MKT4' in H5 as []. apply MKT4' in H8 as [].
    apply Z'_Z_Plus_in_Z'_Z; try apply Z'_Z_Mult_in_Z'_Z; auto.
  - apply MKT4'; split. apply MKT4' in H8 as [].
    apply MKT4' in H5 as []. apply Z'_Z_Mult_in_Z'_Z; auto.
    assert ((y · y1)%z' ∈ Z'). { apply Z'_Mult_in_Z'; auto. }
    apply AxiomII; split; eauto. intro. pose proof Z'0_in_Z'.
    apply MKT41 in H17; eauto. apply Z'_Mult_Property3 in H17 as []; auto.
  - rewrite H6,H9,Q'_Plus_Instantiate; auto; try apply Z'_Z_subset_Z'; auto.
Qed.

(* *Q_Q对乘法封闭. *)
Property Q'_Q_Mult_in_Q'_Q : ∀ u v, u ∈ Q'_Q -> v ∈ Q'_Q -> (u · v) ∈ Q'_Q.
Proof.
  intros. pose proof H; pose proof H0.
  apply Q'_Q_subset_Q' in H1; apply Q'_Q_subset_Q' in H2; auto.
  pose proof H1. apply (Q'_Mult_in_Q' u v) in H3; auto.
  apply AxiomII; split; eauto.
  apply AxiomII in H as [H[x[y[H4[]]]]].
  apply AxiomII in H0 as [H0[x1[y1[H7[]]]]].
  exists (x · x1)%z',(y · y1)%z'.
  Z'split1 H5 H10. Z'split1 H8 H13. repeat split.
  - apply Z'_Z_Mult_in_Z'_Z; auto.
  - apply MKT4'; split. apply MKT4' in H8 as [].
    apply MKT4' in H5 as []. apply Z'_Z_Mult_in_Z'_Z; auto.
    assert ((y · y1)%z' ∈ Z'). { apply Z'_Mult_in_Z'; auto. }
    apply AxiomII; split; eauto. intro. pose proof Z'0_in_Z'.
    apply MKT41 in H17; eauto. apply Z'_Mult_Property3 in H17 as []; auto.
  - rewrite H6,H9,Q'_Mult_Instantiate; auto; try apply Z'_Z_subset_Z'; auto.
Qed.

(* *Q_Q对减法封闭. *)
Property Q'_Q_Minus_in_Q'_Q : ∀ u v, u ∈ Q'_Q -> v ∈ Q'_Q -> (u - v) ∈ Q'_Q.
Proof.
  intros. pose proof H; pose proof H0.
  apply Q'_Q_subset_Q' in H1; apply Q'_Q_subset_Q' in H2; auto.
  apply AxiomII in H as [H[x[y[H3[]]]]].
  apply AxiomII in H0 as [H0[x1[y1[H6[]]]]].
  pose proof H3; pose proof H6.
  apply Z'_Z_subset_Z' in H9; apply Z'_Z_subset_Z' in H10; auto.
  Z'split1 H4 H11. Z'split1 H7 H14. pose proof H7; pose proof H4.
  apply MKT4' in H17 as [H17 _]. apply MKT4' in H18 as [H18 _].
  Q'altH H5 x y y1. Q'altH H8 x1 y1 y. set (a := (y1 · x)%z').
  set (b := (y1 · y)%z'). set (c := (y · x1)%z').
  assert (u = \[[a,b]\]); auto. assert (v = \[[c,b]\]).
  { rewrite H8,(Z'_Mult_Commutation y y1); auto. }
  assert (a ∈ Z'_Z). { apply Z'_Z_Mult_in_Z'_Z; auto. }
  assert (b ∈ Z'_Z). { apply Z'_Z_Mult_in_Z'_Z; auto. }
  assert (c ∈ Z'_Z). { apply Z'_Z_Mult_in_Z'_Z; auto. }
  assert (b ∈ (Z'_Z ~ [Z'0])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. pose proof Z'0_in_Z'. apply MKT41 in H24; eauto.
    apply Z'_Mult_Property3 in H24 as []; auto. }
  clear H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18.
  pose proof H21; pose proof H22; pose proof H23.
  apply Z'_Z_subset_Z' in H3; apply Z'_Z_subset_Z' in H4;
  apply Z'_Z_subset_Z' in H5; auto. Z'split1 H24 H6. pose proof H23.
  apply (Q'_Z_Minus_in_Q'_Z_Lemma2 c a) in H9 as [w[[]_]]; auto.
  pose proof H9. apply Z'_Z_subset_Z' in H11; auto.
  set (k := \[[w,b]\]).
  assert (k ∈ Q' ). { apply Q'_Instantiate2; auto. }
  assert (k ∈ Q'_Q). { apply AxiomII; split; eauto. }
  replace k with (u - v) in H13; auto. apply Q'_Minus_Plus; auto. unfold k.
  rewrite H19,H20,Q'_Plus_Instantiate,(Z'_Mult_Commutation c),
  <-Z'_Mult_Distribution,<-(Q'_equClass_alter _ _ b),H10; auto.
  apply Z'_Plus_in_Z'; auto.
Qed.

(* *Q_Q对除法封闭. *)
Property Q'_Q_Divide_in_Q'_Q : ∀ u v, u ∈ Q'_Q -> v ∈ Q'_Q -> v <> Q'0
  -> (u / v) ∈ Q'_Q.
Proof.
  intros. pose proof H; pose proof H0.
  apply Q'_Q_subset_Q' in H2; apply Q'_Q_subset_Q' in H3; auto.
  apply AxiomII in H as [H[x[y[H4[]]]]].
  apply AxiomII in H0 as [H0[x1[y1[H7[]]]]].
  assert (x1 ∈ (Z'_Z ~ [Z'0])).
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H10; eauto with Z'. elim H1.
    rewrite H9,H10,Q'0_Property; auto. apply R_Z'_Property; auto with Z'.
    Z'split1 H8 H11. auto. rewrite Z'_Mult_Property2,Z'_Mult_Property1;
    auto with Z'. Z'split1 H8 H11. auto. } set (v1 := \[[y1, x1]\]).
  assert (v1 ∈ Q' ).
  { apply Q'_Instantiate2; auto. Z'split1 H8 H11. auto.
    apply Z'split1_Lemma; auto. }
  assert (v · v1 = Q'1).
  { rewrite H9. unfold v1. rewrite Q'_Mult_Instantiate; auto;
    Z'split1 H10 H12; auto; Z'split1 H8 H15; auto. rewrite Q'1_Property; auto.
    apply R_Z'_Property; auto with Z'.
    rewrite Z'_Mult_Property2,Z'_Mult_Property2,Z'_Mult_Commutation;
    auto with Z'. }
  assert (u / v = u · v1).
  { apply Q'_Divide_Mult; auto with Q'.
    rewrite (Q'_Mult_Commutation u),<-Q'_Mult_Association,H12,
    Q'_Mult_Commutation,Q'_Mult_Property2; auto with Q'. }
  rewrite H13. apply Q'_Q_Mult_in_Q'_Q; auto; [rewrite H6|];
  apply AxiomII; split; eauto. rewrite <-H6; auto.
  exists y1,x1. split; auto. apply MKT4' in H8; tauto.
Qed.

(* *Q_Q与*Q_Z的关系: *Q_Q是*Q_Z中的元素做除法而来. *)
Property Q'_Q_equ_Q'_Z_Div : Q'_Q = \{ λ u, u ∈ Q' /\ ∃ a b, a ∈ Q'_Z
    /\ b ∈ (Q'_Z ~ [Q'0]) /\ u = a / b \}.
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII; repeat split; eauto. apply Q'_Q_subset_Q'; auto.
    apply AxiomII in H as [H[x[y[H0[]]]]]. exists (\[[x,(Z'1)]\]),(\[[y,(Z'1)]\]).
    pose proof H0. apply Z'_Z_subset_Z' in H3; auto. Z'split1 H1 H4.
    assert (\[[y,(Z'1)]\] ∈ Q' ). { apply Q'_Instantiate2; auto with Z'. }
    assert (\[[x,(Z'1)]\] ∈ Q' ). { apply Q'_Instantiate2; auto with Z'. }
    repeat split.
    + apply AxiomII; split; eauto.
    + apply MKT4'; split. apply AxiomII; split; eauto. exists y. split; auto.
      apply MKT4' in H1; tauto. apply AxiomII; split; eauto.
      intro. pose proof Q'0_in_Q'. apply MKT41 in H9; eauto.
      rewrite Q'0_Property in H9; auto. apply R_Z'_Property in H9; auto with Z'.
      rewrite Z'_Mult_Property2,Z'_Mult_Property1 in H9; auto with Z'.
    + symmetry. apply (Q'_Divide_Mult _ z); auto. intro.
      rewrite Q'0_Property in H9; auto. apply R_Z'_Property in H9; auto with Z'.
      rewrite Z'_Mult_Property2,Z'_Mult_Property1 in H9; auto with Z'.
      rewrite H2. apply Q'_Instantiate2; auto.
      rewrite H2,Q'_Mult_Instantiate; auto with Z'.
      rewrite (Z'_Mult_Commutation _ y),Z'_Mult_Property2; auto with Z'.
      apply R_Z'_Property; auto with Z'. rewrite Z'_Mult_Property2; auto with Z'.
  - apply AxiomII in H as [H[H0[a[b[H1[]]]]]]. pose proof H2.
    apply MKT4' in H4 as []. pose proof H4. apply AxiomII in H6 as [H6[y[]]].
    pose proof H1. apply AxiomII in H9 as [H9[x[]]]. apply AxiomII; split; auto.
    exists x,y. repeat split; auto.
    + apply MKT4'; split; auto. apply AxiomII; split; eauto.
      intro. pose proof Z'0_in_Z'. apply MKT41 in H12; eauto. rewrite H12 in H8.
      apply AxiomII in H5 as []. elim H14. pose proof Q'0_in_Q'.
      apply MKT41; eauto. rewrite H8,Q'0_Property; auto.
    + inQ' H0 u v. pose proof H7. apply Z'_Z_subset_Z' in H16; auto.
      symmetry in H3. apply Q'_Divide_Mult in H3;
      try (rewrite H15; apply Q'_Instantiate2); try apply Q'_Z_subset_Q'; auto.
      rewrite H11,H8,H15,Q'_Mult_Instantiate,
      (Z'_Mult_Commutation _ v),Z'_Mult_Property2 in H3; auto with Z'.
      apply Z'_Z_subset_Z' in H10; auto. apply R_Z'_Property in H3; auto with Z'.
      rewrite Z'_Mult_Property2 in H3; auto with Z'. rewrite H15.
      apply R_Z'_Property; auto. apply MKT4'; split; auto.
      apply AxiomII; split; eauto. intro. pose proof Z'0_in_Z'.
      apply MKT41 in H17; eauto. rewrite H17 in H8.
      rewrite <-Q'0_Property in H8; auto. rewrite <-H8 in H5.
      apply AxiomII in H5 as []. elim H19. apply MKT41; eauto.
      rewrite Z'_Mult_Commutation; auto. apply AxiomII in H5 as [].
      intro. elim H18. pose proof Q'0_in_Q'. apply MKT41; eauto.
Qed.

(* 两个*Q_Z中的元素相除其结果在*Q_Q中. *)
Property Q'_Z_Divide_in_Q'_Q : ∀ v u, v ∈ Q'_Z -> u ∈ Q'_Z -> u <> Q'0
  -> (v / u) ∈ Q'_Q.
Proof.
  intros. pose proof H. pose proof H0.
  apply Q'_Z_subset_Q' in H2; apply Q'_Z_subset_Q' in H3; auto.
  pose proof H2. apply (Q'_Divide_in_Q' v u) in H4; auto.
  rewrite Q'_Q_equ_Q'_Z_Div; auto. apply AxiomII; repeat split; eauto.
  exists v,u. repeat split; auto. apply MKT4'; split; auto.
  apply AxiomII; split; eauto. intro. pose proof Q'0_in_Q'.
  apply MKT41 in H5; eauto.
Qed.

(* *Q_Z 是 *Q_Q 的真子集. *)
Property Q'_Z_propersubset_Q'_Q : Q'_Z ⊂ Q'_Q /\ Q'_Z <> Q'_Q.
Proof.
  intros. assert (Z'1 ∈ (Z'_Z ~ [Z'0])).
  { pose proof Z'1_in_Z'. apply MKT4'; split. apply AxiomII; split; eauto.
    exists (F 1),(F 0). pose proof in_ω_0; pose proof in_ω_1.
    rewrite Z'1_Property; auto. repeat split; auto; apply Fn_in_N'_N; auto.
    apply AxiomII; split; eauto. intro. pose proof Z'0_in_Z'.
    apply MKT41 in H0; eauto. elim Z'0_isnot_Z'1; auto. }
  split.
  - unfold Included; intros. apply AxiomII in H0 as [H0[x[]]].
    apply AxiomII; repeat split; auto. exists x,(Z'1). repeat split; auto.
  - intro. set (two := (Z'1 + Z'1)%z').
    assert (two ∈ (Z'_Z ~ [Z'0])).
    { assert (two ∈ Z'). unfold two. auto with Z'.
      assert (two ∈ Z'_Z).
      { apply AxiomII; split; eauto. exists ((F 1) + (F 1))%n',((F 0) + (F 0))%n'.
        unfold two. pose proof in_ω_0; pose proof in_ω_1.
        rewrite Z'1_Property,Z'_Plus_Instantiate; try apply Fn_in_N'; auto.
        repeat split; try apply N'_N_Plus_in_N'_N; try apply Fn_in_N'_N; auto. }
      apply MKT4'; split; auto. apply AxiomII; split; eauto. intro.
      pose proof Z'0_in_Z'. apply MKT41 in H3; eauto. pose proof Z'0_lt_Z'1.
      pose proof H5. apply (Z'_Plus_PrOrder _ _ (Z'1)) in H6; auto with Z'.
      unfold two in H3. rewrite Z'_Plus_Property,H3 in H6; auto with Z'.
      apply (Z'_Ord_Trans Z'0) in H6; auto with Z'.
      elim (Z'_Ord_irReflex Z'0 Z'0); auto with Z'. }
    set (dw := \[[Z'1,two]\]). Z'split1 H1 H2.
    assert (dw ∈ Q' ). { apply Q'_Instantiate2; auto with Z'. }
    assert (dw ∈ Q'_Q).
    { apply AxiomII; split; eauto. exists (Z'1),two.
      repeat split; auto. apply MKT4' in H; tauto. }
    assert ((Z'0) < two)%z'.
    { unfold two. apply (Z'_Ord_Trans _ Z'1); auto with Z'.
      pose proof Z'0_lt_Z'1. apply (Z'_Plus_PrOrder _ _ Z'1) in H7; auto with Z'.
      rewrite Z'_Plus_Property in H7; auto with Z'. }
    assert (Q'0 < dw).
    { rewrite Q'0_Property; auto. unfold dw.
      apply Q'_Ord_Instantiate; auto with Z'.
      rewrite Z'_Mult_Commutation,Z'_Mult_Property1,Z'_Mult_Property2;
      auto with Z'. }
    assert (dw < Q'1).
    { unfold dw. rewrite Q'1_Property; auto.
      apply Q'_Ord_Instantiate; auto with Z'.
      rewrite Z'_Mult_Property2,Z'_Mult_Property2; auto with Z'.
      replace (Z'1) with (Z'1 + Z'0)%z'.
      unfold two. apply Z'_Plus_PrOrder; auto with Z'.
      apply Z'_Plus_Property; auto with Z'. }
    rewrite <-H0 in H6. assert (dw ∈ Q'_N).
    { rewrite Q'_N_equ_Q'_Z_me_Q'0; auto. apply AxiomII; repeat split; eauto. }
    destruct φ4_is_Function as [[][]]. assert (dw ∈ ran(φ4)); auto.
    rewrite reqdi in H15. apply Property_Value,Property_ran in H15; auto.
    rewrite <-deqri,H13 in H15.
    assert (dw = φ4[(φ4⁻¹)[dw]]). { rewrite f11vi; auto. }
    rewrite H16,<-φ4_0 in H8; auto. rewrite H16,<-φ4_1 in H9; auto.
    pose proof in_ω_0; pose proof in_ω_1.
    apply φ4_PrOrder in H8; apply φ4_PrOrder in H9; auto.
    apply MKT41 in H9; eauto. rewrite H9 in H8. elim (@ MKT16 0); auto.
Qed.


