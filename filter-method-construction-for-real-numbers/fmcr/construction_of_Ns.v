(*    This file presents the formalization for construction of *N.   *)
(*  It is developmented in the CoqIDE (version 8.13.2) for windows.  *)

(** construction_of_N' *)

Require Export filters.arithmetical_ultrafilter.

(* 声明一个ω上的非主算术超滤 *)
Parameter F0 : Class.
Parameter NPAUF : Arithmetical_ultraFilter F0 ω /\ (∀ m, F0 <> (F ω m)).

Fact NPAUF_is_UF : F0 ∈ β ω.
Proof. destruct NPAUF as [[_[]]]; auto. Qed.
Global Hint Resolve NPAUF_is_UF : core.

Declare Scope n'_scope.
Delimit Scope n'_scope with n'.
Open Scope n'_scope.

Notation "f 〈 F0 〉" := (f〈F0∣ω〉)(at level 5) : n'_scope.
Notation F n := (filter.F ω n).
Notation Const n := (arithmetical_ultrafilter.Const ω n).
Notation βω := (arithmetical_ultrafilter.β ω).

(* 定义 关于 非主算术超滤F0 的算术模型 *N *)
Definition N' :=  \{ λ u, ∃ f, Function f
  /\ dom(f) = ω /\ ran(f) ⊂ ω /\ u = f〈F0〉 \}.

Property N'_subset_βω : N' ⊂ βω.
Proof.
  unfold Included; intros. apply AxiomII in H as [H[f[H0[H1[]]]]].
  rewrite H3. apply (FT4 _ _ ω); auto. New MKT138. eauto.
Qed.

Property N'_is_Set : Ensemble N'.
Proof.
  apply (MKT33 βω). apply βA_is_Set. apply N'_subset_βω; auto.
Qed.
(* 于是由算数超滤生成的*N也一定是一个集*)

(* 任意主超滤都在*N中*)
Property Fn_in_N' : ∀ n, n ∈ ω -> (F n) ∈ N'.
Proof.
  intros. assert (Ensemble (F n)).
  { apply (Filter_is_Set_Fact2 _ ω). apply Fa_P2_b in H.
    destruct H; auto. New MKT138; eauto. }
  pose proof H. apply (F_Const_Fa F0 ω) in H1; auto.
  apply AxiomII; split; auto. exists (Const n). assert (Ensemble n) by eauto.
  apply (Const_is_Function ω n) in H2 as [H2[]]. split; auto. repeat split; auto.
  unfold Included; intros. rewrite H4 in H5. apply MKT41 in H5; eauto.
  rewrite H5; auto. intro. rewrite H3 in H. elim (@ MKT16 n); auto.
Qed.

(* 定义 *N上的序(小于)关系 原始定义: f〈F0〉 前于 g〈F0〉 就是说f在F0的某个集上始终小于g.
                    *N上的u和v, u前于v就是说, 所有生成u的函数f和
                    所有生成v的函数g 都要满足f在F0的某个集上始终小于g.
                    (在这种加强了的描述下, 证明三分律的过程中'算术超滤'的前提是必要的) *)
Definition N'_Ord := \{\ λ u v, ∀ f g, Function f -> Function g
  -> dom(f) = ω -> dom(g) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω
  -> u = f〈F0〉 -> v = g〈F0〉 -> \{ λ w, f[w] ∈ g[w] \} ∈ F0 \}\.

Notation "u < v" := ([u,v] ∈ N'_Ord) : n'_scope.

(* *N上序关系的实例化描述:  f1〈F0〉 前于 f2〈F0〉 实际上就是
                       ((\{ λ w, f1[w] ∈ f2[w] \}) ∈ F0)        *)
Property N'_Ord_Instantiate : ∀ f g, Function f -> Function g
  -> dom(f) = ω -> dom(g) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω
  -> f〈F0〉 < g〈F0〉 <-> \{ λ w, f[w] ∈ g[w] \} ∈ F0.
Proof.
  split; intros.
  - apply AxiomII' in H5 as []. apply H6; auto.
  - assert ((f〈F0〉) ∈ βω /\ (g〈F0〉) ∈ βω) as [].
    { New MKT138. split; apply (FT4 _ _ ω); auto; destruct NPAUF as [[]]; eauto. }
    apply AxiomII'; split; intros. apply MKT49a; eauto.
    destruct NPAUF as [[]_]. apply H17 in H14; apply H17 in H15; auto.
    clear H8 H9 H10 H11 H12 H13.
    destruct H14 as [H8[H9[H10[H11[H12[H13[]]]]]]].
    destruct H15 as [H15[H19[H20[H21[H22[H23[]]]]]]].
    set (A := \{ λ u, u ∈ ω /\ f[u] = f0[u] \}).
    set (B := \{ λ u, u ∈ ω /\ g[u] = g0[u] \}).
    set (C := \{ λ w, f[w] ∈ g[w] \}).
    assert ((C ∩ A ∩ B) ⊂ \{ λ w, f0[w] ∈ g0[w] \}).
    { unfold Included; intros. apply MKT4' in H26 as [].
      apply MKT4' in H27 as []. apply AxiomII in H26 as [].
      apply AxiomII in H27 as [H27[]].
      apply AxiomII in H28 as [H28[]].
      apply AxiomII; split; auto. rewrite <-H31,<-H33; auto. }
    apply AxiomII in H24 as [H24[[H27[H28[H29[]]]]]].
    apply (H31 (C ∩ A ∩ B)); repeat split; auto.
    unfold Included; intros. apply AxiomII in H33 as [].
    apply NNPP; intro. rewrite <-H11 in H35. apply MKT69a in H35.
    rewrite H35 in H34. elim MKT39; eauto.
Qed.

(*验证  序的定义的合理性: 序关系与表示元素的函数无关.
       当 f1〈F0〉 = f2〈F0〉  g1〈F0〉 = g2〈F0〉
          ((\{ λ w, f1[w] ∈ g1[w] \}) ∈ F0)  就等价于
          ((\{ λ w, f2[w] ∈ g2[w] \}) ∈ F0)
       [注: 实际上就是要验证:
           表示同一元素的不同函数相对于表示其他元素的函数的大小关系要保持一致.]      *)
Property N'_Ord_Reasonable : ∀ f1 f2 g1 g2,
  Function f1 -> Function f2 -> Function g1 -> Function g2
  -> dom(f1) = ω -> dom(f2) = ω -> dom(g1) = ω -> dom(g2) = ω
  -> ran(f1) ⊂ ω -> ran(f2) ⊂ ω -> ran(g1) ⊂ ω -> ran(g2) ⊂ ω
  -> f1〈F0〉 = f2〈F0〉 -> g1〈F0〉 = g2〈F0〉
  -> f1〈F0〉 < g1〈F0〉 <-> f2〈F0〉 < g2〈F0〉.
Proof.
  destruct NPAUF as [H _]. intros. pose proof H as Ha.
  destruct H. apply H14 in H12; apply H14 in H13; auto.
  clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
  destruct H12 as [H12[H0[H1[H2[H3[H4[]]]]]]].
  destruct H13 as [H13[H7[H8[H9[H10[H11[]]]]]]].
  set (A := \{ λ u, u ∈ ω /\ f1[u] = f2[u] \}).
  set (B := \{ λ u, u ∈ ω /\ g1[u] = g2[u] \}).
  set (C := \{ λ w, f1[w] ∈ g1[w] \}).
  set (D := \{ λ w, f2[w] ∈ g2[w] \}).
  assert ((C ∩ A ∩ B) ⊂ D).
  { unfold Included; intros. apply MKT4' in H17 as [].
    apply MKT4' in H18 as []. apply AxiomII in H17 as [].
    apply AxiomII in H18 as [H18[]].
    apply AxiomII in H19 as [H19[]].
    apply AxiomII. rewrite <-H22,<-H24; auto. }
  assert ((D ∩ A ∩ B) ⊂ C).
  { unfold Included; intros. apply MKT4' in H18 as [].
    apply MKT4' in H19 as []. apply AxiomII in H18 as [].
    apply AxiomII in H19 as [H19[]].
    apply AxiomII in H20 as [H20[]].
    apply AxiomII. rewrite H23,H25; auto. }
  apply AxiomII in H15 as [H15[[H19[H20[H21[]]]]]].
  split; intros; apply N'_Ord_Instantiate; auto;
  apply N'_Ord_Instantiate in H25; auto.
  - apply (H23 (C ∩ A ∩ B)); repeat split; auto.
    unfold Included; intros. apply AxiomII in H26 as [].
    apply NNPP; intro. rewrite <-H2 in H28. apply MKT69a in H28.
    rewrite H28 in H27. elim MKT39; eauto.
  - apply (H23 (D ∩ A ∩ B)); repeat split; auto.
    unfold Included; intros. apply AxiomII in H26 as [].
    apply NNPP; intro. rewrite <-H1 in H28. apply MKT69a in H28.
    rewrite H28 in H27. elim MKT39; eauto.
Qed.

Open Scope ω_scope.

Property N'0_isnot_N'1 : F 0 <> F 1.
Proof.
  destruct MKT135; pose proof in_ω_1. apply (Example2 ω 0 1); auto. intro.
  assert (0 ∈ 1). { apply MKT41; eauto. }
  rewrite <-H2 in H3. pose proof (@ MKT16 Φ); auto.
Qed.

Property N'0_lt_N'1 : (F 0) < (F 1).
Proof.
  destruct NPAUF as [H _]. intros.
  assert (Ensemble 0 /\ Ensemble 1) as [].
  { pose proof in_ω_0; pose proof in_ω_1; eauto. }
  assert (ω <> 0) as HH.
  { intro. pose proof in_ω_0. rewrite H2 in H3. elim (@ MKT16 0); eauto. }
  apply (Const_is_Function ω) in H0 as [H0[]]; auto.
  apply (Const_is_Function ω) in H1 as [H1[]]; auto.
  pose proof in_ω_0; pose proof in_ω_1.
  assert (ran(Const 0) ⊂ ω /\ ran(Const 1) ⊂ ω) as [].
  { split; [rewrite H3|rewrite H5]; unfold Included; intros;
    apply MKT41 in H8; eauto; rewrite H8; auto. }
  pose proof in_ω_0; pose proof in_ω_1.
  apply (F_Const_Fa F0 ω) in H10; [ |destruct H]; auto.
  apply (F_Const_Fa F0 ω) in H11; [ |destruct H]; auto.
  rewrite <-H10,<-H11. apply N'_Ord_Instantiate; auto.
  assert (\{ λ w, (Const 0)[w] ∈ (Const 1)[w] \} = ω).
  { apply AxiomI; split; intros.
    - apply AxiomII in H12 as []. apply NNPP; intro.
      rewrite <-H2 in H14. apply MKT69a in H14.
      rewrite H14 in H13. elim MKT39; eauto.
    - apply AxiomII; split; eauto. pose proof H12.
      rewrite <-H2 in H12. rewrite <-H4 in H13.
      apply Property_Value,Property_ran in H12; auto.
      apply Property_Value,Property_ran in H13; auto.
      rewrite H3 in H12. rewrite H5 in H13.
      apply MKT41 in H12; eauto. apply MKT41 in H13; eauto.
      rewrite H12,H13. apply MKT41; eauto. }
  destruct H as [_[]]. rewrite H12. apply AxiomII in H as [H[[]]]; tauto.
Qed.

Property N'0_is_FirstMember : ∀ u, u ∈ N' -> ~ u < (F 0).
Proof.
  destruct NPAUF as [H _]. intros. intro. apply AxiomII' in H1 as [].
  apply AxiomII in H0 as [H0[f[H3[H4[]]]]].
  pose proof in_ω_0. apply Fn_in_N' in H7. destruct H as [_[]].
  pose proof in_ω_0. apply (F_Const_Fa F0 ω) in H9; auto.
  assert (Ensemble 0) by (pose proof in_ω_0; eauto).
  apply (Const_is_Function ω) in H10 as [H10[]].
  pose proof H3. apply (H2 f (Const 0)) in H13; auto.
  assert (\{ λ w, f [w] ∈ (Const 0)[w] \} = 0).
  { apply AxiomI; split; intros; elim (@ MKT16 z); auto.
    apply AxiomII in H14 as []. destruct (classic (z ∈ ω)).
    rewrite <-H11 in H16. apply Property_Value,Property_ran
    in H16; auto. rewrite H12 in H16.
    apply MKT41 in H16; pose proof in_ω_0; eauto.
    rewrite H16 in H15. elim (@ MKT16 (f[z])); auto.
    rewrite <-H4 in H16. apply MKT69a in H16.
    rewrite H16 in H15. elim MKT39; eauto. }
  rewrite H14 in H13. apply AxiomII in H as [H[[H15[]]]]; auto.
  unfold Included; intros. rewrite H12 in H14.
  apply MKT41 in H14; pose proof in_ω_0; eauto. rewrite H14; auto.
  pose proof in_ω_1. intro. rewrite H12 in H11. elim (@ MKT16 1); auto.
Qed.

(* *N上定义的 N'_Ord关系 具有反自反性 *)
Property N'_Ord_irReflex_weak : ∀ u, u ∈ N' -> ~ u < u.
Proof.
  destruct NPAUF as [[_[H _]] _]. intros; intro.
  apply AxiomII in H0 as [H0[f[H2[H3[]]]]]. apply AxiomII' in H1 as [].
  assert (\{ λ w, f[w] ∈ f[w] \} ∈ F0). { apply H6; auto. }
  assert (\{ λ w, f[w] ∈ f[w] \} = Φ).
  { apply AxiomI; split; intros. apply AxiomII in H8 as [].
    pose proof (MKT101 (f[z])). contradiction.
    elim (@ MKT16 z); auto. }
  rewrite H8 in H7. apply AxiomII in H as [H[[H9[]]]].
  contradiction.
Qed.

(* 反自反性的强化表述 *)
Property N'_Ord_irReflex : ∀ u v, u ∈ N' -> v ∈ N' -> u = v -> ~ u < v.
Proof.
  destruct NPAUF as [H _]. intros. intro.
  apply AxiomII in H0 as [H0[f1[H4[H5[]]]]].
  apply AxiomII in H1 as [H1[f2[H8[H9[]]]]]. rewrite H7,H11 in H3.
  apply N'_Ord_Instantiate in H3; auto. rewrite H7,H11 in H2.
  destruct H. apply H12 in H2; auto.
  clear H4 H5 H6 H7 H8 H9 H10 H11.
  destruct H2 as [H2[H4[H5[H6[H7[H8[]]]]]]].
  assert (\{ λ u, u ∈ ω /\ f1[u] = f2[u] \}
    ∩ \{ λ w, f1[w] ∈ f2[w] \} = Φ).
  { apply AxiomI; split; intros. apply MKT4' in H11 as [].
    apply AxiomII in H11 as [H11[]]. apply AxiomII in H13 as [].
    rewrite H15 in H16. pose proof (MKT101 (f2[z])).
    contradiction. elim (@ MKT16 z); auto. }
  assert (Φ ∈ F0).
  { rewrite <-H11. apply AxiomII in H9 as [H9[[H13[H14[H15[]]]]]].
    apply H16; auto. }
  apply AxiomII in H9 as [H9[[H14[]]]]; auto.
Qed.

(* *N'上定义的 N'_Ord关系 具有可传递性  *)
Property N'_Ord_Trans : ∀ u v w, u ∈ N' -> v ∈ N' -> w ∈ N'
  -> u < v -> v < w -> u < w.
Proof.
  destruct NPAUF as [H _]. intros.
  apply AxiomII in H0 as [H0[f[H5[H6[]]]]].
  apply AxiomII in H1 as [H1[f1[H9[H10[]]]]].
  apply AxiomII in H2 as [H2[f2[H13[H14[]]]]].
  apply AxiomII' in H3 as []. apply AxiomII' in H4 as [].
  apply AxiomII'; split. apply MKT49a; auto. intros.
  assert (\{ λ w, f0[w] ∈ f1[w] \} ∈ F0). { apply H17; auto. }
  assert (\{ λ w, f1[w] ∈ g[w] \} ∈ F0). { apply H18; auto. }
  assert (\{ λ w, f0[w] ∈ f1[w] \} ∩ \{ λ w, f1[w] ∈ g[w] \}
    ⊂ \{ λ w, f0[w] ∈ g[w] \}).
  { unfold Included; intros. apply MKT4' in H29 as [].
    apply AxiomII in H29 as []. apply AxiomII in H30 as [].
    apply AxiomII; split; auto. destruct (classic (z ∈ ω)).
    - rewrite <-H22 in H33. apply Property_Value,Property_ran
      in H33; auto. apply H24 in H33. apply AxiomII in H33 as
      [H33[[]]]. apply H35 in H32. apply H32; auto.
    - rewrite <-H21 in H33. apply MKT69a in H33.
      rewrite H33 in H31. elim MKT39; eauto. }
  destruct H as [_[H _]]. apply AxiomII in H as [H[[H30[H31[H32[]]]]]].
  apply (H34 (\{ λ w, f0[w] ∈ f1[w] \} ∩ \{ λ w, f1[w] ∈ g[w] \}));
  repeat split; auto. unfold Included; intros.
  apply AxiomII in H36 as []. destruct (classic (z ∈ ω)); auto.
  rewrite <-H21 in H38. apply MKT69a in H38. rewrite H38 in H37.
  elim MKT39; eauto.
Qed.


(* *N上定义的 N'_Ord关系 满足三分律, 也就是 N'_Ord 连接*N. *)
Property N'_Ord_Tri : Connect N'_Ord N'.
Proof.
  destruct NPAUF as [H _]. intros. unfold Connect; intros.
  apply AxiomII in H0 as [H0[f[H2[H3[]]]]].
  apply AxiomII in H1 as [H1[f1[H6[H7[]]]]].
  assert (ω = \{ λ w, f[w] ∈ f1[w] \} ∪ \{ λ w, f1[w] ∈ f[w] \}
    ∪ \{ λ w, w ∈ ω /\ f[w] = f1[w] \}).
  { apply AxiomI; split; intros.
    - pose proof H10. pose proof H11.
      rewrite <-H3 in H10; rewrite <-H7 in H11.
      apply Property_Value,Property_ran,H4 in H10; auto.
      apply Property_Value,Property_ran,H8 in H11; auto.
      assert (Ordinal f[z] /\ Ordinal f1[z]) as [].
      { apply AxiomII in H10 as [H10[]].
        apply AxiomII in H11 as [H11[]]. auto. }
      apply (@ MKT110 _ f1[z]) in H13 as [H13|[|]]; auto; clear H14.
      + apply MKT4; left. apply AxiomII; split; eauto.
      + apply MKT4; right. apply MKT4; left.
        apply AxiomII; split; eauto.
      + apply MKT4; right. apply MKT4; right.
        apply AxiomII; split; eauto.
    - apply MKT4 in H10 as []. apply AxiomII in H10 as [].
      apply NNPP; intro. rewrite <-H3 in H12. apply MKT69a in H12.
      rewrite H12 in H11. elim MKT39; eauto.
      apply MKT4 in H10 as []. apply AxiomII in H10 as [].
      apply NNPP; intro. rewrite <-H7 in H12. apply MKT69a in H12.
      rewrite H12 in H11. elim MKT39; eauto.
      apply AxiomII in H10; tauto. }
  pose proof H as Ha. destruct H as [_[]]. apply AxiomII in H
  as [H[[H12[H13[]]]]]. rewrite H10 in H14. destruct Ha as [_[]]. clear H18.
  apply AxiomII in H17 as []. apply (FT1 _ ω) in H14 as []; auto.
  - left. apply AxiomII'; split. apply MKT49a; auto.
    intros. rewrite H5 in H25. apply H11 in H25; auto.
    rewrite H9 in H26. apply H11 in H26; auto.
    destruct H25 as [H25[H27[H28[H29[H30[H31[]]]]]]].
    destruct H26 as [H26[H34[H35[H36[H37[H38[]]]]]]].
    set (A := \{ λ u, u ∈ ω /\ f[u] = f0[u] \}
      ∩ \{ λ u, u ∈ ω /\ f1[u] = g[u] \}
      ∩ \{ λ w, f[w] ∈ f1[w] \}).
    assert (A ⊂ \{ λ w, f0[w] ∈ g[w] \}).
    { unfold Included; intros. apply MKT4' in H41 as [].
      apply MKT4' in H42 as []. apply AxiomII in H41 as [H41[]].
      apply AxiomII in H42 as [H42[]]. apply AxiomII in H43 as [].
      apply AxiomII; split; auto. rewrite H45,H47 in H48; auto. }
    destruct H15. apply (H42 A); [ | |unfold A]; auto.
    unfold Included; intros. apply AxiomII in H43 as [].
    apply NNPP; intro. rewrite <-H29 in H45.
    apply MKT69a in H45. rewrite H45 in H44. elim MKT39; eauto.
  - apply (FT1 _ ω) in H14 as []; auto.
    + right; left. apply AxiomII'; split. apply MKT49a; auto.
      intros. rewrite H5 in H26; rewrite H9 in H25.
      apply H11 in H25; auto.
      destruct H25 as [H25[H27[H28[H29[H30[H31[]]]]]]].
      apply H11 in H26; auto.
      destruct H26 as [H26[H34[H35[H36[H37[H38[]]]]]]].
      set (A := \{ λ u, u ∈ ω /\ f1[u] = f0[u] \}
        ∩ \{ λ u, u ∈ ω /\ f[u] = g[u] \}
        ∩ \{ λ w, f1[w] ∈ f[w] \}).
      assert (A ⊂ \{ λ w, f0[w] ∈ g[w] \}).
      { unfold Included; intros. apply MKT4' in H41 as [].
        apply MKT4' in H42 as []. apply AxiomII in H41 as [H41[]].
        apply AxiomII in H42 as [H42[]]. apply AxiomII in H43 as [].
        apply AxiomII; split; auto. rewrite H45,H47 in H48; auto. }
      destruct H15. apply (H42 A); [ | |unfold A]; auto.
      unfold Included; intros. apply AxiomII in H43 as [].
      apply NNPP; intro. rewrite <-H29 in H45.
      apply MKT69a in H45. rewrite H45 in H44. elim MKT39; eauto.
    + repeat right. rewrite H5,H9. apply (FT8 _ _ ω). destruct H2,H6.
      repeat split; auto.
Qed.

Open Scope ωfun_scope.

(* 定义 *N中的加法运算
       此定义仅用于算数模型*N, 即 定义中的u v需是*N中的元,F0需是某个非主算数超滤.*)
Definition N'_Plus u v := ∩(\{ λ a, ∀ f g, Function f
  -> Function g -> dom(f) = ω -> dom(g) = ω -> ran(f) ⊂ ω
  -> ran(g) ⊂ ω -> u = f〈F0〉 -> v = g〈F0〉-> a = (f + g)〈F0〉 \}).

Notation "u + v" := (N'_Plus u v) : n'_scope.

(* 此引理为证明 *N中加法运算的合理性 作准备
   [注: 这里需要用到算数超滤的附加性质]    *)
Lemma N'_Plus_Reasonable_Lemma : ∀ f g g1, Function f
  -> Function g -> Function g1 -> dom(f) = ω -> dom(g) = ω
  -> dom(g1) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω -> ran(g1) ⊂ ω
  -> g <> g1 -> g〈F0〉 = g1〈F0〉-> (f + g)〈F0〉 = (f + g1)〈F0〉.
Proof.
  intros. destruct NPAUF as [H10 _]. apply (FT8 _ _ ω). unfold AlmostEqual.
  pose proof H0 as Ha; pose proof H1 as Hb.
  apply (ωFun_Plus_P1 f g) in H0 as [H0[]]; auto.
  apply (ωFun_Plus_P1 f g1) in H1 as [H1[]]; auto.
  destruct H0,H1. repeat split; auto.
  assert (\{ λ u, u ∈ ω /\ g[u] = g1[u] \}
    = \{ λ u, u ∈ ω /\ (f + g)[u] = (f + g1)[u] \}).
  { assert (∀ z, z ∈ ω -> f[z] ∈ ω /\ g[z] ∈ ω /\ g1[z] ∈ ω).
    { intros. repeat split;
      [rewrite <-H2 in H17|rewrite <-H3 in H17|rewrite <-H4 in H17];
      apply Property_Value,Property_ran in H17; auto. }
    apply AxiomI; split; intros. apply AxiomII in H18 as [H18[]].
    apply AxiomII; repeat split; auto. rewrite ωFun_Plus_P2,ωFun_Plus_P2; auto.
    apply H17 in H19 as [H27[]]. apply Plus_Cancellation; auto.
    apply AxiomII in H18 as [H18[]]. apply AxiomII; repeat split; auto.
    rewrite ωFun_Plus_P2,ωFun_Plus_P2 in H20; auto.
    apply H17 in H19 as [H19[]]. apply Plus_Cancellation in H20; auto. }
  rewrite <-H17; auto. destruct H10 as [_[]]. apply H18 in H9; auto.
  destruct H9; tauto.
Qed.

(* 验证 *N中定义的加法运算的合理性: 对于任意*N中的u和v, *N上的加法定义中的{}中只有
                              一个元素, 并且该唯一的元素也是一个算术超滤.
                              于是u与v的相加结果形如 ∩[a] 是唯一的.  *)
Property N'_Plus_Reasonable : ∀ u v, u ∈ N' -> v ∈ N'
  -> ∃ a, Arithmetical_ultraFilter a ω
    /\ [a] = \{ λ a, ∀ f g, Function f -> Function g -> dom(f) = ω
    -> dom(g) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω -> u = f〈F0〉
    -> v = g〈F0〉 -> a = (f + g)〈F0〉 \}.
Proof.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[h1[H2[H3[]]]]].
  apply AxiomII in H1 as [H1[h2[H6[H7[]]]]]. exists ((h1 + h2)〈F0〉).
  assert (Arithmetical_ultraFilter (h1 + h2)〈F0〉 ω).
  { apply (ωFun_Plus_P1 h1 h2) in H2 as [H2[]]; auto. apply (FT10 F0 _ ω ω) ; auto.
    New MKT138. eauto. unfold Finite; intro. rewrite Inf_P1 in H12.
    elim (@ MKT101 ω); auto. }
  split; auto. apply AxiomI; split; intros.
  - apply MKT41 in H11. apply AxiomII; split; intros.
    destruct H10 as [_[]]. rewrite H11; eauto. rewrite H11.
    assert ((h1 + h2)〈F0〉 = (h1 + g)〈F0〉).
    { destruct (classic (h2 = g)). rewrite H20; auto. apply
      N'_Plus_Reasonable_Lemma; auto. rewrite H9 in H19; auto. }
    assert ((h1 + g)〈F0〉 = (f + g)〈F0〉).
    { destruct (classic (h1 = f)). rewrite H21; auto.
      assert (∀ z, z ∈ ω -> f[z] ∈ ω /\ g[z] ∈ ω /\ h1[z] ∈ ω).
      { intros. repeat split. rewrite <-H14 in H22.
        apply Property_Value,Property_ran in H22; auto.
        rewrite <-H15 in H22. apply Property_Value,
        Property_ran in H22; auto. rewrite <-H3 in H22.
        apply Property_Value,Property_ran in H22; auto. }
      assert (f + g = g + f).
      { apply AxiomI; split; intros; apply AxiomII in H23
        as [H23[x[y[H24[]]]]]; apply AxiomII; split; auto;
        exists x,y; repeat split; auto; apply H22 in H25
        as [H25[]]; rewrite Plus_Commutation; auto. }
      assert (h1 + g = g + h1).
      { apply AxiomI; split; intros; apply AxiomII in H24
        as [H24[x[y[H25[]]]]]; apply AxiomII; split; auto;
        exists x,y; repeat split; auto; apply H22 in H26
        as [H26[]]; rewrite Plus_Commutation; auto. }
      rewrite H23,H24. apply N'_Plus_Reasonable_Lemma; auto.
      rewrite H5 in H18; auto. }
    rewrite H20,H21; auto. destruct H10 as [_[]]; eauto.
  - apply AxiomII in H11 as []. destruct H10 as [_[]]. apply MKT41; eauto.
Qed.

(* *N上的加法满足 f〈F0〉 + g〈F0〉 = (f+g)〈F0〉 *)
Property N'_Plus_Instantiate : ∀ f g, Function f -> Function g
  -> dom(f) = ω -> dom(g) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω
  -> (f〈F0〉 + g〈F0〉)%n'= (f + g)〈F0〉.
Proof.
  destruct NPAUF as [H _]. intros.
  assert (Arithmetical_ultraFilter ((f + g)〈F0〉) ω).
  { apply (ωFun_Plus_P1 f g) in H0 as [H0[]]; auto.
    apply (FT10 F0 _ ω ω); auto. New MKT138; eauto. intro.
    unfold Finite in H8. rewrite Inf_P1 in H8. elim (@ MKT101 ω); auto. }
  assert ([(f + g)〈F0〉] = \{ λ a, ∀ f0 g4, Function f0
    -> Function g4 -> dom( f0) = ω -> dom(g4) = ω -> ran(f0) ⊂ ω
    -> ran(g4) ⊂ ω -> f〈F0〉 = f0〈F0〉 -> g〈F0〉 = g4〈F0〉
    -> a = (f0 + g4)〈F0〉 \}).
  { apply AxiomI; split; intros.
    - apply MKT41 in H7. apply AxiomII; split; intros.
      destruct H6 as [_[]]. rewrite <-H7 in H6. eauto. rewrite H7.
      assert ((f + g)〈F0〉 = (f + g4)〈F0〉).
      { destruct (classic (g = g4)). rewrite H16; auto.
        apply N'_Plus_Reasonable_Lemma; auto. }
      assert ((f + g4)〈F0〉 = (f0 + g4)〈F0〉).
      { destruct (classic (f = f0)). rewrite H17; auto.
      assert (∀ z, z ∈ ω -> f[z] ∈ ω /\ f0[z] ∈ ω /\ g4[z] ∈ ω).
      { intros. repeat split. rewrite <-H2 in H18.
        apply Property_Value,Property_ran in H18; auto.
        rewrite <-H10 in H18. apply Property_Value,
        Property_ran in H18; auto. rewrite <-H11 in H18.
        apply Property_Value,Property_ran in H18; auto. }
      assert (f + g4 = g4 + f).
      { apply AxiomI; split; intros; apply AxiomII in H19
        as [H19[x[y[H20[]]]]]; apply AxiomII; split; auto;
        exists x,y; repeat split; auto; apply H18 in H21
        as [H21[]]; rewrite Plus_Commutation; auto. }
      assert (f0 + g4 = g4 + f0).
      { apply AxiomI; split; intros; apply AxiomII in H20
        as [H20[x[y[H21[]]]]]; apply AxiomII; split; auto;
        exists x,y; repeat split; auto; apply H18 in H22
        as [H22[]]; rewrite Plus_Commutation; auto. }
      rewrite H19,H20. apply N'_Plus_Reasonable_Lemma; auto. }
      rewrite H16,H17; auto. destruct H6 as [_[]]; eauto.
    - apply AxiomII in H7 as []. destruct H6 as [_[]]. apply MKT41; eauto. }
  unfold N'_Plus. rewrite <-H7. apply MKT44. destruct H6 as [_[]]; eauto.
Qed.

(* 进一步验证 *N上定义的加法对*N封闭*)
Property N'_Plus_in_N' : ∀ u v, u ∈ N' -> v ∈ N' -> (u + v)%n' ∈ N'.
Proof.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[f[H2[H3[]]]]].
  apply AxiomII in H1 as [H1[g[H6[H7[]]]]]. rewrite H5,H9.
  rewrite N'_Plus_Instantiate; auto.
  apply (ωFun_Plus_P1 f g) in H2 as [H2[]]; auto.
  assert (Arithmetical_ultraFilter ((f + g)〈F0〉) ω).
  { apply (FT10 F0 _ ω ω); auto. New MKT138; eauto. unfold Finite; intro.
    rewrite Inf_P1 in H12. elim (@ MKT101 ω); auto. }
  destruct H12 as [_[]]. apply AxiomII; split; eauto.
Qed.

(* 定义 *N中的乘法运算
       此定义仅用于算数模型*N, 即 定义中的u v需是*N中的元, F0需是某个非主算数超滤.*)
Definition N'_Mult u v := ∩(\{ λ a, ∀ f g, Function f
  -> Function g -> dom(f) = ω -> dom(g) = ω -> ran(f) ⊂ ω
  -> ran(g) ⊂ ω -> u = f〈F0〉 -> v = g〈F0〉 -> a = (f · g)〈F0〉 \}).

Notation "u · v" := (N'_Mult u v) : n'_scope.

(* 此引理为证明 *N中乘法运算的合理性 作准备
   [注: 这里需要用到算数超滤的附加性质]*)
Lemma N'_Mult_Reasonable_Lemma : ∀ f g g1, Function f
  -> Function g -> Function g1 -> dom(f) = ω -> dom(g) = ω
  -> dom(g1) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω -> ran(g1) ⊂ ω
  -> g <> g1 -> g〈F0〉 = g1〈F0〉 -> (f · g)〈F0〉 = (f · g1)〈F0〉.
Proof.
  intros. destruct NPAUF as [H10 _]. apply (FT8 _ _ ω). unfold AlmostEqual.
  pose proof H0 as Ha; pose proof H1 as Hb.
  apply (ωFun_Mult_P1 f g) in H0 as [H0[]]; auto.
  apply (ωFun_Mult_P1 f g1) in H1 as [H1[]]; auto.
  destruct H0,H1. repeat split; auto.
  assert (\{ λ u, u ∈ ω /\ g[u] = g1[u] \}
    ⊂ \{ λ u, u ∈ ω /\ (f · g)[u] = (f · g1)[u] \}).
  { assert (∀ z, z ∈ ω -> f[z] ∈ ω /\ g[z] ∈ ω /\ g1[z] ∈ ω).
    { intros. repeat split;
      [rewrite <-H2 in H17|rewrite <-H3 in H17|rewrite <-H4 in H17];
      apply Property_Value,Property_ran in H17; auto. }
    red; intros. apply AxiomII in H18 as [H18[]].
    apply AxiomII; repeat split; auto. rewrite ωFun_Mult_P2,ωFun_Mult_P2; auto.
    apply H17 in H19 as [H27[]]. rewrite H20; auto. }
  destruct H10 as [_[]]. apply AxiomII in H10 as [_[[_[_[_[]]]]_]].
  apply H19 in H17; auto. red; intros. apply AxiomII in H20; tauto.
  apply H18 in H9 as []; auto. tauto.
Qed.

(* 验证 *N中定义的乘法运算的合理性: 对于任意*N中的u和v, *N上的乘法定义中的{}中只有
                              一个元素, 并且该唯一的元素也是一个算术超滤.
                              于是u与v的相乘结果形如 ∩[a] 是唯一的.   *)
Property N'_Mult_Reasonable : ∀ u v, u ∈ N' -> v ∈ N'
  -> ∃ a, Arithmetical_ultraFilter a ω
    /\ [a] = \{ λ a, ∀ f g, Function f -> Function g -> dom(f) = ω
    -> dom(g) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω -> u = f〈F0〉
    -> v = g〈F0〉 -> a = (f · g)〈F0〉 \}.
Proof.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[h1[H2[H3[]]]]].
  apply AxiomII in H1 as [H1[h2[H6[H7[]]]]]. exists ((h1 · h2)〈F0〉).
  assert (Arithmetical_ultraFilter (h1 · h2)〈F0〉 ω).
  { apply (ωFun_Mult_P1 h1 h2) in H2 as [H2[]]; auto.
    apply (FT10 F0 _ ω ω); auto. New MKT138; eauto. unfold Finite; intro.
    rewrite Inf_P1 in H12. elim (@ MKT101 ω); auto. }
  split; auto. apply AxiomI; split; intros.
  - apply MKT41 in H11. apply AxiomII; split; intros.
    destruct H10 as [_[]]. rewrite H11; eauto. rewrite H11.
    assert ((h1 · h2)〈F0〉 = (h1 · g)〈F0〉).
    { destruct (classic (h2 = g)). rewrite H20; auto. apply
      N'_Mult_Reasonable_Lemma; auto. rewrite H9 in H19; auto. }
    assert ((h1 · g)〈F0〉 = (f · g)〈F0〉).
    { destruct (classic (h1 = f)). rewrite H21; auto.
      assert (∀ z, z ∈ ω -> f[z] ∈ ω /\ g[z] ∈ ω /\ h1[z] ∈ ω).
      { intros. repeat split. rewrite <-H14 in H22.
        apply Property_Value,Property_ran in H22; auto.
        rewrite <-H15 in H22. apply Property_Value,
        Property_ran in H22; auto. rewrite <-H3 in H22.
        apply Property_Value,Property_ran in H22; auto. }
      assert (f · g = g · f).
      { apply AxiomI; split; intros; apply AxiomII in H23
        as [H23[x[y[H24[]]]]]; apply AxiomII; split; auto;
        exists x,y; repeat split; auto; apply H22 in H25
        as [H25[]]; rewrite Mult_Commutation; auto. }
      assert (h1 · g = g · h1).
      { apply AxiomI; split; intros; apply AxiomII in H24
        as [H24[x[y[H25[]]]]]; apply AxiomII; split; auto;
        exists x,y; repeat split; auto; apply H22 in H26
        as [H26[]]; rewrite Mult_Commutation; auto. }
      rewrite H23,H24. apply N'_Mult_Reasonable_Lemma; auto.
      rewrite H5 in H18; auto. }
    rewrite H20,H21; auto. destruct H10 as [_[]]; eauto.
  - apply AxiomII in H11 as []. destruct H10 as [_[]]. apply MKT41; eauto.
Qed.

(* *N上的乘法满足 f〈F0〉 * g〈F0〉 = (f*g)〈F0〉 *)
Property N'_Mult_Instantiate : ∀ f g, Function f -> Function g
  -> dom(f) = ω -> dom(g) = ω -> ran(f) ⊂ ω -> ran(g) ⊂ ω
  -> (f〈F0〉 · g〈F0〉)%n' = (f · g)〈F0〉.
Proof.
  destruct NPAUF as [H _]. intros.
  assert (Arithmetical_ultraFilter ((f · g)〈F0〉) ω).
  { apply (ωFun_Mult_P1 f g) in H0 as [H0[]]; auto. apply (FT10 F0 _ ω ω); auto.
    New MKT138; eauto. unfold Finite; intro. rewrite Inf_P1 in H8.
    elim (@ MKT101 ω); auto. }
  assert ([(f · g)〈F0〉] = \{ λ a, ∀ f0 g4, Function f0
    -> Function g4 -> dom(f0) = ω -> dom(g4) = ω -> ran(f0) ⊂ ω
    -> ran(g4) ⊂ ω -> f〈F0〉 = f0〈F0〉 -> g〈F0〉 = g4〈F0〉
    -> a = (f0 · g4)〈F0〉 \}).
  { apply AxiomI; split; intros.
    - apply MKT41 in H7. apply AxiomII; split; intros.
      destruct H6 as [_[]]. rewrite <-H7 in H6. eauto. rewrite H7.
      assert ((f · g)〈F0〉 = (f · g4)〈F0〉).
      { destruct (classic (g = g4)). rewrite H16; auto.
        apply N'_Mult_Reasonable_Lemma; auto. }
      assert ((f · g4)〈F0〉 = (f0 · g4)〈F0〉).
      { destruct (classic (f = f0)). rewrite H17; auto.
        assert (∀ z, z ∈ ω -> f[z] ∈ ω /\ f0[z] ∈ ω /\ g4[z] ∈ ω).
        { intros. repeat split; [rewrite <-H2 in H18|
          rewrite <-H10 in H18|rewrite <-H11 in H18];
          apply Property_Value,Property_ran in H18; auto. }
        assert (f · g4 = g4 · f).
        { apply AxiomI; split; intros; apply AxiomII in H19
          as [H19[x[y[H20[]]]]]; apply AxiomII; split; auto;
          exists x,y; repeat split; auto; apply H18 in H21
          as [H21[]]; rewrite Mult_Commutation; auto. }
        assert (f0 · g4 = g4 · f0).
        { apply AxiomI; split; intros; apply AxiomII in H20
          as [H20[x[y[H21[]]]]]; apply AxiomII; split; auto;
          exists x,y; repeat split; auto; apply H18 in H22
          as [H22[]]; rewrite Mult_Commutation; auto. }
        rewrite H19,H20. apply N'_Mult_Reasonable_Lemma; auto. }
      rewrite H16,H17; auto. destruct H6 as [_[]]; eauto.
    - apply AxiomII in H7 as []. destruct H6 as [_[]]. apply MKT41; eauto. }
  unfold N'_Mult. rewrite <-H7. apply MKT44. destruct H6 as [_[]]; eauto.
Qed.

(* 进一步验证 *N上定义的乘法对*N封闭 *)
Property N'_Mult_in_N' : ∀ u v, u ∈ N' -> v ∈ N' -> (u · v)%n' ∈ N'.
Proof.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[f[H2[H3[]]]]].
  apply AxiomII in H1 as [H1[g[H6[H7[]]]]]. rewrite H5,H9.
  rewrite N'_Mult_Instantiate; auto.
  apply (ωFun_Mult_P1 f g) in H2 as [H2[]]; auto.
  assert (Arithmetical_ultraFilter ((f · g)〈F0〉) ω).
  { apply (FT10 F0 _ ω ω); auto. New MKT138; eauto. unfold Finite; intro.
    rewrite Inf_P1 in H12. elim (@ MKT101 ω); auto. }
  destruct H12 as [_[]]. apply AxiomII; split; eauto.
Qed.

Open Scope n'_scope.

(* 验证 *N中关于零元的性质:
       u + F0 = u ; u * F0 = F0 ; 无零因子*)
Property N'_Plus_Property : ∀ u, u ∈ N' -> u + (F 0) = u.
Proof.
  destruct NPAUF as [H _]. intros.
  apply AxiomII in H0 as [H0[f[H1[H2[]]]]]. rewrite H4.
  assert ((Const 0)〈F0〉 = F 0).
  { apply F_Const_Fa; destruct H,MKT135; auto. }
  rewrite <-H5. assert (Ensemble 0) by (New in_ω_0; eauto).
  apply (Const_is_Function ω) in H6 as [H6[]].
  rewrite N'_Plus_Instantiate; auto.
  assert (∀ z, z ∈ ω -> f[z] ∈ ω ).
  { intros. rewrite <-H2 in H9.
    apply Property_Value,Property_ran in H9; auto. }
  assert (∀ z, z ∈ ω -> f[z] + (Const 0)[z] = f[z])%ω.
  { intros. assert ((Const 0)[z] = 0).
    { rewrite <-H7 in H10. apply Property_Value,Property_ran
      in H10; auto. rewrite H8 in H10. destruct MKT135.
      apply MKT41 in H10; eauto. }
    rewrite H11,Plus_Property1_a; auto. }
  assert ((f + (Const 0))%ωfun = f).
  { apply AxiomI; split; intros. apply AxiomII in H11 as
    [H11[x[y[H12[]]]]]. rewrite H10 in H14; auto.
    rewrite <-H2 in H13. apply Property_Value in H13; auto.
    rewrite H12,H14; auto. apply AxiomII; split; eauto.
    pose proof H1. apply MKT70 in H12. pose proof H11.
    rewrite H12 in H11. apply AxiomII in H11 as [H11[x[y[]]]].
    exists x,y. rewrite H14 in H13. split; auto. apply
    Property_dom in H13. rewrite H2 in H13. rewrite H10; auto. }
  rewrite H11; auto. unfold Included; intros. rewrite H8 in H9.
  destruct MKT135. apply MKT41 in H9; eauto. rewrite H9; auto.
  intro. New in_ω_0. rewrite H7 in H8. elim (@ MKT101 0); auto.
Qed.

(* 验证 *N中的加法满足交换律. *)
Property N'_Plus_Commutation : ∀ u v, u ∈ N' -> v ∈ N' -> u + v = v + u.
Proof.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[f[H2[H3[]]]]].
  apply AxiomII in H1 as [H1[g[H6[H7[]]]]].
  assert (∀ z, z ∈ ω -> (f[z] ∈ ω /\ g[z] ∈ ω)).
  { intros. split; [rewrite <-H3 in H10|rewrite <-H7 in H10];
    apply Property_Value,Property_ran in H10; auto. }
  rewrite H5,H9,N'_Plus_Instantiate,N'_Plus_Instantiate; auto.
  assert (f + g = g + f)%ωfun.
  { apply AxiomI; split; intros; apply AxiomII in H11
    as [H11[x[y[H12[]]]]]; apply AxiomII; split; eauto;
    exists x,y; repeat split; auto; apply H10 in H13 as
    []; rewrite Plus_Commutation; auto. }
  rewrite H11; auto.
Qed.

(* 验证 *N中的加法满足结合律 *)
Property N'_Plus_Association : ∀ u v w, u ∈ N' -> v ∈ N' -> w ∈ N'
  -> (u + v) + w = u + (v + w).
Proof.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[f1[H3[H4[]]]]].
  apply AxiomII in H1 as [H1[f2[H7[H8[]]]]].
  apply AxiomII in H2 as [H2[f3[H11[H12[]]]]].
  assert (∀ z, z ∈ ω -> f1[z] ∈ ω /\ f2[z] ∈ ω /\ f3[z] ∈ ω).
  { intros. repeat split;
    [rewrite <-H4 in H15|rewrite <-H8 in H15|rewrite <-H12 in H15];
    apply Property_Value,Property_ran in H15; auto. }
  pose proof H3; pose proof H11.
  apply (ωFun_Plus_P1 f1 f2) in H3 as [H3[]]; auto.
  apply (ωFun_Plus_P1 f2 f3) in H11 as [H11[]]; auto.
  rewrite H6,H10,H14,N'_Plus_Instantiate,N'_Plus_Instantiate,
  N'_Plus_Instantiate,N'_Plus_Instantiate; auto.
  assert ((f1 + f2) + f3 = f1 + (f2 + f3))%ωfun.
  { apply AxiomI; split; intros; apply AxiomII in H22 as
    [H22[x[y[H23[]]]]]; apply AxiomII; split; auto; exists x,y;
    repeat split; auto; rewrite ωFun_Plus_P2; auto;
    rewrite ωFun_Plus_P2 in H25; auto; apply H15
    in H24 as [H24[]]; try rewrite <-Plus_Association; auto.
    rewrite Plus_Association; auto. }
  rewrite H22; auto.
Qed.

(* 验证 *N中的加法满足消去律 *)
Property N'_Plus_Cancellation : ∀ u v w, u ∈ N' -> v ∈ N' -> w ∈ N'
  -> u + v = u + w -> v = w.
Proof.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[f1[H4[H5[]]]]].
  apply AxiomII in H1 as [H1[f2[H8[H9[]]]]].
  apply AxiomII in H2 as [H2[f3[H12[H13[]]]]].
  assert (∀ z, z ∈ ω -> f1[z] ∈ ω /\ f2[z] ∈ ω /\ f3[z] ∈ ω).
  { intros. repeat split;
    [rewrite <-H5 in H16|rewrite <-H9 in H16|rewrite <-H13 in H16];
    apply Property_Value, Property_ran in H16; auto. }
  rewrite H7,H11,H15,N'_Plus_Instantiate,N'_Plus_Instantiate in H3;
  auto. pose proof H4; pose proof H4.
  apply (ωFun_Plus_P1 f1 f2) in H17 as [H17[]]; auto.
  apply (ωFun_Plus_P1 f1 f3) in H18 as [H18[]]; auto.
  destruct H. apply H23 in H3; auto. clear H17 H18 H19 H20 H21 H22.
  destruct H3 as [H3[H17[H18[H19[H20[H21[]]]]]]].
  assert (\{ λ u, u ∈ ω /\ f2[u] = f3[u] \} ∈ F0).
  { apply AxiomII in H22 as [H22[[H25[H26[H27[]]]]]].
    apply (H29 (\{ λ u, u ∈ ω /\ (f1 + f2)%ωfun[u] = (f1 + f3)%ωfun[u] \}));
    repeat split; auto. unfold Included; intros. apply AxiomII in H31 as [H31[]].
    rewrite ωFun_Plus_P2,ωFun_Plus_P2 in H33; auto. pose proof H32.
    apply Plus_Cancellation in H33; apply H16 in H32; try tauto.
    apply AxiomII; auto. unfold Included; intros. apply AxiomII in H31; tauto. }
  assert (AlmostEqual f2 f3 ω ω F0).
  { destruct H8,H12. repeat split; auto. }
  apply (FT8 _ _ ω) in H26. rewrite H11,H15; auto.
Qed.

(* *N上定义的 N'_Ord关系 满足加法保序 (需注意和 消去律 的区别)
                     (证明中需要用到滤子中的 大集性质 和 对交封闭
                      以及 算数超滤满足命题六的反向)*)
Property N'_Plus_PrOrder : ∀ u v w, u ∈ N' -> v ∈ N' -> w ∈ N'
  -> u < v <-> (w + u) < (w + v).
Proof.
  destruct NPAUF as [H _]. split; intros.
  - pose proof H0 as Ha; pose proof H1 as Hb; pose proof H2 as Hc.
    apply AxiomII in H0 as [H0[f1[H4[H5[]]]]].
    apply AxiomII in H1 as [H1[f2[H8[H9[]]]]].
    apply AxiomII in H2 as [H2[f3[H12[H13[]]]]].
    apply AxiomII' in H3 as []. pose proof H4.
    apply (H16 f1 f2) in H17; auto.
    assert ((w + u) ∈ N'). { apply N'_Plus_in_N'; auto. }
    assert ((w + v) ∈ N'). { apply N'_Plus_in_N'; auto. }
    apply AxiomII'; split. apply MKT49a; eauto.
    intros. pose proof H4; pose proof H8.
    apply (ωFun_Plus_P1 f3 f1) in H28 as [H28[]]; auto.
    apply (ωFun_Plus_P1 f3 f2) in H29 as [H29[]]; auto.
    rewrite H7,H15,N'_Plus_Instantiate in H26; auto.
    rewrite H11,H15,N'_Plus_Instantiate in H27; auto.
    destruct H. apply H34 in H26; apply H34 in H27; auto.
    destruct H26 as [H26[H35[H36[H37[H38[H39[]]]]]]].
    destruct H27 as [H27[H42[H43[H44[H45[H46[]]]]]]].
    assert (\{ λ w, f1[w] ∈ f2[w] \}
       ⊂ \{ λ w, (f3 + f1)%ωfun[w] ∈ (f3 + f2)%ωfun[w] \}).
    { unfold Included; intros. apply AxiomII in H49 as [].
      apply AxiomII; split; auto. rewrite ωFun_Plus_P2,ωFun_Plus_P2; auto.
      assert (z ∈ ω).
      { apply NNPP; intro. rewrite <-H5 in H51. apply MKT69a in H51.
        rewrite H51 in H50. elim MKT39; eauto. }
      assert (∀ f, Function f -> dom( f) = ω -> ran( f) ⊂ ω -> f[z] ∈ ω).
      { intros. rewrite <-H53 in H51.
        apply Property_Value,Property_ran in H51; auto. }
      apply Plus_PrOrder; auto. }
    apply AxiomII in H40 as [H40[[H50[H51[H52[]]]]]].
    assert (\{ λ w, (f3 + f1)%ωfun[w] ∈ (f3 + f2)%ωfun[w] \} ∈ F0).
    { apply (H54 (\{ λ w, f1[w] ∈ f2[w] \})); repeat split; auto.
      unfold Included; intros. apply AxiomII in H56 as [].
      apply NNPP; intro. rewrite <-H30 in H58. apply MKT69a in H58.
      rewrite H58 in H57. elim MKT39; eauto. }
    assert ((\{ λ u, u ∈ ω /\ (f3 + f1)%ωfun[u] = f[u] \}
      ∩ \{ λ u, u ∈ ω /\ (f3 + f2)%ωfun[u] = g[u] \}
      ∩ \{ λ w, (f3 + f1)%ωfun[w] ∈ (f3 + f2)%ωfun[w] \})
       ⊂ \{ λ w, f[w] ∈ g[w] \}).
    { unfold Included; intros. apply MKT4' in H57 as [].
      apply MKT4' in H58 as []. apply AxiomII in H57 as [H57[]].
      apply AxiomII in H58 as [H58[]]. apply AxiomII in H59 as [].
      rewrite H61,H63 in H64. apply AxiomII; auto. }
    apply (H54 (\{ λ u, u ∈ ω /\ (f3 + f1)%ωfun[u] = f[u] \}
      ∩ \{ λ u, u ∈ ω /\ (f3 + f2)%ωfun[u] = g[u] \}
      ∩ \{ λ w, (f3 + f1)%ωfun[w] ∈ (f3 + f2)%ωfun[w] \}));
    repeat split; auto. unfold Included; intros. apply AxiomII
    in H58 as []. apply NNPP; intro. rewrite <-H22 in H60.
    apply MKT69a in H60. rewrite H60 in H59. elim MKT39; eauto.
  - apply AxiomII in H0 as [H0[f1[H4[H5[]]]]].
    apply AxiomII in H1 as [H1[f2[H8[H9[]]]]].
    apply AxiomII in H2 as [H2[f3[H12[H13[]]]]].
    rewrite H7,H11,H15 in *. clear dependent u. clear dependent v.
    clear dependent w. rewrite N'_Plus_Instantiate,N'_Plus_Instantiate
    in H3; auto. pose proof H12; pose proof H12.
    apply (ωFun_Plus_P1 f3 f1) in H7 as [H7[]]; auto.
    apply (ωFun_Plus_P1 f3 f2) in H11 as [H11[]]; auto.
    apply N'_Ord_Instantiate in H3; auto.
    apply N'_Ord_Instantiate; auto.
    set (A := \{ λ w, (f3 + f1)%ωfun[w] ∈ ((f3 + f2)%ωfun[w]) \}).
    destruct H as [_[]]. apply AxiomII in H as [H[[H20[H21[H22[]]]]]].
    apply (H24 A); repeat split; auto; unfold Included; intros.
    apply AxiomII in H26 as []. rewrite ωFun_Plus_P2,
    ωFun_Plus_P2 in H27; auto.
    assert (∀ z, z ∈ ω -> f1[z] ∈ ω /\ f2[z] ∈ ω /\ f3[z] ∈ ω).
    { intros. repeat split. rewrite <-H5 in H28.
      apply Property_Value,Property_ran,H6 in H28; auto.
      rewrite <-H9 in H28.
      apply Property_Value,Property_ran,H10 in H28; auto.
      rewrite <-H13 in H28.
      apply Property_Value,Property_ran,H14 in H28; auto. }
    apply AxiomII; split; auto.
    assert (z ∈ ω).
    { apply NNPP; intro. unfold Plus in H27.
      rewrite <-H5 in H29. apply MKT69a in H29.
      assert (~ f1[z] ∈ dom(PlusFunction f3[z])).
      { intro. rewrite H29 in H30. elim MKT39; eauto. }
      apply MKT69a in H30. rewrite H30 in H27. elim MKT39; eauto. }
    apply H28 in H29 as [H29[]]. apply Plus_PrOrder in H27; auto.
    apply AxiomII in H26 as []. apply NNPP; intro.
    rewrite <-H5 in H28. apply MKT69a in H28.
    rewrite H28 in H27. elim MKT39; eauto.
Qed.

Corollary N'_Plus_PrOrder_Corollary : ∀ u v, u ∈ N' -> v ∈ N'
  -> u < v <-> ∃! w, w ∈ N' /\ (F 0) < w /\ u + w = v.
Proof.
  destruct NPAUF as [H _]. split; intros.
  - apply AxiomII in H0 as [H0[f1[H3[H4[]]]]].
    apply AxiomII in H1 as [H1[f2[H7[H8[]]]]].
    rewrite H6,H10 in H2. apply N'_Ord_Instantiate in H2; auto.
    set (A := \{ λ w, f1[w] ∈ f2[w] \}).
    set (f3 := \{\ λ u v, u ∈ ω
      /\ ((~ u ∈ A /\ u = v) \/ (u ∈ A /\ v = ∩(\{ λ a, a ∈ ω
        /\ 0 ∈ a /\ (f1[u] + a)%ω = f2[u] \}))) \}\).
    assert (Function f3).
    { split; intros.
      - unfold Relation; intros.
        apply AxiomII in H11 as [H11[x[y[]]]]; eauto.
      - apply AxiomII' in H11 as [H11[]].
        apply AxiomII' in H12 as [H12[]].
        destruct H14,H16,H14,H16; try contradiction;
        try rewrite H17,H18; try rewrite H17 in H18; auto. }
    assert (dom(f3) = ω).
    { apply AxiomI; split; intros.
      - apply AxiomII in H12 as [H12[y]].
        apply AxiomII' in H13; tauto.
      - apply AxiomII; split; eauto. destruct (classic (z ∈ A)).
        + exists (∩(\{ λ a, a ∈ ω /\ 0 ∈ a /\ (f1[z] + a)%ω = f2[z] \})).
          apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
          apply AxiomII in H13 as []. apply Plus_PrOrder_Corollary
          in H14 as [k[[H14[]]]].
          assert ([k] = \{ λ a, a ∈ ω /\ 0 ∈ a /\ (f1[z] + a)%ω = f2[z] \}).
          { apply AxiomI; split; intros.
            - apply MKT41 in H18; eauto.
              apply AxiomII; split; rewrite H18; eauto.
            - apply AxiomII in H18 as []. apply MKT41; eauto.
              symmetry. apply H17; auto. }
          rewrite <-H18. destruct (@ MKT44 k); eauto.
          rewrite H19; eauto. rewrite <-H8 in H12.
          apply Property_Value,Property_ran,H9 in H12; auto.
          rewrite <-H4 in H12.
          apply Property_Value,Property_ran,H5 in H12; auto.
        + exists z. apply AxiomII'; repeat split; auto.
          apply MKT49a; eauto. }
    assert (ran(f3) ⊂ ω).
    { unfold Included; intros. apply AxiomII in H13 as [H13[x]].
      apply AxiomII' in H14 as [H14[]]. destruct H16,H16; auto.
      - rewrite <-H17; auto.
      - apply AxiomII in H16 as [].
        apply Plus_PrOrder_Corollary in H18 as [k[[H18[]]]].
        assert ([k] = \{ λ a, a ∈ ω /\ 0 ∈ a /\ (f1[x] + a)%ω = f2[x] \}).
        { apply AxiomI; split; intros.
          - apply MKT41 in H22; eauto.
            apply AxiomII; rewrite H22; split; eauto.
          - apply AxiomII in H22 as []. apply H21 in H23.
            rewrite <-H23. apply MKT41; eauto. }
        rewrite <-H22 in H17. destruct (@ MKT44 k); eauto.
        rewrite H17,H23; auto. rewrite <-H8 in H15.
        apply Property_Value,Property_ran,H9 in H15; auto.
        rewrite <-H4 in H15.
        apply Property_Value,Property_ran,H5 in H15; auto. }
    exists (f3〈F0〉). assert (f3〈F0〉 ∈ N').
    { apply AxiomII; split; eauto. destruct H as [_[]].
      apply (FT4 F0 f3 ω ω) in H; eauto. New MKT138; eauto. }
    assert ((F 0) < f3〈F0〉).
    { assert (Ensemble 0) by (pose proof in_ω_0; eauto).
      apply (Const_is_Function ω) in H15 as [H15[]].
      assert (ran(Const 0) ⊂ ω).
      { unfold Included; intros. rewrite H17 in H18.
        pose proof in_ω_0. apply MKT41 in H18; eauto.
        rewrite H18; auto. }
      pose proof in_ω_0. apply Fn_in_N' in H19.
      pose proof in_ω_0 as H20. apply (F_Const_Fa F0 ω) in H20; auto.
      rewrite <-H20. apply N'_Ord_Instantiate; auto.
      assert (A ⊂ \{ λ w, (Const 0)[w] ∈ f3[w] \}).
      { unfold Included; intros. apply AxiomII; split; eauto.
        assert (z ∈ ω).
        { apply NNPP; intro. rewrite <-H4 in H22.
          apply MKT69a in H22. apply AxiomII in H21 as [].
          rewrite H22 in H23. elim MKT39; eauto. }
        assert (f3[z] = ∩(\{ λ a, a ∈ ω /\ 0 ∈ a /\ (f1[z] + a)%ω = f2[z] \})).
        { pose proof H21. apply AxiomII in H21 as []. rewrite <-H12 in H22.
          apply Property_Value in H22; auto.
          apply AxiomII' in H22 as [H22[H25[[]|[]]]];
          try contradiction; auto. } apply AxiomII in H21 as [].
        apply Plus_PrOrder_Corollary in H24 as [k[[H24[]]]].
        assert ([k] = \{ λ a, a ∈ ω /\ 0 ∈ a /\ (f1[z] + a)%ω = f2[z] \}).
        { apply AxiomI; split; intros. apply MKT41 in H28; eauto.
          rewrite H28. apply AxiomII; split; eauto.
          apply AxiomII in H28 as []. apply H27 in H29.
          rewrite H29. apply MKT41; auto. }
        rewrite <-H28 in H23. destruct (@ MKT44 k); eauto.
        rewrite H23,H29. assert ((Const 0)[z] = 0).
        { rewrite <-H16 in H22. apply Property_Value,Property_ran
          in H22; auto. rewrite H17 in H22. pose proof in_ω_0.
          apply MKT41 in H22; eauto. }
        rewrite H31; auto. rewrite <-H8 in H22.
        apply Property_Value,Property_ran,H9 in H22; auto.
        rewrite <-H4 in H22.
        apply Property_Value,Property_ran,H5 in H22; auto. }
      destruct H as [_[H _]]. apply AxiomII in H as [H[[H22[H23[H24[]]]]]].
      apply (H26 A); repeat split; auto. unfold Included; intros.
      apply AxiomII in H28 as []. apply NNPP; intro. rewrite <-H16 in H30.
      apply MKT69a in H30. rewrite H30 in H29. elim MKT39; eauto.
      intro. New in_ω_0. rewrite H16 in H17. elim (@ MKT16 0); auto. }
    assert (u + f3〈F0〉 = v).
    { rewrite H6,H10. rewrite N'_Plus_Instantiate; auto.
      pose proof H3. apply (ωFun_Plus_P1 f1 f3)
      in H16 as [H16[]]; auto. apply (FT8 _ _ ω). split; auto.
      split; auto. repeat split; auto.
      assert (A ⊂ \{ λ u0, u0 ∈ ω /\ ((f1 + f3)[u0] = f2[u0])%ωfun \}).
      { unfold Included; intros. pose proof H19 as H19'.
        apply AxiomII in H19 as [].
        assert (z ∈ ω).
        { apply NNPP; intro. rewrite <-H4 in H21.
          apply MKT69a in H21. rewrite H21 in H20.
          elim MKT39; eauto. }
        apply AxiomII; repeat split; auto.
        rewrite ωFun_Plus_P2; auto.
        rewrite <-H12 in H21. apply Property_Value in H21; auto.
        apply AxiomII' in H21 as [H21[H22[[]|[]]]];
        try contradiction.
        apply Plus_PrOrder_Corollary in H20 as [k[[H20[]]]].
        assert ([k] = \{ λ a, a ∈ ω /\ 0 ∈ a /\ (f1[z] + a)%ω = f2[z] \}).
        { apply AxiomI; split; intros. apply MKT41 in H28; eauto.
          rewrite H28. apply AxiomII; split; eauto.
          apply MKT41; eauto. apply AxiomII in H28 as [].
          apply H27 in H29; auto. }
        rewrite <-H28 in H24. destruct (@ MKT44 k); eauto.
        rewrite H29 in H24. rewrite H24; auto. rewrite <-H8 in H22.
        apply Property_Value,Property_ran,H9 in H22; auto.
        rewrite <-H4 in H22. apply Property_Value,Property_ran,H5
        in H22; auto. }
      destruct H as [_[]]. apply AxiomII in H as [H[[H21[H22[H23[]]]]]].
      apply (H25 A); repeat split; auto. unfold Included; intros.
      apply AxiomII in H27; tauto. }
    repeat split; auto. intros x [H17[]]. rewrite <-H16 in H19.
    apply N'_Plus_Cancellation in H19; auto.
    apply AxiomII; split; eauto.
  - destruct H2 as [w[[H2[]]]].
    apply AxiomII in H0 as [H0[f1[H6[H7[]]]]].
    apply AxiomII in H1 as [H1[f2[H10[H11[]]]]].
    apply AxiomII in H2 as [H2[f3[H14[H15[]]]]].
    rewrite H9,H13,H17 in *. rewrite N'_Plus_Instantiate in H4; auto.
    apply N'_Ord_Instantiate; auto.
    assert (Ensemble 0) by (pose proof in_ω_0; eauto).
    apply (Const_is_Function ω) in H18 as [H18[]].
    assert (1 ⊂ ω).
    { unfold Included; intros. pose proof in_ω_0.
      apply MKT41 in H21; eauto. rewrite H21; auto. }
    rewrite <-H20 in H21. pose proof in_ω_0. apply Fn_in_N' in H22.
    pose proof in_ω_0. apply (F_Const_Fa F0 ω) in H23; auto.
    rewrite <-H23 in H3. apply N'_Ord_Instantiate in H3; auto;
    try split; auto. pose proof H6.
    apply (ωFun_Plus_P1 f1 f3) in H24 as [H24[]]; auto.
    destruct H as [_[]]. apply H27 in H4; auto. clear H10 H11 H12 H24 H25 H26.
    destruct H4 as [H4[H10[H11[H12[H24[H25[]]]]]]].
    set (A := \{ λ w, (Const 0)[w] ∈ f3[w] \}).
    set (B := \{ λ u, u ∈ ω /\ ((f1 + f3)[u] = f2[u])%ωfun \}).
    assert ((A ∩ B) ⊂ \{ λ w0, f1[w0] ∈ f2[w0] \}).
    { unfold Included; intros. apply MKT4' in H29 as [].
      apply AxiomII in H29 as []. apply AxiomII in H30 as [H30[]].
      rewrite ωFun_Plus_P2 in H33; auto. apply AxiomII; split; auto.
      apply Plus_PrOrder_Corollary. rewrite <-H12 in H32.
      apply Property_Value,Property_ran,H25 in H32; auto. rewrite <-H7 in H32.
      apply Property_Value,Property_ran,H8 in H32; auto.
      exists (f3[z]). repeat split; auto. rewrite <-H15 in H32.
      apply Property_Value,Property_ran,H16 in H32; auto.
      rewrite <-H19 in H32. apply Property_Value,Property_ran in H32; auto.
      rewrite H20 in H32. pose proof in_ω_0. apply MKT41 in H32; eauto.
      rewrite H32 in H31; auto. intros x [H34[]]. rewrite <-H33 in H36.
      apply Plus_Cancellation in H36; auto. rewrite <-H7 in H32.
      apply Property_Value,Property_ran,H8 in H32; auto. rewrite <-H15 in H32.
      apply Property_Value,Property_ran,H16 in H32; auto. }
    apply AxiomII in H as [H[[H30[H31[H32[]]]]]].
    apply (H34 (A ∩ B)); repeat split; auto.
    unfold Included; intros. apply AxiomII in H36 as [].
    apply NNPP; intro. rewrite <-H7 in H38. apply MKT69a in H38.
    rewrite H38 in H37. elim MKT39; eauto. intro. New in_ω_0.
    rewrite H19 in H20. elim (@ MKT16 0); auto.
Qed.

Property N'_Mult_Property1 : ∀ u, u ∈ N' -> u · (F 0) = F 0.
Proof.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[f[H1[H2[]]]]].
  rewrite H4. assert ((Const 0)〈F0〉 = F 0).
  { apply F_Const_Fa; destruct H,MKT135; auto. }
  rewrite <-H5. assert (Ensemble 0). eauto. apply (Const_is_Function ω)
  in H6 as [H6[]]. rewrite N'_Mult_Instantiate; auto.
  assert (∀ z, z ∈ ω -> f[z] ∈ ω ).
  { intros. rewrite <-H2 in H9.
    apply Property_Value,Property_ran in H9; auto. }
  assert (∀ z, z ∈ ω -> f[z] · (Const 0)[z] = 0)%ω.
  { intros. assert ((Const 0)[z] = 0).
    { rewrite <-H7 in H10. apply Property_Value,Property_ran
      in H10; auto. rewrite H8 in H10. destruct MKT135.
      apply MKT41 in H10; eauto. }
    rewrite H11,Mult_Property1_a; auto. }
  assert ((f · (Const 0))%ωfun = Const 0).
  { apply AxiomI; split; intros. apply AxiomII in H11 as
    [H11[x[y[H12[]]]]]. rewrite H10 in H14; auto. rewrite
    <-H2 in H13. apply Property_Value in H13; auto. rewrite
    H12. apply AxiomII'; repeat split; auto. rewrite <-H12;
    auto. apply Property_dom in H13. rewrite H2 in H13; auto.
    apply AxiomII in H11 as [H11[x[y[H12[]]]]]. rewrite H12
    in *. apply AxiomII'; repeat split; auto. rewrite H10; auto. }
  rewrite H11; auto. unfold Included; intros. rewrite H8 in H9.
  destruct MKT135. apply MKT41 in H9; eauto. rewrite H9; auto.
  intro. New in_ω_0. rewrite H7 in H8. elim (@ MKT16 0); auto.
Qed.

(* 验证 *N中的单位元: u * F1 = u *)
Property N'_Mult_Property2 : ∀ u, u ∈ N' -> u · (F 1) = u.
Proof.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[f[H1[H2[]]]]].
  rewrite H4. assert ((Const 1)〈F0〉 = (F 1)).
  { apply F_Const_Fa. destruct H; auto. apply in_ω_1. }
  rewrite <-H5. assert (Ensemble 1). eauto. apply (Const_is_Function ω)
  in H6 as [H6[]]. rewrite N'_Mult_Instantiate; auto.
  assert (∀ z, z ∈ ω -> f[z] ∈ ω ).
  { intros. rewrite <-H2 in H9.
    apply Property_Value,Property_ran in H9; auto.  }
  assert (∀ z, z ∈ ω -> Mult (f[z]) ((Const 1)[z]) = f[z]).
  { intros. assert ((Const 1)[z] = 1).
    { rewrite <-H7 in H10. apply Property_Value,Property_ran
      in H10; auto. rewrite H8 in H10. destruct MKT135.
      apply MKT41 in H10; eauto. }
    rewrite H11. replace 1 with (PlusOne 0). destruct MKT135.
    rewrite Mult_Property2_a,Mult_Property1_a,Plus_Property1_b;
    auto. unfold PlusOne. apply MKT17. }
  assert ((f · (Const 1))%ωfun = f).
  { apply AxiomI; split; intros. apply AxiomII in H11 as
    [H11[x[y[H12[]]]]]. rewrite H10 in H14; auto.
    rewrite <-H2 in H13. apply Property_Value in H13; auto.
    rewrite H12,H14; auto. apply AxiomII; split; eauto.
    pose proof H1. apply MKT70 in H12. pose proof H11.
    rewrite H12 in H11. apply AxiomII in H11 as [H11[x[y[]]]].
    exists x,y. rewrite H14 in H13. split; auto. apply
    Property_dom in H13. rewrite H2 in H13. rewrite H10; auto. }
  rewrite H11; auto. unfold Included; intros. rewrite H8 in H9.
  pose proof in_ω_1. apply MKT41 in H9; eauto. rewrite H9; auto.
  intro. New in_ω_0. rewrite H7 in H8. elim (@ MKT16 0); auto.
Qed.

(* 无零因子 *)
Property N'_Mult_Property3 : ∀ u v, u ∈ N' -> v ∈ N' -> u · v = F 0
  -> u = F 0 \/ v = F 0.
Proof.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[f1[H3[H4[]]]]].
  apply AxiomII in H1 as [H1[f2[H7[H8[]]]]]. rewrite H6,H10 in H2.
  rewrite N'_Mult_Instantiate in H2; auto. pose proof H3.
  apply (ωFun_Mult_P1 f1 f2) in H11 as [H11[]]; auto.
  assert (Ensemble 0) by eauto. apply (Const_is_Function ω) in H14 as [H14[]].
  assert (ran(Const 0) ⊂ ω).
  { unfold Included; intros. rewrite H16 in H17. pose proof in_ω_0.
    apply MKT41 in H17; eauto. rewrite H17; auto. }
  pose proof in_ω_0. apply Fn_in_N' in H18.
  pose proof in_ω_0. apply (F_Const_Fa F0 ω) in H19; auto.
  rewrite <-H19 in H2. destruct H. apply H20 in H2; auto.
  clear H11 H12 H13 H14 H15 H17.
  destruct H2 as [H2[H21[H11[H12[H13[H14[]]]]]]].
  set (A := \{ λ u, u ∈ ω /\ (f1 · f2)%ωfun[u] = (Const 0)[u] \}).
  set (B := \{ λ u, u ∈ ω /\ f1[u] = (Const 0)[u] \}).
  set (C := \{ λ u, u ∈ ω /\ f2[u] = (Const 0)[u] \}).
  assert (A ⊂ (B ∪ C)).
  { unfold Included; intros. apply AxiomII in H22 as [H22[]].
    rewrite ωFun_Mult_P2 in H24; auto.
    assert ((Const 0)[z] = 0).
    { rewrite <-H12 in H23. apply Property_Value,Property_ran
      in H23; auto. rewrite H16 in H23. pose proof in_ω_0.
      apply MKT41 in H23; eauto. }
    rewrite H25 in H24. assert (f1[z] ∈ ω /\ f2[z] ∈ ω) as [].
    pose proof H23. rewrite <-H4 in H23. rewrite <-H8 in H26.
    apply Property_Value,Property_ran,H5 in H23;
    apply Property_Value,Property_ran,H9 in H26; auto. apply MKT4.
    destruct (classic (f1[z] = 0)); [left|right; apply
    Mult_Cancellation_Lemma in H24; auto]; apply AxiomII;
    rewrite H25; auto. }
  apply AxiomII in H15 as [H15[[H23[H24[H25[]]]]]].
  assert ((B ∪ C) ∈ F0).
  { apply (H27 A); repeat split; auto. unfold Included; intros.
    apply MKT4 in H29. destruct H29; apply AxiomII in H29; tauto. }
  rewrite H6,H10,<-H19. apply (FT1 _ ω) in H29.
  destruct H29; [left|right]; apply (FT8 _ _ ω); split; auto;
  split; auto; repeat split; auto. destruct H20. apply AxiomII in H20; tauto.
  intro. New in_ω_0. rewrite H15 in H16. elim (@ MKT16 0); auto.
Qed.

(* 验证 *N中的乘法满足交换律. *)
Fact N'_Mult_Commutation : ∀ u v, u ∈ N' -> v ∈ N' -> u · v = v · u.
Proof.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[f[H2[H3[]]]]].
  apply AxiomII in H1 as [H1[g[H6[H7[]]]]].
  assert (∀ z, z ∈ ω -> (f[z] ∈ ω /\ g[z] ∈ ω)).
  { intros. split; [rewrite <-H3 in H10|rewrite <-H7 in H10];
    apply Property_Value,Property_ran in H10; auto. }
  rewrite H5,H9,N'_Mult_Instantiate,N'_Mult_Instantiate; auto.
  assert (f · g = g · f)%ωfun.
  { apply AxiomI; split; intros; apply AxiomII in H11
    as [H11[x[y[H12[]]]]]; apply AxiomII; split; eauto;
    exists x,y; repeat split; auto; apply H10 in H13 as [];
    rewrite Mult_Commutation; auto. }
  rewrite H11; auto.
Qed.

(* 验证*N中的乘法满足结合律 *)
Property N'_Mult_Association : ∀ u v w, u ∈ N' -> v ∈ N' -> w ∈ N'
  -> (u · v) · w = u · (v · w).
Proof.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[f1[H3[H4[]]]]].
  apply AxiomII in H1 as [H1[f2[H7[H8[]]]]].
  apply AxiomII in H2 as [H2[f3[H11[H12[]]]]].
  assert (∀ z, z ∈ ω -> (f1[z] ∈ ω /\ f2[z] ∈ ω /\ f3[z] ∈ ω)).
  { intros. repeat split;
    [rewrite <-H4 in H15|rewrite <-H8 in H15|rewrite <-H12 in H15];
    apply Property_Value,Property_ran in H15; auto. }
  pose proof H3; pose proof H11.
  apply (ωFun_Mult_P1 f1 f2) in H3 as [H3[]]; auto.
  apply (ωFun_Mult_P1 f2 f3) in H11 as [H11[]]; auto.
  rewrite H6,H10,H14,N'_Mult_Instantiate,N'_Mult_Instantiate,
  N'_Mult_Instantiate,N'_Mult_Instantiate; auto.
  assert ((f1 · f2) · f3 = f1 · (f2 · f3))%ωfun.
  { apply AxiomI; split; intros; apply AxiomII in H22
    as [H22[x[y[H23[]]]]]; apply AxiomII; split; auto; exists x,y;
    repeat split; auto; rewrite ωFun_Mult_P2; auto;
    rewrite ωFun_Mult_P2 in H25; auto; apply H15
    in H24 as [H24[]]; try rewrite <-Mult_Association; auto.
    rewrite Mult_Association; auto. }
  rewrite H22; auto.
Qed.

(* 验证*N中的乘法满足分配律. *)
Fact N'_Mult_Distribution : ∀ u v w, u ∈ N' -> v ∈ N' -> w ∈ N'
  -> u · (v + w) = (u · v) + (u · w).
Proof.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[f1[H3[H4[]]]]].
  apply AxiomII in H1 as [H1[f2[H7[H8[]]]]].
  apply AxiomII in H2 as [H2[f3[H11[H12[]]]]].
  assert (∀ z, z ∈ ω -> f1[z] ∈ ω /\ f2[z] ∈ ω /\ f3[z] ∈ ω).
  { intros. repeat split;
    [rewrite <-H4 in H15|rewrite <-H8 in H15|rewrite <-H12 in H15];
    apply Property_Value,Property_ran in H15; auto. }
  pose proof H3; pose proof H7; pose proof H11.
  apply (ωFun_Mult_P1 f1 f2) in H16 as [H16[]]; auto.
  apply (ωFun_Mult_P1 f1 f3) in H18 as [H18[]]; auto.
  apply (ωFun_Plus_P1 f2 f3) in H17 as [H17[]]; auto.
  rewrite H6,H10,H14. rewrite N'_Plus_Instantiate,N'_Mult_Instantiate,
  N'_Mult_Instantiate,N'_Mult_Instantiate,N'_Plus_Instantiate; auto.
  assert (f1 · (f2 + f3) = (f1 · f2) + (f1 · f3))%ωfun.
  { apply AxiomI; split; intros; apply AxiomII in H25 as
    [H25[x[y[H26[]]]]]; apply AxiomII; split; auto; exists x,y;
    repeat split; auto; try rewrite ωFun_Plus_P2
    in H28; auto; try rewrite ωFun_Mult_P2,
    ωFun_Mult_P2; auto; apply H15 in H27 as [H27[]];
    try rewrite <-Mult_Distribution; auto.
    rewrite ωFun_Mult_P2,ωFun_Mult_P2
    in H28; auto.
    rewrite ωFun_Plus_P2,Mult_Distribution; auto. }
  rewrite H25; auto.
Qed.

(* 验证*N中的乘法满足消去律.*)
Property N'_Mult_Cancellation : ∀ w u v, w ∈ N' -> u ∈ N' -> v ∈ N'
  -> w <> F 0 -> w · u = w · v -> u = v.
Proof.
  destruct NPAUF as [H _]. intros. apply AxiomII in H0 as [H0[f0[H5[H6[]]]]].
  apply AxiomII in H1 as [H1[f1[H9[H10[]]]]].
  apply AxiomII in H2 as [H2[f2[H13[H14[]]]]].
  rewrite H8,H12,H16 in *. rewrite N'_Mult_Instantiate,
  N'_Mult_Instantiate in H4; auto. apply (FT8 _ _ ω). split; auto.
  split; auto. repeat split; auto. pose proof H5; pose proof H5.
  apply (ωFun_Mult_P1 f0 f1) in H17 as [H17[]]; auto.
  apply (ωFun_Mult_P1 f0 f2) in H18 as [H18[]]; auto.
  destruct H. apply H23 in H4; auto. clear H17 H18 H19 H20 H21 H22.
  destruct H4 as [H4[H17[H18[H19[H20[H21[]]]]]]].
  assert (Ensemble 0) by eauto. apply (Const_is_Function ω) in H25 as [H25[]].
  assert (1 ⊂ ω).
  { pose proof in_ω_0. unfold Included; intros.
    apply MKT41 in H29; eauto. rewrite H29; auto. }
  rewrite <-H27 in H28. pose proof in_ω_0. apply Fn_in_N' in H29.
  pose proof in_ω_0. apply (F_Const_Fa F0 ω) in H30; auto. rewrite <-H30 in H3.
  assert (~ \{ λ u0, u0 ∈ ω /\ f0[u0] = (Const 0)[u0] \} ∈ F0).
  { intro. elim H3. apply (FT8 _ _ ω). split;
    auto. split; auto. repeat split; auto. }
  apply AxiomII in H22 as [H22[[H32[H33[H34[]]]]]].
  set (A := \{ λ u, u ∈ ω /\ (f0 · f1)%ωfun[u] = (f0 · f2)%ωfun[u] \}).
  set (B := \{ λ u0, u0 ∈ ω /\ f0[u0] = (Const 0)[u0] \}).
  set (C := \{ λ u0, u0 ∈ ω /\ f0[u0] <> (Const 0)[u0] \}).
  assert (B ⊂ ω).
  { unfold Included; intros. apply AxiomII in H38; tauto. }
  assert (∀ z, z ∈ ω -> (Const 0)[z] = 0).
  { intros. rewrite <-H26 in H39.
    apply Property_Value,Property_ran in H39; auto.
    rewrite H27 in H39. pose proof in_ω_0.
    apply MKT41 in H39; eauto. }
  apply H37 in H38 as []; try contradiction.
  assert ((ω ~ B) = C).
  { apply AxiomI; split; intros.
    - apply MKT4' in H40 as []. apply AxiomII in H41 as [].
      apply AxiomII; repeat split; auto. intro. elim H42.
      apply AxiomII; auto.
    - apply AxiomII in H40 as [H40[]]. apply MKT4'; split; auto.
      apply AxiomII; split; auto. intro. apply AxiomII in H43
      as [H43[]]; auto. }
  rewrite H40 in H38. clear H40.
  assert ((A ∩ C) ⊂ \{ λ u0, u0 ∈ ω /\ f1[u0] = f2[u0] \}).
  { unfold Included; intros. apply MKT4' in H40 as [].
    apply AxiomII in H40 as [H40[]].
    apply AxiomII in H41 as [H41[]].
    apply AxiomII; repeat split; auto. rewrite H39 in H45; auto.
    rewrite ωFun_Mult_P2,ωFun_Mult_P2
    in H43; auto. apply Mult_Cancellation in H43; auto.
    rewrite <-H6 in H42.
    apply Property_Value,Property_ran,H7 in H42; auto.
    rewrite <-H10 in H42.
    apply Property_Value,Property_ran,H11 in H42; auto.
    rewrite <-H14 in H42.
    apply Property_Value,Property_ran,H15 in H42; auto. }
  apply (H36 (A ∩ C)); repeat split; auto. unfold Included; intros.
  apply AxiomII in H41; tauto. intro. New in_ω_0. rewrite H26 in H27.
  elim (@ MKT16 0); auto.
Qed.

(* *N上定义的 N'_Ord关系 满足乘法保序 (需注意和 消去律 的区别)
                     (证明过程中需要用到滤子中的 大集性质 和 对交封闭 和
                      超滤的极大性 以及 算数超滤满足命题六的反向)*)
Fact N'_Mult_PrOrder : ∀ u v w, u ∈ N' -> v ∈ N' -> w ∈ N' -> w <> F 0
  -> u < v <-> (w · u) < (w · v).
Proof.
  destruct NPAUF as [H _]. split; intros.
  - pose proof H0 as Ha; pose proof H1 as Hb; pose proof H2 as Hc.
    apply AxiomII in H0 as [H0[f1[H5[H6[]]]]].
    apply AxiomII in H1 as [H1[f2[H9[H10[]]]]].
    apply AxiomII in H2 as [H2[f3[H13[H14[]]]]].
    apply AxiomII' in H4 as [].
    pose proof H5. apply (H17 f1 f2) in H18; auto.
    assert ((w · u) ∈ N'). { apply N'_Mult_in_N'; auto. }
    assert ((w · v) ∈ N'). { apply N'_Mult_in_N'; auto. }
    apply AxiomII'; split. apply MKT49a; eauto.
    intros. pose proof H5; pose proof H9.
    apply (ωFun_Mult_P1 f3 f1) in H29 as [H29[]]; auto.
    apply (ωFun_Mult_P1 f3 f2) in H30 as [H30[]]; auto.
    rewrite H8,H16,N'_Mult_Instantiate in H27; auto.
    rewrite H12,H16,N'_Mult_Instantiate in H28; auto.
    destruct H. apply H35 in H27; apply H35 in H28; auto.
    destruct H27 as [H27[H36[H37[H38[H39[H40[]]]]]]].
    destruct H28 as [H28[H43[H44[H45[H46[H47[]]]]]]].
    assert ((\{ λ w, f1[w] ∈ f2[w] \}
      ∩ \{ λ w, w ∈ ω /\ f3[w] <> Φ \})
       ⊂ \{ λ w, (f3 · f1)%ωfun[w] ∈ (f3 · f2)%ωfun[w] \}).
    { unfold Included; intros. apply MKT4' in H50 as [].
      apply AxiomII in H50 as []. apply AxiomII in H51 as [H51[]].
      apply AxiomII; split; auto. rewrite ωFun_Mult_P2,ωFun_Mult_P2; auto.
      assert (∀ f, Function f -> dom(f) = ω -> ran(f) ⊂ ω -> f[z] ∈ ω).
      { intros. rewrite <-H56 in H53.
        apply Property_Value,Property_ran in H53; auto. }
      apply Mult_PrOrder; auto. }
    apply AxiomII in H41 as [H41[[H51[H52[H53[]]]]]].
    assert ((\{ λ w, f1[w] ∈ f2[w] \}
      ∩ \{ λ w, w ∈ ω /\ f3[w] <> Φ \}) ∈ F0).
    { apply H54; auto.
      assert (\{ λ w, w ∈ ω /\ f3[w] <> Φ \} ⊂ ω).
      { unfold Included; intros. apply AxiomII in H57; tauto. }
      apply H56 in H57 as []; auto.
      assert (ω ~ \{ λ w, w ∈ ω /\ f3[w] <> Φ \}
        = \{ λ w, w ∈ ω /\ f3[w] = Φ \}).
      { apply AxiomI; split; intros. apply MKT4' in H58 as [].
        apply AxiomII in H59 as []. apply AxiomII; repeat split;
        auto. apply NNPP; intro. elim H60. apply AxiomII; auto.
        apply AxiomII in H58 as [H58[]]. apply MKT4'; split;
        auto. apply AxiomII; split; auto. intro. apply AxiomII
        in H61 as [H61[]]. contradiction. }
      rewrite H58 in H57.
      assert (\{ λ w, w ∈ ω /\ f3[w] = Φ \}
        = \{ λ w, w ∈ ω /\ f3[w] = (Const 0)[w] \}).
      { apply AxiomI; split; intros. apply AxiomII in H59 as [H59[]].
        apply AxiomII; repeat split; auto. assert (Ensemble 0) by eauto.
        apply (Const_is_Function ω) in H62 as [H62[]].
        rewrite <-H63 in H60. apply Property_Value,Property_ran in H60; auto.
        rewrite H64 in H60. apply MKT41 in H60; eauto. rewrite H60,H61; auto.
        intro. rewrite H63 in H60. elim (@ MKT16 z); auto.
        apply AxiomII in H59 as [H59[]]. apply AxiomII;
        repeat split; auto. assert (Ensemble 0) by eauto.
        apply (Const_is_Function ω) in H62 as [H62[]].
        rewrite <-H63 in H60. apply Property_Value,Property_ran in H60; auto.
        rewrite H64 in H60. apply MKT41 in H60; eauto. rewrite H61,H60; auto.
        intro. rewrite H63 in H60. elim (@ MKT16 z); auto. }
      rewrite H59 in H57. clear H58 H59.
      assert (AlmostEqual f3 (Const 0) ω ω F0).
      { assert (Ensemble 0) by eauto.
        apply (Const_is_Function ω) in H58 as [H58[]]. split; auto. split; auto.
        repeat split; auto. unfold Included; intros. rewrite H60 in H61.
        destruct MKT135. apply MKT41 in H61; eauto. rewrite H61; auto.
        intro. rewrite H59 in H53; auto. }
      apply (FT8 _ _ ω) in H58. destruct MKT135. rewrite F_Const_Fa
      in H58; auto. elim H3; rewrite H16; auto. }
    assert (\{ λ w, (f3 · f1)%ωfun[w] ∈ (f3 · f2)%ωfun[w] \} ∈ F0).
    { apply (H55 (\{ λ w, f1[w] ∈ f2[w] \}
        ∩ \{ λ w, w ∈ ω /\ f3[w] <> Φ \})); repeat split; auto.
      unfold Included; intros. apply AxiomII in H58 as [].
      apply NNPP; intro. rewrite <-H31 in H60.
      apply MKT69a in H60. rewrite H60 in H59. elim MKT39; eauto. }
    assert (\{ λ u, u ∈ ω /\ (f3 · f1)%ωfun[u] = f[u] \}
      ∩ \{ λ u, u ∈ ω /\ (f3 · f2)%ωfun[u] = g[u] \}
      ∩ \{ λ w, (f3 · f1)%ωfun[w] ∈ (f3 · f2)%ωfun[w] \}
       ⊂ \{ λ w, f[w] ∈ g[w] \}).
    { unfold Included; intros. apply MKT4' in H59 as [].
      apply MKT4' in H60 as []. apply AxiomII in H59 as [H59[]].
      apply AxiomII in H60 as [H60[]]. apply AxiomII in H61 as [].
      rewrite H63,H65 in H66. apply AxiomII; auto. }
    apply (H55 (\{ λ u, u ∈ ω /\ (f3 · f1)%ωfun[u] = f[u] \}
      ∩ \{ λ u, u ∈ ω /\ (f3 · f2)%ωfun[u] = g[u] \}
      ∩ \{ λ w, (f3 · f1)%ωfun[w] ∈ (f3 · f2)%ωfun[w] \}));
    repeat split; auto. unfold Included; intros.
    apply AxiomII in H60 as []. apply NNPP; intro.
    rewrite <-H23 in H62. apply MKT69a in H62.
    rewrite H62 in H61. elim MKT39; eauto.
  - apply AxiomII in H0 as [H0[f1[H5[H6[]]]]].
    apply AxiomII in H1 as [H1[f2[H9[H10[]]]]].
    apply AxiomII in H2 as [H2[f3[H13[H14[]]]]].
    rewrite H8,H12,H16 in *.
    rewrite N'_Mult_Instantiate,N'_Mult_Instantiate in H4; auto.
    pose proof H13; pose proof H13.
    apply (ωFun_Mult_P1 f3 f1) in H17 as [H17[]]; auto.
    apply (ωFun_Mult_P1 f3 f2) in H18 as [H18[]]; auto.
    apply N'_Ord_Instantiate in H4; auto.
    apply N'_Ord_Instantiate; auto.
    set (A := \{ λ w, (f3 · f1)%ωfun[w] ∈ (f3 · f2)%ωfun[w] \}).
    assert (A ⊂ \{ λ w0, f1[w0] ∈ f2[w0] \}).
    { unfold Included; intros. apply AxiomII in H23 as [].
      assert (z ∈ ω).
      { apply NNPP; intro. rewrite <-H19 in H25.
        apply MKT69a in H25. rewrite H25 in H24.
        elim MKT39; eauto. }
      rewrite ωFun_Mult_P2,ωFun_Mult_P2
      in H24; auto. apply AxiomII; split; auto.
      apply Mult_PrOrder in H24; auto. rewrite <-H14 in H25.
      apply Property_Value,Property_ran,H15 in H25; auto.
      rewrite <-H6 in H25.
      apply Property_Value,Property_ran,H7 in H25; auto.
      rewrite <-H10 in H25.
      apply Property_Value,Property_ran,H11 in H25; auto. intro.
      rewrite H27,(Mult_Property1_b (f2[z])) in H24.
      elim (@ MKT16 (0 · f1[z])%ω); auto. rewrite <-H10 in H25.
      apply Property_Value,Property_ran,H11 in H25; auto. }
    destruct H as [_[]]. apply AxiomII in H as [H[[H25[H26[H27[]]]]]].
    apply (H29 A); repeat split; auto. unfold Included; intros.
    apply AxiomII in H31 as []. apply NNPP; intro.
    rewrite <-H6 in H33. apply MKT69a in H33.
    rewrite H33 in H32. elim MKT39; eauto.
Qed.


(* *N_N 是由所有主超滤构成的类 *)
Definition N'_N := \{ λ u, ∃ n, n ∈ ω /\ u = F n \}.

(* *N_N 是一个集*)
Property N'_N_is_Set : Ensemble (N'_N).
Proof.
  apply (MKT33 βω). apply βA_is_Set. unfold Included; intros.
  apply AxiomII in H as [H[n[]]]. apply AxiomII; split; auto.
  rewrite H1. apply Fa_P2_b; auto. New MKT138. eauto.
Qed.


(* 主超滤集是*N的子集 *)
Property N'_N_subset_N' : N'_N ⊂ N'.
Proof.
  destruct NPAUF as [H _]. unfold Included; intros.
  apply AxiomII in H0 as [H0[m[]]]. apply Fn_in_N' in H1. rewrite H2; auto.
Qed.

Property Fn_in_N'_N : ∀ n, n ∈ ω -> (F n) ∈ N'_N.
Proof.
  intros. pose proof H. apply Fa_P2_b in H. destruct H.
  apply Filter_is_Set_Fact2 in H. apply AxiomII; split; eauto.
  New MKT138; eauto.
Qed.


(* 以下6条定义及结论旨在说明ω与 *N_N 是同构的, 即 *N_N 实际上可以作为自然数集使用 *)

(* 构造: φ是ω到 *N_N 的一一函数*)
Definition φ := \{\ λ u v, u ∈ ω /\ v = F u \}\.

Property φ_is_Function : Function1_1 φ /\ dom(φ) = ω /\ ran(φ) = N'_N.
Proof.
  assert (Function1_1 φ).
  { repeat split; unfold Relation; intros; try destruct H.
    - apply AxiomII in H as [H[x[y[]]]]; eauto.
    - apply AxiomII' in H as [H[]].
      apply AxiomII' in H0 as [H0[]]. rewrite H2,H4; auto.
    - apply AxiomII in H as [H[x[y[]]]]; eauto.
    - apply AxiomII' in H as []. apply AxiomII' in H1 as [H1[]].
      apply AxiomII' in H0 as []. apply AxiomII' in H4 as [H4[]].
      apply NNPP; intro. apply (Example2 ω y z) in H7; auto.
      rewrite H3 in H6; auto. }
  split; auto. destruct H. split; apply AxiomI; split; intros.
  - apply AxiomII in H1 as [H1[]]. apply AxiomII' in H2; tauto.
  - apply AxiomII; split; eauto. exists (F z).
    apply AxiomII'; split; auto. pose proof H1.
    apply Fa_P2_b in H2 as []. apply Filter_is_Set_Fact2 in H2.
    apply MKT49a; eauto. New MKT138; eauto.
  - apply AxiomII in H1 as [H1[]].
    apply AxiomII' in H2 as [H2[]]. apply AxiomII; split; eauto.
  - apply AxiomII in H1 as [H1[x[]]]. apply AxiomII; split; auto.
    exists x. apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.

Property φ_0 : φ[0] = F 0.
Proof.
  destruct φ_is_Function as [[][]]. pose proof in_ω_0.
  rewrite <-H1 in H3. apply Property_Value,AxiomII' in H3; tauto.
Qed.

Property φ_1 : φ[1] = F 1.
Proof.
  destruct φ_is_Function as [[][]]. pose proof in_ω_1.
  rewrite <-H1 in H3. apply Property_Value,AxiomII' in H3; tauto.
Qed.

(* φ是序保持的:
   *N_N中所有主超滤的排序方式类似于自然数的排序方式 (自然数集到主超滤集的序保持) *)
Property φ_PrOrder : ∀ m n, m ∈ ω -> n ∈ ω -> m ∈ n <-> φ[m] < φ[n].
Proof.
  destruct φ_is_Function as [[][]]. destruct NPAUF as [H3 _].
  assert (ω <> 0) as HH.
  { intro. New in_ω_0. rewrite H4 in H5. elim (@ MKT16 0); auto. }
  split; intros.
  - assert (φ[m] = F m /\ Ensemble (F m)) as [].
    { rewrite <-H1 in H4. apply Property_Value in H4; auto.
      apply AxiomII' in H4 as [H4[]]. split; auto. rewrite
      H8 in H4. apply MKT49b in H4; tauto. }
    assert (φ[n] = F n /\ Ensemble (F n)) as [].
    { rewrite <-H1 in H5. apply Property_Value in H5; auto.
      apply AxiomII' in H5 as [H5[]]. split; auto. rewrite
      H10 in H5. apply MKT49b in H5; tauto. }
    apply AxiomII'; split.
    rewrite H7,H9; apply MKT49a; auto. intros.
    assert ((Const m)〈F0〉 = F m /\ (Const n)〈F0〉 = F n) as [].
    { destruct H3. split; apply F_Const_Fa; auto. }
    rewrite H7,<-H19 in H17. rewrite H9,<-H20 in H18. destruct H3.
    assert (Ensemble m /\ Ensemble n) as [] by (split; eauto).
    apply (Const_is_Function ω) in H22 as [H22[]]; auto.
    apply (Const_is_Function ω) in H23 as [H23[]]; auto.
    assert (ran(Const n) ⊂ ω /\ ran(Const m) ⊂ ω) as [].
    { split; unfold Included; intros; try rewrite H25 in H28;
      try rewrite H27 in H28; apply MKT41 in H28; eauto;
      try rewrite H28; auto. }
    apply H21 in H17; apply H21 in H18; auto.
    destruct H17 as [H17[H30[H31[H32[H33[H34[]]]]]]].
    destruct H18 as [H18[H37[H38[H39[H40[H41[]]]]]]].
    assert (\{ λ u, u ∈ ω /\ (Const m)[u] = f[u] \}
      = \{ λ u, u ∈ ω /\ m = f[u] \}).
    { apply AxiomI; split; intros. apply AxiomII in H44 as [H44[]].
      apply AxiomII; repeat split; auto. rewrite <-H24 in H45.
      apply Property_Value,Property_ran in H45; auto.
      rewrite H25 in H45. apply MKT41 in H45; eauto.
      rewrite H45 in H46; auto. apply AxiomII in H44 as [H44[]].
      apply AxiomII; repeat split; auto. rewrite <-H46.
      rewrite <-H24 in H45. apply Property_Value,Property_ran
      in H45; auto. rewrite H25 in H45. apply MKT41 in H45; eauto. }
    assert (\{ λ u, u ∈ ω /\ (Const n)[u] = g[u] \}
      = \{ λ u, u ∈ ω /\ n = g[u] \}).
    { apply AxiomI; split; intros. apply AxiomII in H45 as [H45[]].
      apply AxiomII; repeat split; auto. rewrite <-H26 in H46.
      apply Property_Value,Property_ran in H46; auto.
      rewrite H27 in H46. apply MKT41 in H46; eauto.
      rewrite H46 in H47; auto. apply AxiomII in H45 as [H45[]].
      apply AxiomII; repeat split; auto. rewrite <-H47.
      rewrite <-H26 in H46. apply Property_Value,Property_ran
      in H46; auto. rewrite H27 in H46. apply MKT41 in H46; eauto. }
    rewrite H44 in H36. rewrite H45 in H43. clear H44 H45.
    assert (ω = \{ λ u, u ∈ ω /\ m ∈ n \}).
    { apply AxiomI; split; intros. apply AxiomII; split;
      eauto. apply AxiomII in H44; tauto. }
    assert ((\{ λ u, u ∈ ω /\ m = f[u] \}
      ∩ \{ λ u, u ∈ ω /\ n = g[u] \}
      ∩ \{ λ u, u ∈ ω /\ m ∈ n \}) ⊂ \{ λ w, f[w] ∈ g[w] \}).
    { unfold Included; intros. apply MKT4' in H45 as [].
      apply MKT4' in H46 as [].
      apply AxiomII in H45 as [H45[]].
      apply AxiomII in H46 as [H46[]].
      apply AxiomII in H47 as [H47[]].
      apply AxiomII; split; auto. rewrite <-H49,<-H51; auto. }
    rewrite <-H44 in H45.
    apply AxiomII in H35 as [H35[[H46[H47[H48[]]]]]].
    apply (H50 (\{ λ u, u ∈ ω /\ m = f[u] \}
      ∩ \{ λ u, u ∈ ω /\ n = g[u] \} ∩ ω)) ; auto.
    repeat split; auto. unfold Included; intros.
    apply AxiomII in H52 as []. apply NNPP; intro.
    rewrite <-H13 in H54. apply MKT69a in H54.
    rewrite H54 in H53. elim MKT39; eauto.
  - apply AxiomII' in H6 as [].
    assert (\{ λ w, (Const m)[w] ∈ (Const n)[w] \} ∈ F0).
    { assert (∀ m, m ∈ ω -> φ[m] = (Const m)〈F0〉).
      { intros. destruct H3. rewrite F_Const_Fa; auto.
        assert (Ensemble m0) by eauto.
        apply (Const_is_Function ω) in H10 as [H10[]]; auto.
        rewrite <-H1 in H8. apply Property_Value in H8; auto.
        apply AxiomII' in H8; tauto. }
      assert (Ensemble m /\ Ensemble n) as [] by (split; eauto).
      apply (Const_is_Function ω) in H9 as [H9[]]; auto.
      apply (Const_is_Function ω) in H10 as [H10[]]; auto.
      apply H7; auto. unfold Included; intros.
      rewrite H12 in H15. apply MKT41 in H15; eauto.
      rewrite H15; auto. unfold Included; intros.
      rewrite H14 in H15. apply MKT41 in H15; eauto.
      rewrite H15; auto. }
    assert (∀ m n, m ∈ ω -> n ∈ ω -> (Const m)[n] = m).
    { intros. assert (Ensemble m0) by eauto.
      apply (Const_is_Function ω) in H11 as [H11[]]; auto.
      rewrite <-H12 in H10.
      apply Property_Value,Property_ran in H10; auto.
      rewrite H13 in H10. apply MKT41 in H10; eauto. }
    assert (\{ λ w, (Const m)[w] ∈ (Const n)[w] \}
       ⊂ \{ λ w, w ∈ ω /\ m ∈ n \}).
    { unfold Included; intros. apply AxiomII in H10 as [].
      destruct (classic (z ∈ ω)). pose proof H12. pose proof H12.
      apply (H9 m z) in H12; auto. apply (H9 n z) in H13; auto.
      rewrite H12,H13 in H11. apply AxiomII; auto.
      assert (Ensemble m) by eauto.
      apply (Const_is_Function ω) in H13 as [H13[]]; auto.
      rewrite <-H14 in H12. apply MKT69a in H12.
      rewrite H12 in H11. elim MKT39; eauto. }
    destruct H3 as [_[]]. apply AxiomII in H3 as [H3[[H12[H13[H14[]]]]]].
    assert (\{ λ u, u ∈ ω /\ m ∈ n \} ∈ F0).
    { apply (H16 (\{ λ w, (Const m)[w] ∈ (Const n)[w] \}));
      repeat split; auto. unfold Included; intros.
      apply AxiomII in H18; tauto. }
    apply NNPP; intro.
    assert (\{ λ u, u ∈ ω /\ m ∈ n \} = Φ).
    { apply AxiomI; split; intros; elim (@ MKT16 z); auto.
      apply AxiomII in H20 as [H20[]]. contradiction. }
    rewrite H20 in H18. contradiction.
Qed.

(* φ是加法保持的 *)
Property φ_PrPlus : ∀ m n, m ∈ ω -> n ∈ ω -> φ[(m + n)%ω] = φ[m] + φ[n].
Proof.
  destruct NPAUF as [H _]. intros. assert (∀ m, m ∈ ω -> φ[m] = F m).
  { intros. destruct φ_is_Function as [H4[]]. rewrite <-H3 in H2.
    destruct H4. apply Property_Value in H2; auto.
    apply AxiomII' in H2; tauto. }
  assert (∀ m, m ∈ ω -> (Const m)〈F0〉 = F m).
  { intros. destruct H. apply F_Const_Fa; auto. }
  assert (ω <> 0) as HH.
  { intro. New in_ω_0. rewrite H4 in H5. elim (@ MKT16 0); auto. }
  assert (∀ m n, m ∈ ω -> n ∈ ω -> (Const m)[n] = m) as Ha.
  { intros. assert (Ensemble m0) by eauto.
    apply (Const_is_Function ω) in H6 as [H6[]]; auto.
    rewrite <-H7 in H5. apply Property_Value,Property_ran in H5; auto.
    rewrite H8 in H5. apply MKT41 in H5; eauto. }
  rewrite H2,H2,H2; try apply ω_Plus_in_ω; auto.
  rewrite <-(H3 m),<-(H3 n); auto.
  assert (Ensemble m /\ Ensemble n) as [] by (split; eauto).
  apply (Const_is_Function ω) in H4 as [H4[]]; auto.
  apply (Const_is_Function ω) in H5 as [H5[]]; auto.
  rewrite N'_Plus_Instantiate; auto. all:swap 1 2.
  unfold Included; intros. rewrite H7 in H10.
  apply MKT41 in H10; eauto. rewrite H10; auto. all:swap 1 2.
  unfold Included; intros. rewrite H9 in H10.
  apply MKT41 in H10; eauto. rewrite H10; auto.
  assert (((Const m) + (Const n))%ωfun = (Const (m + n)%ω)).
  { apply AxiomI; split; intros.
    - apply AxiomII in H10 as [H10[x[y[H11[]]]]].
      apply AxiomII; split; auto. exists x,y. repeat split; auto.
      rewrite Ha,Ha in H13; auto.
    - apply AxiomII in H10 as [H10[x[y[H11[]]]]].
      apply AxiomII; split; auto. exists x,y. repeat split; auto.
      rewrite Ha,Ha; auto. }
  rewrite H10. symmetry. apply H3,ω_Plus_in_ω; auto.
Qed.

(* φ是乘法保持的 *)
Property φ_PrMult : ∀ m n, m ∈ ω -> n ∈ ω -> φ[(m · n)%ω] = φ[m] · φ[n].
Proof.
  destruct NPAUF as [H _]. intros. assert (∀ m, m ∈ ω -> φ[m] = F m).
  { intros. destruct φ_is_Function as [H4[]]. rewrite <-H3 in H2.
    destruct H4. apply Property_Value in H2; auto.
    apply AxiomII' in H2; tauto. }
  assert (∀ m, m ∈ ω -> (Const m)〈F0〉 = F m).
  { intros. destruct H. apply F_Const_Fa; auto. }
  assert (ω <> 0) as HH.
  { intro. New in_ω_0. rewrite H4 in H5. elim (@ MKT16 0); auto. }
  assert (∀ m n, m ∈ ω -> n ∈ ω -> (Const m)[n] = m) as Ha.
  { intros. assert (Ensemble m0) by eauto.
    apply (Const_is_Function ω) in H6 as [H6[]]; auto.
    rewrite <-H7 in H5. apply Property_Value,Property_ran in H5;
    auto. rewrite H8 in H5. apply MKT41 in H5; eauto. }
  rewrite H2,H2,H2; try apply ω_Mult_in_ω; auto.
  rewrite <-(H3 m),<-(H3 n); auto.
  assert (Ensemble m /\ Ensemble n) as [] by (split; eauto).
  apply (Const_is_Function ω) in H4 as [H4[]]; auto.
  apply (Const_is_Function ω) in H5 as [H5[]]; auto.
  rewrite N'_Mult_Instantiate; auto. all:swap 1 2.
  unfold Included; intros. rewrite H7 in H10.
  apply MKT41 in H10; eauto. rewrite H10; auto.
  all:swap 1 2. unfold Included; intros. rewrite H9 in H10.
  apply MKT41 in H10; eauto. rewrite H10; auto.
  assert (((Const m) · (Const n))%ωfun = Const (m · n)%ω).
  { apply AxiomI; split; intros.
    - apply AxiomII in H10 as [H10[x[y[H11[]]]]].
      apply AxiomII; split; auto. exists x,y.
      repeat split; auto. rewrite Ha,Ha in H13; auto.
    - apply AxiomII in H10 as [H10[x[y[H11[]]]]].
      apply AxiomII; split; auto. exists x,y.
      repeat split; auto. rewrite Ha,Ha; auto. }
  rewrite H10. symmetry. apply H3,ω_Mult_in_ω; auto.
Qed.

(* φ对函数的复合运算是保持的 *)
Property φ_PrComposition : ∀ m h, m ∈ ω -> Function h -> dom(h) = ω
  -> ran(h) ⊂ ω -> φ[h[m]] = h〈φ[m]〉.
Proof.
  destruct NPAUF as [H _]. intros. assert (∀ m, m ∈ ω -> φ[m] = F m).
  { intros. destruct φ_is_Function as [H5[]]. rewrite <-H6 in H4.
    destruct H5. apply Property_Value in H4; auto.
    apply AxiomII' in H4; tauto. }
  assert (∀ m, m ∈ ω -> (Const m)〈F0〉 = F m).
  { intros. destruct H. apply F_Const_Fa; auto. }
  assert (∀ m, m ∈ ω -> h[m] ∈ ω).
  { intros. rewrite <-H2 in H6. apply Property_Value,
    Property_ran in H6; auto. }
  rewrite H4,H4; auto. symmetry. apply FT5_a; auto. New MKT138; eauto.
Qed.

(* 综合以上6条定义及结论, 主超滤集与自然数集在同构意义上相同, 于是对于*N,
   若只讨论其中的主超滤, 这些主超滤具有形同自然数的序结构: F0 F1 F2 F3 F4 ··· *)

(* *N_N对加法封闭.*)
Property N'_N_Plus_in_N'_N : ∀ u v, u ∈ N'_N -> v ∈ N'_N
  -> (u + v) ∈ N'_N.
Proof.
  destruct NPAUF as [H _]. intros. pose proof H0; pose proof H1.
  apply N'_N_subset_N' in H2,H3; auto.
  pose proof H3. apply (N'_Plus_in_N' u v) in H4; auto.
  apply AxiomII; split; eauto. apply AxiomII in H0 as [H0[m[]]].
  apply AxiomII in H1 as [H1[n[]]].
  assert (Ensemble m /\ Ensemble n) as [] by (split; eauto).
  assert (ω <> 0) as HH.
  { intro. rewrite H11 in H5. elim (@ MKT16 m); auto. }
  apply (Const_is_Function ω) in H9 as [H9[]]; auto.
  apply (Const_is_Function ω) in H10 as [H10[]]; auto.
  pose proof H5; pose proof H7. pose proof H.
  apply (F_Const_Fa F0 ω) in H15; apply (F_Const_Fa F0 ω) in H16;
  destruct H17 as [_[]]; auto. clear H18. exists (m + n)%ω.
  assert (ran(Const m) ⊂ ω /\ ran(Const n) ⊂ ω) as [].
  { rewrite H12,H14. split; unfold Included; intros;
    apply MKT41 in H18; eauto; rewrite H18; auto. }
  assert ((m + n)%ω ∈ ω). { apply ω_Plus_in_ω; auto. }
  assert (Ensemble (m + n)%ω) by eauto.
  apply (Const_is_Function ω) in H21 as [H21[]]; auto.
  pose proof H20. apply (F_Const_Fa F0 ω) in H24; auto.
  assert (ran(Const (m + n)%ω) ⊂ ω).
  { rewrite H23. unfold Included; intros.
    apply MKT41 in H25; eauto. rewrite H25; auto. }
  split; auto. rewrite <-H24,H6,H8,<-H15,<-H16,N'_Plus_Instantiate;
  auto. pose proof H9. apply (ωFun_Plus_P1 _ (Const n)) in H26 as [H26[]]; auto.
  assert (((Const m) + (Const n))%ωfun = Const (m + n)%ω).
  { apply MKT71; auto. intros. destruct (classic (x ∈ ω)).
    - rewrite ωFun_Plus_P2; auto.
      pose proof H29. pose proof H29. rewrite <-H11 in H29.
      rewrite <-H13 in H30. rewrite <-H22 in H31.
      apply Property_Value,Property_ran in H29;
      apply Property_Value,Property_ran in H30;
      apply Property_Value,Property_ran in H31; auto.
      rewrite H12 in H29. rewrite H14 in H30. rewrite H23 in H31.
      apply MKT41 in H29; apply MKT41 in H30; apply MKT41 in H31;
      eauto. rewrite H29,H30,H31; auto.
    - pose proof H29. rewrite <-H22 in H29. rewrite <-H27 in H30.
      apply MKT69a in H29; apply MKT69a in H30.
      rewrite H29,H30; auto. }
  rewrite H29; auto.
Qed.

(* *N_N对乘法封闭.*)
Property N'_N_Mult_in_N'_N : ∀ u v, u ∈ N'_N -> v ∈ N'_N -> (u · v) ∈ N'_N.
Proof.
  destruct NPAUF as [H _]. intros. pose proof H0; pose proof H1.
  apply N'_N_subset_N' in H2,H3; auto.
  pose proof H3. apply (N'_Mult_in_N' u v) in H4; auto.
  apply AxiomII; split; eauto. apply AxiomII in H0 as [H0[m[]]].
  apply AxiomII in H1 as [H1[n[]]].
  assert (Ensemble m /\ Ensemble n) as [] by (split; eauto).
  assert (ω <> 0) as HH.
  { intro. rewrite H11 in H5. elim (@ MKT16 m); auto. }
  apply (Const_is_Function ω) in H9 as [H9[]]; auto.
  apply (Const_is_Function ω) in H10 as [H10[]]; auto.
  pose proof H5; pose proof H7. pose proof H.
  apply (F_Const_Fa F0 ω) in H15; apply (F_Const_Fa F0 ω) in H16;
  destruct H17 as [_[]]; auto. clear H18. exists (m · n)%ω.
  assert (ran(Const m) ⊂ ω /\ ran(Const n) ⊂ ω) as [].
  { rewrite H12,H14. split; unfold Included; intros;
    apply MKT41 in H18; eauto; rewrite H18; auto. }
  assert ((m · n)%ω ∈ ω). { apply ω_Mult_in_ω; auto. }
  assert (Ensemble (m · n)%ω) by eauto.
  apply (Const_is_Function ω) in H21 as [H21[]]; auto.
  pose proof H20. apply (F_Const_Fa F0 ω) in H24; auto.
  assert (ran(Const (m · n)%ω) ⊂ ω).
  { rewrite H23. unfold Included; intros.
    apply MKT41 in H25; eauto. rewrite H25; auto. }
  split; auto. rewrite <-H24,H6,H8,<-H15,<-H16,N'_Mult_Instantiate;
  auto. pose proof H9. apply (ωFun_Mult_P1 _ (Const n)) in H26 as [H26[]]; auto.
  assert (((Const m) · (Const n))%ωfun = Const (m · n)%ω).
  { apply MKT71; auto. intros. destruct (classic (x ∈ ω)).
    - rewrite ωFun_Mult_P2; auto.
      pose proof H29. pose proof H29. rewrite <-H11 in H29.
      rewrite <-H13 in H30. rewrite <-H22 in H31.
      apply Property_Value,Property_ran in H29;
      apply Property_Value,Property_ran in H30;
      apply Property_Value,Property_ran in H31; auto.
      rewrite H12 in H29. rewrite H14 in H30. rewrite H23 in H31.
      apply MKT41 in H29; apply MKT41 in H30; apply MKT41 in H31;
      eauto. rewrite H29,H30,H31; auto.
    - pose proof H29. rewrite <-H22 in H29. rewrite <-H27 in H30.
      apply MKT69a in H29; apply MKT69a in H30.
      rewrite H29,H30; auto. }
  rewrite H29; auto.
Qed.


(* *N_N是*N的真子集, 也就是说, *N中除了主超滤还存在其他的元素.
   如果将主超滤就视为对应的自然数本身(在同构性意义上是允许的),
   那么这些多出的元素则是'自然数的延伸', 或者说'非标准自然数'.
   也就是说, *N实现了自然数集的非标准扩张.
   接下来的内容将是关于这些'非标准自然数'的.  *)
Property N'_N_propersubset_N' :  N'_N ⊂ N' /\ N'_N <> N'.
Proof.
  destruct NPAUF. split.
  - unfold Included; intros. apply AxiomII in H1 as [H1[m[]]].
    apply Fn_in_N' in H2. rewrite H3; auto.
  - intro. set (f := \{\ λ u v, u ∈ ω /\ v = u \}\).
    assert (Function f).
    { split; intros. unfold Relation; intros. apply AxiomII in H2
      as [H2[x[y[]]]]; eauto. apply AxiomII' in H2 as [H2[]].
      apply AxiomII' in H3 as [H3[]]. rewrite H5,H7; auto. }
    assert (dom(f) = ω).
    { apply AxiomI; split; intros. apply AxiomII in H3 as [H3[]].
      apply AxiomII' in H4; tauto. apply AxiomII; split; eauto.
      exists z. apply AxiomII'; split; auto. apply MKT49a; eauto. }
    assert (ran(f) ⊂ ω).
    { unfold Included; intros. apply AxiomII in H4 as [H4[]].
      apply AxiomII' in H5 as [H5[]]. rewrite H7; auto. }
    assert (f〈F0〉 = F0).
    { assert (∀ z, z ⊂ ω -> f⁻¹「z」 = z).
      { intros. apply AxiomI; split; intros.
        apply AxiomII in H6 as [H6[]].
        apply Property_Value,AxiomII' in H7 as [H7[]]; auto.
        rewrite <-H10; auto. apply AxiomII; split; eauto.
        pose proof H6. apply H5 in H6. rewrite <-H3 in H6.
        split; auto. apply Property_Value,AxiomII'
        in H6 as [H6[]]; auto. rewrite H9; auto. }
      apply AxiomI; split; intros.
      - apply AxiomII in H6 as [H6[]]. rewrite <-(H5 z); auto.
      - apply AxiomII; split; eauto. destruct H as [_[]].
        apply AxiomII in H as [H[[]]]. pose proof H6.
        apply H8,AxiomII in H6 as []. split; auto.
        rewrite H5; auto. }
    assert (F0 ∈ N'). { destruct H. apply AxiomII; split; eauto. }
    rewrite <-H1 in H6. apply AxiomII in H6 as [H6[m[]]]. elim (H0 m); auto.
Qed.


(*引理 定义域是一个整数的函数, 其值域有限. *)
Lemma N'_Infty_Lemma : ∀ n f, n ∈ ω -> Function f -> dom(f) = n
  -> Finite (ran(f)).
Proof.
  intros. set (A x := \{ λ u, [u,x] ∈ f \}).
  assert (∀ x, x ∈ ran(f) -> A x <> 0).
  { intros. apply AxiomII in H2 as [H2[]].
    assert (x0 ∈ (A x)).
    { apply AxiomII; split; auto.
      apply Property_dom in H3. eauto. }
    intro. rewrite H5 in H4. elim (@ MKT16 x0); auto. }
  assert (∀ x, (A x) ⊂ n).
  { unfold Included; intros. apply AxiomII in H3 as [].
    apply Property_dom in H4. rewrite <-H1; auto. }
  assert (∀ x, x ∈ ran(f) -> ∃ a, FirstMember a E (A x)).
  { intros. assert (WellOrdered E n).
    { pose proof MKT138. apply AxiomII in H5 as [].
      apply (wosub ω). apply MKT107; auto. destruct H6.
      apply H7; auto. }
    assert (WellOrdered E (A x)) as []. { apply (wosub n); auto. }
    apply H7; [unfold Included|apply H2]; auto. }
  set (B := \{ λ u, ∃ x, [u,x] ∈ f /\ FirstMember u E (A x) \}).
  set (h := \{\ λ u v, u ∈ B /\ v = f[u] \}\).
  assert (Function1_1 h).
  { repeat split; unfold Relation; intros.
    - apply AxiomII in H5 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H5 as [_[]].
      apply AxiomII' in H6 as [_[]]. rewrite H7,H8; auto.
    - apply AxiomII in H5 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H5 as [_]. apply AxiomII' in H6 as [_].
      apply AxiomII' in H5 as [_[]]. apply AxiomII' in H6 as [_[]].
      apply AxiomII in H5 as [_[z1[H5[]]]].
      apply AxiomII in H6 as [_[z2[H6[]]]].
      pose proof H5; pose proof H6.
      apply Property_dom,Property_Value in H13;
      apply Property_dom,Property_Value in H14; auto.
      assert (z1 = f[y] /\ z2 = f[z]) as [].
      { destruct H0. split; [apply (H15 y)|apply (H15 z)]; auto. }
      assert (z1 = z2). { rewrite H15,H16,<-H7,<-H8; auto. }
      apply Property_dom in H5; apply Property_dom in H6.
      rewrite H1 in H5,H6. pose proof MKT138. apply AxiomII
      in H18 as [_[]]. apply H19 in H. apply H in H5; apply H in H6.
      assert (Ordinal y /\ Ordinal z) as [].
      { apply AxiomII in H5 as [_[]].
        apply AxiomII in H6 as [_[]]; auto. }
      apply (@ MKT110 y z) in H20 as [|[]]; auto; clear H21.
      rewrite <-H17 in H12. apply H12 in H9. elim H9.
      apply AxiomII'; split; auto. apply MKT49a; eauto.
      rewrite H17 in H10. apply H10 in H11. elim H11.
      apply AxiomII'; split; auto. apply MKT49a; eauto. }
  assert (B ⊂ dom(f)).
  { unfold Included; intros. apply AxiomII in H6 as [_[x[]]].
    apply Property_dom in H6; auto. }
  assert (dom(h) = B /\ ran(h) = ran(f)) as [].
  { split; apply AxiomI; split; intros.
    - apply AxiomII in H7 as [_[]]. apply AxiomII' in H7; tauto.
    - apply AxiomII; split; eauto. exists (f[z]).
      apply AxiomII'; split; auto. apply MKT49a; eauto.
      apply H6 in H7.
      apply Property_Value,Property_ran in H7; eauto.
    - apply AxiomII in H7 as [_[]]. apply AxiomII' in H7 as [H7[]].
      rewrite H9. apply H6 in H8.
      apply Property_Value,Property_ran in H8; auto.
    - apply AxiomII; split; eauto. pose proof H7.
      apply H4 in H7 as [a]. exists a.
      apply AxiomII'; repeat split. destruct H7.
      apply MKT49a; eauto. destruct H7. apply AxiomII; split; eauto.
      exists z. repeat split; auto. apply AxiomII in H7; tauto.
      destruct H7. apply AxiomII in H7 as [_]. pose proof H7.
      apply Property_dom,Property_Value in H10; auto.
      destruct H0. apply (H11 a); auto. }
  assert (B ≈ ran(f)). { exists h; auto. }
  apply (Inf_P4 _ B). apply (@ finsub dom(f)); auto.
  rewrite H1. unfold Finite. pose proof H. apply MKT164,MKT156
  in H10 as []. rewrite H11; auto. apply MKT146; auto.
Qed.

(* 考察*N中的非标准数, 所有非标准数大于一般自然数, 因而也可称为无穷大数
        F0 F1 F2 F3 F4 ··· t1 t2 t3 ··· (tn为 *N~N中的元素)   *)
Property N'_Infty : ∀ t u, t ∈ (N' ~ N'_N) -> u ∈ N'_N -> u < t.
Proof.
  destruct NPAUF. intros. pose proof H2. apply AxiomII in H3 as [_[n[]]].
  rewrite H4 in *. clear H2 H4. pose proof H3.
  apply (F_Const_Fa F0 ω) in H2; [ |destruct H]; auto.
  pose proof H3. apply Fn_in_N' in H3. assert (Ensemble n) by eauto.
  assert (ω <> 0) as HH.
  { intro. rewrite H6 in H4. elim (@ MKT16 n); auto. }
  apply (Const_is_Function ω) in H5 as [H5[]]; auto.
  assert (ran(Const n) ⊂ ω).
  { unfold Included; intros. rewrite H7 in H8.
    apply MKT41 in H8; eauto. rewrite H8; auto. }
  assert (∀ m, m ∈ ω -> (Const n)[m] = n).
  { intros. rewrite <-H6 in H9. apply Property_Value in H9; auto.
    apply AxiomII' in H9; tauto. }
  pose proof H1. apply MKT4' in H10 as [H10 _]. pose proof H10.
  apply AxiomII in H10 as [_[f[H10[H12[]]]]]. pose proof H1.
  apply MKT4' in H15 as [_]. apply AxiomII in H15 as [_].
  assert ((F n) ∈ N' /\ t ∈ N') as []; auto.
  apply (N'_Ord_Tri _ t) in H16 as [H16|[]]; auto;
  clear H17; rewrite <-H2,H14 in H16.
  - apply N'_Ord_Instantiate in H16; auto.
    set (A x := \{ λ w, x ∈ ω /\ f[w] = x \}).
    set (B := ∪(\{ λ w, ∃ u, u ∈ ω /\ u ∈ n /\ w = A u \})).
    assert (B = \{ λ w, f[w] ∈ ((Const n)[w]) \}).
    { apply AxiomI; split; intros.
      - apply AxiomII in H17 as [_[a[]]].
        apply AxiomII in H18 as [H18[x[H19[]]]].
        rewrite H21 in H17. apply AxiomII in H17 as [H17[]].
        apply AxiomII; split; auto. rewrite H9,H23; auto.
        apply NNPP; intro. rewrite <-H12 in H24.
        apply MKT69a in H24. rewrite <-H23,H24 in H20.
        elim MKT39; eauto.
      - apply AxiomII in H17 as [].
        assert (z ∈ ω).
        { apply NNPP; intro. rewrite <-H12 in H19.
          apply MKT69a in H19. rewrite H19 in H18.
          elim MKT39; eauto. }
        rewrite H9 in H18; auto. apply AxiomII; split; auto.
        assert (f[z] ∈ ω).
        { pose proof MKT138. apply AxiomII in H20 as [_[]].
          apply H21 in H4. apply H4; auto. }
        exists (A (f[z])). split. apply AxiomII; auto.
        assert (Ensemble (A f[z])).
        { apply (MKT33 ω). pose proof MKT138; eauto.
          unfold Included; intros. apply AxiomII in H21 as [_[]].
          apply NNPP; intro. rewrite <-H12 in H23.
          apply MKT69a in H23. rewrite <-H22,H23 in H18.
          elim MKT39; eauto. }
        apply AxiomII; split; eauto. }
    set (h := \{\ λ u v, u ∈ n /\ v = A u \}\).
    assert (Function h).
    { split; unfold Relation; intros.
      - apply AxiomII in H18 as [_[x[y[]]]]; eauto.
      - apply AxiomII' in H18 as [_[]].
        apply AxiomII' in H19 as [_[]]. rewrite H20,H21; auto. }
    assert (∀ x, Ensemble x -> Ensemble (A x)).
    { intros. apply (MKT33 ω). pose proof MKT138; eauto.
      unfold Included; intros. apply AxiomII in H20 as [_[]].
      apply NNPP; intro. rewrite <-H12 in H22. apply MKT69a in H22.
      rewrite <-H21,H22 in H19. elim MKT39; auto. }
    assert (dom(h) = n).
    { apply AxiomI; split; intros.
      - apply AxiomII in H20 as [_[]]. apply AxiomII' in H20; tauto.
      - apply AxiomII; split; eauto. exists (A z).
        apply AxiomII'; split; auto. apply MKT49a; eauto. }
    assert (ran(h) = \{ λ w, ∃ u, u ∈ ω /\ u ∈ n /\ w = A u \}).
    { apply AxiomI; split; intros.
      - apply AxiomII in H21 as [H21[]].
        apply AxiomII' in H22 as [_[]].
        apply AxiomII; split; auto. exists x.
        split; auto. pose proof MKT138.
        apply AxiomII in H24 as [_[]]. eapply H25; eauto.
      - apply AxiomII in H21 as [H21[x[H22[]]]].
        apply AxiomII; split; auto. exists x.
        apply AxiomII'; split; auto. apply MKT49a; eauto. }
    assert (Finite (\{ λ w, ∃ u, u ∈ ω /\ u ∈ n /\ w = A u \})).
    { rewrite <-H21. apply (N'_Infty_Lemma n h); auto. }
    apply (FT1_Corollary F0 ω) in H22 as [D[]]; [ |destruct H as [_[]];
    apply AxiomII in H as [[]]|unfold B in H17; rewrite H17]; auto.
    apply AxiomII in H22 as [H22[x[H24[]]]]. pose proof H24.
    apply (FT7 F0 f ω ω x) in H27; auto. rewrite H14,H27 in H15. elim H15.
    apply Fn_in_N'_N; auto. exists D. split; intros; auto. rewrite H26 in H28.
    apply AxiomII in H28; tauto.
  - rewrite H14,<-H16,H2 in H15. elim H15. apply Fn_in_N'_N; auto.
Qed.

















